import HadwigerLean.Woven.HubWoven

import Mathlib.Tactic

/-!
# Canonical matching of root, residual, and terminal arrivals

One root proxy is paired with each residual-model start. The two proxy
endpoints of each terminal pair are paired with each other.
-/

namespace HadwigerLean
namespace Woven

/-- Proxy role slots: one per root and two per terminal pair. -/
abbrev HubProxyRole (a j : ℕ) := Fin a ⊕ (Fin j × Fin 2)

/-- The explicit matching before enumerating the pair indices by `Fin`. -/
def proxyRoleMatching {a j : ℕ} {Z : Type*}
    (proxy : HubProxyRole a j ≃ Z) :
    ((Fin a ⊕ Fin j) × Fin 2) ≃ (Z ⊕ Fin a) where
  toFun
    | (Sum.inl i,b) => if b = 0 then Sum.inl (proxy (Sum.inl i)) else Sum.inr i
    | (Sum.inr k,b) => Sum.inl (proxy (Sum.inr (k,b)))
  invFun
    | Sum.inl z =>
        match proxy.symm z with
        | Sum.inl i => (Sum.inl i,0)
        | Sum.inr (k,b) => (Sum.inr k,b)
    | Sum.inr i => (Sum.inl i,1)
  left_inv := by
    intro x
    rcases x with ⟨i,b⟩
    cases i with
    | inl i =>
        fin_cases b <;> simp
    | inr k =>
        simp
  right_inv := by
    intro x
    cases x with
    | inl z =>
        cases h : proxy.symm z with
        | inl i =>
            have hz : proxy (Sum.inl i) = z := by
              simpa [h] using proxy.apply_symm_apply z
            simp [h, hz]
        | inr kb =>
            rcases kb with ⟨k,b⟩
            have hz : proxy (Sum.inr (k,b)) = z := by
              simpa [h] using proxy.apply_symm_apply z
            simp [h, hz]
    | inr i => simp

/-- Enumerate the `a+j` matching pairs by a single finite index. -/
def hubRoleMatching {a j : ℕ} {Z : Type*}
    (proxy : HubProxyRole a j ≃ Z) :
    (Fin (a + j) × Fin 2) ≃ (Z ⊕ Fin a) :=
  (Equiv.prodCongr finSumFinEquiv.symm (Equiv.refl (Fin 2))).trans
    (proxyRoleMatching proxy)

/-- Root pairs occupy the first block of matched hub routes. -/
def hubRootSlot (a j : ℕ) : Fin a ↪ Fin (a + j) :=
  Fin.castAddEmb j

/-- Terminal pairs occupy the second block of matched hub routes. -/
def hubTerminalSlot (a j : ℕ) : Fin j ↪ Fin (a + j) :=
  Fin.natAddEmb a

theorem hubRootSlot_ne_hubTerminalSlot (a j : ℕ)
    (i : Fin a) (k : Fin j) :
    hubRootSlot a j i ≠ hubTerminalSlot a j k := by
  intro h
  have heq := congrArg (finSumFinEquiv.symm : Fin (a+j) → Fin a ⊕ Fin j) h
  simpa [hubRootSlot, hubTerminalSlot] using heq

@[simp] theorem hubRoleMatching_root_proxy {a j : ℕ} {Z : Type*}
    (proxy : HubProxyRole a j ≃ Z) (i : Fin a) :
    hubRoleMatching proxy (hubRootSlot a j i,0) =
      Sum.inl (proxy (Sum.inl i)) := by
  simp [hubRoleMatching, proxyRoleMatching, hubRootSlot]

@[simp] theorem hubRoleMatching_root_residual {a j : ℕ} {Z : Type*}
    (proxy : HubProxyRole a j ≃ Z) (i : Fin a) :
    hubRoleMatching proxy (hubRootSlot a j i,1) = Sum.inr i := by
  simp [hubRoleMatching, proxyRoleMatching, hubRootSlot]

@[simp] theorem hubRoleMatching_terminal {a j : ℕ} {Z : Type*}
    (proxy : HubProxyRole a j ≃ Z) (k : Fin j) (b : Fin 2) :
    hubRoleMatching proxy (hubTerminalSlot a j k,b) =
      Sum.inl (proxy (Sum.inr (k,b))) := by
  simp [hubRoleMatching, proxyRoleMatching, hubTerminalSlot]


/-- The first arrival of every matched pair is a proxy. -/
theorem hubRoleMatching_first_proxy {a j : ℕ} {Z : Type*}
    (proxy : HubProxyRole a j ≃ Z) (k : Fin (a + j)) :
    ∃ z : Z, hubRoleMatching proxy (k,0) = Sum.inl z := by
  obtain ⟨s,rfl⟩ :=
    (finSumFinEquiv : Fin a ⊕ Fin j ≃ Fin (a+j)).surjective k
  cases s with
  | inl i =>
      exact ⟨proxy (Sum.inl i), by
        simpa [hubRootSlot] using hubRoleMatching_root_proxy proxy i⟩
  | inr t =>
      exact ⟨proxy (Sum.inr (t,0)), by
        simpa [hubTerminalSlot] using hubRoleMatching_terminal proxy t 0⟩
end Woven
end HadwigerLean
