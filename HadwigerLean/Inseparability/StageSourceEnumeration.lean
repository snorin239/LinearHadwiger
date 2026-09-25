import HadwigerLean.Inseparability.StageMixedReindex
import Mathlib.Tactic

/-!
# The reserved old and child sources

Before constructing the first double fan, the previous tangencies and
the two roots in each child branch are enumerated in the first `3px`
path slots. This equivalence fixes the order required by the raw model.
-/

namespace HadwigerLean.Inseparability

abbrev CISourceRole (p x : ℕ) :=
  (Fin p × Fin x) ⊕ (Fin p × (Fin 2 × Fin x))

def ciSourceRoleEquiv (p x : ℕ) :
    Fin (3 * p * x) ≃ CISourceRole p x :=
  (finCongr (by ring : 3 * p * x = p * x + p * (2 * x))).trans
    ((finSumFinEquiv.symm).trans
      (Equiv.sumCongr finProdFinEquiv.symm
        (finProdFinEquiv.symm.trans
          (Equiv.prodCongr (Equiv.refl (Fin p))
            finProdFinEquiv.symm))))

theorem ciSourceRoleEquiv_old (p x : ℕ)
    (i : Fin p) (r : Fin x) :
    ciSourceRoleEquiv p x
      (ciSourceBlock p x ⟨i.val, by omega⟩ r) =
        Sum.inl (i,r) := by
  have hleft :
      (finCongr (by ring : 3 * p * x = p * x + p * (2 * x)))
        (ciSourceBlock p x ⟨i.val, by omega⟩ r) =
      Fin.castAdd (p * (2 * x)) (finProdFinEquiv (i,r)) := by
    apply Fin.ext
    simp [ciSourceBlock, finProdFinEquiv, Nat.mul_comm]
    omega
  simp only [ciSourceRoleEquiv, Equiv.trans_apply, hleft,
    finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply]
  simp

theorem ciSourceRoleEquiv_child (p x : ℕ)
    (i : Fin p) (d : Fin 2) (r : Fin x) :
    ciSourceRoleEquiv p x
      (ciSourceBlock p x
        ⟨p + 2 * i.val + d.val, by omega⟩ r) =
        Sum.inr (i,(d,r)) := by
  have hright :
      (finCongr (by ring : 3 * p * x = p * x + p * (2 * x)))
        (ciSourceBlock p x
          ⟨p + 2 * i.val + d.val, by omega⟩ r) =
      Fin.natAdd (p * x)
        (finProdFinEquiv (i, finProdFinEquiv (d,r))) := by
    apply Fin.ext
    simp [ciSourceBlock, finProdFinEquiv]
    ring
  simp only [ciSourceRoleEquiv, Equiv.trans_apply, hright,
    finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply]
  simp

def ciSourceValue {V : Type*} (p x : ℕ)
    (oldRoot : Fin p × Fin x → V)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (k : Fin (3 * p * x)) : V :=
  match ciSourceRoleEquiv p x k with
  | .inl z => oldRoot z
  | .inr (i,d) => childRoot i d

theorem ciSourceValue_old {V : Type*} (p x : ℕ)
    (oldRoot : Fin p × Fin x → V)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (i : Fin p) (r : Fin x) :
    ciSourceValue p x oldRoot childRoot
      (ciSourceBlock p x ⟨i.val, by omega⟩ r) =
        oldRoot (i,r) := by
  simp [ciSourceValue, ciSourceRoleEquiv_old]

theorem ciSourceValue_child {V : Type*} (p x : ℕ)
    (oldRoot : Fin p × Fin x → V)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (i : Fin p) (d : Fin 2) (r : Fin x) :
    ciSourceValue p x oldRoot childRoot
      (ciSourceBlock p x
        ⟨p + 2 * i.val + d.val, by omega⟩ r) =
        childRoot i (d,r) := by
  simp [ciSourceValue, ciSourceRoleEquiv_child]

theorem ciSourceValue_injective {V : Type*} (p x : ℕ)
    (oldRoot : Fin p × Fin x → V)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (hOld : Function.Injective oldRoot)
    (hChild : Function.Injective
      (fun q : Fin p × (Fin 2 × Fin x) => childRoot q.1 q.2))
    (hCross : ∀ (z : Fin p × Fin x) (q : Fin p × (Fin 2 × Fin x)), oldRoot z ≠ childRoot q.1 q.2) :
    Function.Injective (ciSourceValue p x oldRoot childRoot) := by
  intro k l hkl
  apply (ciSourceRoleEquiv p x).injective
  cases hk : ciSourceRoleEquiv p x k with
  | inl z =>
      cases hl : ciSourceRoleEquiv p x l with
      | inl w =>
          have h : oldRoot z = oldRoot w := by
            simpa [ciSourceValue, hk, hl] using hkl
          exact congrArg Sum.inl (hOld h)
      | inr q =>
          have h : oldRoot z = childRoot q.1 q.2 := by
            simpa [ciSourceValue, hk, hl] using hkl
          exact False.elim ((hCross z q) h)
  | inr q =>
      cases hl : ciSourceRoleEquiv p x l with
      | inl z =>
          have h : childRoot q.1 q.2 = oldRoot z := by
            simpa [ciSourceValue, hk, hl] using hkl
          exact False.elim ((hCross z q) h.symm)
      | inr w =>
          have h : childRoot q.1 q.2 = childRoot w.1 w.2 := by
            simpa [ciSourceValue, hk, hl] using hkl
          exact congrArg Sum.inr (hChild h)

/-- The exact source set, with its canonical order. -/
noncomputable def ciSourceEquiv {V : Type*} [Fintype V] [DecidableEq V]
    (p x : ℕ)
    (oldRoot : Fin p × Fin x → V)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (hOld : Function.Injective oldRoot)
    (hChild : Function.Injective
      (fun q : Fin p × (Fin 2 × Fin x) => childRoot q.1 q.2))
    (hCross : ∀ (z : Fin p × Fin x) (q : Fin p × (Fin 2 × Fin x)), oldRoot z ≠ childRoot q.1 q.2) :
    Fin (3 * p * x) ≃
      (Finset.univ.image (ciSourceValue p x oldRoot childRoot) : Finset V) := by
  classical
  let f : Fin (3 * p * x) →
      (Finset.univ.image (ciSourceValue p x oldRoot childRoot) : Finset V) :=
    fun k => ⟨ciSourceValue p x oldRoot childRoot k,
      Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro k l h
    exact ciSourceValue_injective p x oldRoot childRoot
      hOld hChild hCross (congrArg Subtype.val h)
  · rintro ⟨v,hv⟩
    obtain ⟨k,-,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨k,rfl⟩

@[simp] theorem ciSourceEquiv_apply {V : Type*}
    [Fintype V] [DecidableEq V] (p x : ℕ)
    (oldRoot : Fin p × Fin x → V)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (hOld : Function.Injective oldRoot)
    (hChild : Function.Injective
      (fun q : Fin p × (Fin 2 × Fin x) => childRoot q.1 q.2))
    (hCross : ∀ (z : Fin p × Fin x) (q : Fin p × (Fin 2 × Fin x)), oldRoot z ≠ childRoot q.1 q.2)
    (k : Fin (3 * p * x)) :
    ((ciSourceEquiv p x oldRoot childRoot hOld hChild hCross k) : V) =
      ciSourceValue p x oldRoot childRoot k := by
  rfl

theorem ciSourceFinset_card {V : Type*}
    [Fintype V] [DecidableEq V] (p x : ℕ)
    (oldRoot : Fin p × Fin x → V)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (hOld : Function.Injective oldRoot)
    (hChild : Function.Injective
      (fun q : Fin p × (Fin 2 × Fin x) => childRoot q.1 q.2))
    (hCross : ∀ (z : Fin p × Fin x) (q : Fin p × (Fin 2 × Fin x)), oldRoot z ≠ childRoot q.1 q.2) :
    (Finset.univ.image (ciSourceValue p x oldRoot childRoot)).card =
      3 * p * x := by
  have h := Fintype.card_congr
    (ciSourceEquiv p x oldRoot childRoot hOld hChild hCross)
  simpa only [Fintype.card_coe, Fintype.card_fin] using h.symm

end HadwigerLean.Inseparability


