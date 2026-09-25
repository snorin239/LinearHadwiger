import HadwigerLean.Woven.NormalizedConstruction
import HadwigerLean.Woven.MixedFanWoven
import Mathlib.Tactic

/-!
# Reindex normalized proxy roles for the hub construction
-/

namespace HadwigerLean
namespace Woven

/-- The hub's product-indexed terminal roles agree with the original
sum-indexed terminal roles. -/
def hubToDistinctRole (a j : ℕ) :
    HubProxyRole a j ≃ DistinctRoleIndex a j where
  toFun
    | .inl i => .inl i
    | .inr (k,b) => .inr (if b = 0 then .inl k else .inr k)
  invFun
    | .inl i => .inl i
    | .inr (.inl k) => .inr (k,0)
    | .inr (.inr k) => .inr (k,1)
  left_inv := by
    intro x
    rcases x with i | ⟨k,b⟩
    · rfl
    · fin_cases b <;> rfl
  right_inv := by
    intro x
    rcases x with i | (k | k) <;> rfl

/-- Interpret a normalized role enumeration in the hub's indexing. -/
noncomputable def hubRoleFin {W : Type*} {a j : ℕ}
    (role : Fin (a + 2 * j) → W) :
    HubProxyRole a j → W :=
  role ∘ (distinctRoleEquiv a j) ∘ (hubToDistinctRole a j)

theorem hubRoleFin_injective
    {W : Type*} {a j : ℕ}
    (role : Fin (a + 2 * j) → W)
    (hrole : Function.Injective role) :
    Function.Injective (hubRoleFin role) :=
  hrole.comp ((distinctRoleEquiv a j).injective.comp
    (hubToDistinctRole a j).injective)

/-- Package the normalized proxy injection as the hub's canonical
equivalence onto its image. -/
noncomputable def hubProxyEquiv
    {W : Type*} [Fintype W] [DecidableEq W] {a j : ℕ}
    (role : Fin (a + 2 * j) → W)
    (hrole : Function.Injective role) :
    HubProxyRole a j ≃ (Finset.univ.image (hubRoleFin role) : Finset W) := by
  classical
  let f : HubProxyRole a j →
      (Finset.univ.image (hubRoleFin role) : Finset W) :=
    fun q => ⟨hubRoleFin role q,
      Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro q r h
    exact hubRoleFin_injective role hrole (congrArg Subtype.val h)
  · rintro ⟨w,hw⟩
    obtain ⟨q,-,rfl⟩ := Finset.mem_image.mp hw
    exact ⟨q,rfl⟩

@[simp] theorem hubProxyEquiv_apply
    {W : Type*} [Fintype W] [DecidableEq W] {a j : ℕ}
    (role : Fin (a + 2 * j) → W)
    (hrole : Function.Injective role)
    (q : HubProxyRole a j) :
    ((hubProxyEquiv role hrole q :
      (Finset.univ.image (hubRoleFin role) : Finset W)) : W) =
      hubRoleFin role q := by
  rfl


/-- Hub proxy roots agree with the canonical normalized role roots. -/
theorem hubProxyRoots_eq_selectedRoots
    {W : Type*} [Fintype W] [DecidableEq W] {a j : ℕ}
    (role : Fin (a + 2 * j) → W)
    (hrole : Function.Injective role) :
    hubProxyRoots (hubProxyEquiv role hrole) =
      selectedRoots (distinctRoleEquiv a j).toEmbedding role := by
  funext i
  change ((hubProxyEquiv role hrole (Sum.inl i)) : W) =
    role ((distinctRoleEquiv a j) (Sum.inl i))
  rw [hubProxyEquiv_apply]
  rfl

/-- Hub proxy terminal pairs agree with the canonical normalized pairs. -/
theorem hubProxyPairs_eq_selectedPairs
    {W : Type*} [Fintype W] [DecidableEq W] {a j : ℕ}
    (role : Fin (a + 2 * j) → W)
    (hrole : Function.Injective role) :
    hubProxyPairs (hubProxyEquiv role hrole) =
      selectedPairs (distinctRoleEquiv a j).toEmbedding role := by
  have hs : (hubProxyPairs (hubProxyEquiv role hrole)).start =
      (selectedPairs (distinctRoleEquiv a j).toEmbedding role).start := by
    funext k
    change ((hubProxyEquiv role hrole (Sum.inr (k,0))) : W) =
      role ((distinctRoleEquiv a j) (Sum.inr (Sum.inl k)))
    rw [hubProxyEquiv_apply]
    rfl
  have ht : (hubProxyPairs (hubProxyEquiv role hrole)).finish =
      (selectedPairs (distinctRoleEquiv a j).toEmbedding role).finish := by
    funext k
    change ((hubProxyEquiv role hrole (Sum.inr (k,1))) : W) =
      role ((distinctRoleEquiv a j) (Sum.inr (Sum.inr k)))
    rw [hubProxyEquiv_apply]
    rfl
  cases e₁ : hubProxyPairs (hubProxyEquiv role hrole) with
  | mk s t =>
    cases e₂ : selectedPairs (distinctRoleEquiv a j).toEmbedding role with
    | mk s' t' =>
      have hs' : s = s' := by simpa [e₁, e₂] using hs
      have ht' : t = t' := by simpa [e₁, e₂] using ht
      cases hs'
      cases ht'
      rfl


/-- A proxy woven solution in the normalized graph lifts back to the
arbitrary original roots and terminal pairs. -/
theorem exists_original_solution_of_normalized_hub_proxy
    {V : Type*} [Fintype V] [DecidableEq V]
    {a j : ℕ}
    (G : SimpleGraph V)
    (root : Fin a → V) (P : IndexedPairs (Fin j) V)
    [Fintype (normalizedSet root P)]
    (hroot : Function.Injective root)
    (hP : P.DisjointTerminals)
    (role : Fin (a + 2 * j) → normalizedSet root P)
    (hrole : Function.Injective role)
    (hadj : ∀ i, G.Adj (originalRoleFin root P i) (role i).1)
    (T : WovenSolution (G.induce (normalizedSet root P))
      (hubProxyRoots (hubProxyEquiv role hrole))
      (hubProxyPairs (hubProxyEquiv role hrole))) :
    Nonempty (WovenSolution G root P) := by
  classical
  let f : DistinctRoleIndex a j ↪ Fin (a + 2 * j) :=
    (distinctRoleEquiv a j).toEmbedding
  have hrEq := hubProxyRoots_eq_selectedRoots role hrole
  have hpEq := hubProxyPairs_eq_selectedPairs role hrole
  rw [hrEq, hpEq] at T
  have hroles : Disjoint (Set.range (selectedRoots f role))
      (selectedPairs f role).allTerminals :=
    selectedRoles_disjoint f role hrole
  have hrootEdge : ∀ i, G.Adj (root i) (selectedRoots f role i).1 := by
    intro i
    simpa [f, originalRoleFin, originalRole, selectedRoots] using
      hadj (f (Sum.inl i))
  have hstartEdge : ∀ i, G.Adj (P.start i)
      ((selectedPairs f role).start i).1 := by
    intro i
    simpa [f, originalRoleFin, originalRole, selectedPairs] using
      hadj (f (Sum.inr (Sum.inl i)))
  have hfinishEdge : ∀ i, G.Adj
      ((selectedPairs f role).finish i).1 (P.finish i) := by
    intro i
    simpa [f, originalRoleFin, originalRole, selectedPairs] using
      (hadj (f (Sum.inr (Sum.inr i)))).symm
  exact ⟨T.extendFromInduced hroles hroot
    (root_not_normalized root P) hP
    (terminals_not_normalized root P)
    hrootEdge hstartEdge hfinishEdge⟩

end Woven
end HadwigerLean