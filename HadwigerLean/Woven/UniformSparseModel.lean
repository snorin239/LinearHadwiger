import HadwigerLean.Woven.NormalizedConstruction
import HadwigerLean.Graph.RootedDensity.CliqueMatchingRoles

/-! Lifting a sparse clique-plus-matching proxy minor to a woven solution. -/

namespace HadwigerLean.Woven

open HadwigerLean.RootedDensity

variable {V : Type*} [Fintype V] [DecidableEq V] {a j : ℕ}


private theorem indexedPairs_ext
    {ι X : Type*} (P Q : IndexedPairs ι X)
    (hs : P.start = Q.start) (ht : P.finish = Q.finish) : P = Q := by
  cases P with
  | mk s t =>
    cases Q with
    | mk s' t' =>
      cases hs
      cases ht
      rfl
/-- Translate a canonical target label to its normalized proxy vertex. -/
noncomputable def cliqueMatchingProxyRole
    (root : Fin a → V) (P : IndexedPairs (Fin j) V)
    (proxy : Fin (a + 2 * j) → normalizedSet root P) :
    CliqueMatchingLabels a j → normalizedSet root P :=
  fun w => proxy ((distinctRoleEquiv a j)
    ((cliqueMatchingRoleEquiv a j).symm w))

@[simp] theorem cliqueMatchingProxyRole_apply_role
    (root : Fin a → V) (P : IndexedPairs (Fin j) V)
    (proxy : Fin (a + 2 * j) → normalizedSet root P)
    (r : DistinctRoleIndex a j) :
    cliqueMatchingProxyRole root P proxy (cliqueMatchingRoleLabel a j r) =
      proxy ((distinctRoleEquiv a j) r) := by
  simp [cliqueMatchingProxyRole, cliqueMatchingRoleEquiv]

/-- An arbitrary rooted model of `K_a + j K₂` at the selected normalized
proxies reconstructs the full woven solution for the original roles. -/
theorem exists_solution_of_normalized_sparse_minor
    (G : SimpleGraph V)
    (root : Fin a → V) (P : IndexedPairs (Fin j) V)
    (hroot : Function.Injective root)
    (hP : P.DisjointTerminals)
    (proxy : Fin (a + 2 * j) → normalizedSet root P)
    (hinj : Function.Injective proxy)
    (hadj : ∀ i, G.Adj (originalRoleFin root P i) (proxy i).1)
    (hminor : Nonempty (RootedMinorModel (cliqueMatchingGraph a j)
      (G.induce (normalizedSet root P))
      (cliqueMatchingProxyRole root P proxy))) :
    Nonempty (WovenSolution G root P) := by
  obtain ⟨M⟩ := hminor
  obtain ⟨T⟩ := wovenSolution_of_cliqueMatching_model M
  let f : DistinctRoleIndex a j ↪ Fin (a + 2 * j) :=
    (distinctRoleEquiv a j).toEmbedding
  have hrootEq : sparseSelectedRoots (cliqueMatchingRoleLabel a j)
      (cliqueMatchingProxyRole root P proxy) = selectedRoots f proxy := by
    funext i
    simp [sparseSelectedRoots, selectedRoots, f]
  have hpairEq : sparseSelectedPairs (cliqueMatchingRoleLabel a j)
      (cliqueMatchingProxyRole root P proxy) = selectedPairs f proxy := by
    apply indexedPairs_ext
    · funext i
      simpa [sparseSelectedPairs, selectedPairs, f] using
        cliqueMatchingProxyRole_apply_role root P proxy (Sum.inr (Sum.inl i))
    · funext i
      simpa [sparseSelectedPairs, selectedPairs, f] using
        cliqueMatchingProxyRole_apply_role root P proxy (Sum.inr (Sum.inr i))
  have T' : WovenSolution (G.induce (normalizedSet root P))
      (selectedRoots f proxy) (selectedPairs f proxy) := by
    rw [← hrootEq, ← hpairEq]
    exact T
  have hdis := selectedRoles_disjoint f proxy hinj
  exact ⟨T'.extendFromInduced hdis hroot
    (root_not_normalized root P) hP (terminals_not_normalized root P)
    (by intro i
        simpa [f, originalRoleFin, originalRole, selectedRoots] using
          hadj (f (Sum.inl i)))
    (by intro i
        simpa [f, originalRoleFin, originalRole, selectedPairs] using
          hadj (f (Sum.inr (Sum.inl i))))
    (by intro i
        simpa [f, originalRoleFin, originalRole, selectedPairs] using
          (hadj (f (Sum.inr (Sum.inr i)))).symm)⟩

end HadwigerLean.Woven



