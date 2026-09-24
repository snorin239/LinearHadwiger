import HadwigerLean.ReedSeymour.Partial

/-!
# Relabeling finite egg decompositions

The local quotient updates use naturally occurring finite index types.
This module converts them to `Fin n` for the global maximality argument.
-/

namespace HadwigerLean

variable {V I J : Type*} [Fintype V] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] {G : SimpleGraph V}

omit [DecidableEq I] [DecidableEq J] in
/-- The partial egg invariant is preserved by a bijection of block labels. -/
theorem ConnectedPartition.isPartialEggDecomposition_relabel
    (P : ConnectedPartition G I) (e : J ≃ I) (w : V → ℝ)
    (hP : IsPartialEggDecomposition P w) :
    IsPartialEggDecomposition (P.relabel e) w := by
  classical
  let iso := P.touchingQuotientIso e
  constructor
  · exact hP.1.of_iso iso.symm
  · intro j
    rcases hP.2 (e j) with hEgg | ⟨hsim, hneighbors⟩
    · exact Or.inl hEgg
    · right
      constructor
      · intro x y _ _ hjx hjy hxy
        have hOldX : P.touchingQuotient.Adj (e j) (e x) :=
          iso.map_rel_iff.mpr hjx
        have hOldY : P.touchingQuotient.Adj (e j) (e y) :=
          iso.map_rel_iff.mpr hjy
        have hOldXY : P.touchingQuotient.Adj (e x) (e y) :=
          hsim (Finset.mem_univ _) (Finset.mem_univ _)
            hOldX hOldY (fun he => hxy (e.injective he))
        exact iso.map_rel_iff.mp hOldXY
      · intro k hjk
        exact hneighbors (e k) (iso.map_rel_iff.mpr hjk)

omit [DecidableEq I] in
/-- Reindex a finite partial egg decomposition by `Fin n`, retaining its
egg support exactly. -/
theorem ConnectedPartition.exists_fin_relabel
    (P : ConnectedPartition G I) (w : V → ℝ)
    (hP : IsPartialEggDecomposition P w) :
    ∃ n : ℕ, ∃ Q : ConnectedPartition G (Fin n),
      IsPartialEggDecomposition Q w ∧
        eggSupport Q w = eggSupport P w := by
  classical
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let Q := P.relabel e
  exact ⟨Fintype.card I, Q,
    P.isPartialEggDecomposition_relabel e w hP,
    P.eggSupport_relabel e w⟩

end HadwigerLean
