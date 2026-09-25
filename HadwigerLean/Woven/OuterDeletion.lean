import HadwigerLean.Woven.NormalizedConstruction
import HadwigerLean.Woven.DoubleFanCost
import HadwigerLean.Graph.ChromaticSlice
import Mathlib.Tactic

/-!
# Chromatic losses from role and proxy deletion
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Deleting a finite vertex set costs at most one color per deleted vertex. -/
theorem chromatic_le_card_add_complement
    (G : SimpleGraph V) (S : Finset V) :
    chromatic G ≤ S.card +
      chromatic (G.induce (S : Set V)ᶜ) := by
  classical
  have h := chromatic_induce_le_add_remainder G Set.univ (S : Set V)
  have hS : chromatic (G.induce (S : Set V)) ≤ S.card := by
    simpa using chromatic_le_card (G.induce (S : Set V))
  have huniv : chromatic (G.induce Set.univ) = chromatic G := by
    have hu : ((Finset.univ : Finset V) : Set V) = Set.univ := by
      ext x
      simp
    rw [← hu]
    exact chromatic_induce_univ_finset G
  have hdiff : Set.univ \ (S : Set V) = (S : Set V)ᶜ := by
    ext x
    simp
  rw [huniv, hdiff] at h
  omega

/-- Exactly a+2j original role occurrences are budgeted, so at most 7a
colors are lost when j ≤ 3a and occupied original vertices are removed. -/
theorem chromatic_le_normalized_add_seven
    (G : SimpleGraph V)
    {a j : ℕ} (root : Fin a → V)
    (P : IndexedPairs (Fin j) V)
    (hj : j ≤ 3 * a) :
    chromatic G ≤ 7 * a +
      chromatic (G.induce (normalizedSet root P)) := by
  have h := chromatic_le_card_add_complement G
    (occupiedRoles root P)
  have hcard := occupiedRoles_card_le root P
  change chromatic G ≤
    (occupiedRoles root P).card +
      chromatic (G.induce (normalizedSet root P)) at h
  omega

end Woven
end HadwigerLean
