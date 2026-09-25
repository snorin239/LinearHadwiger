import HadwigerLean.Inseparability.RegionExtraction
import HadwigerLean.Inseparability.CoreColor
import Mathlib.Tactic

/-!
# Extract a chromatic connected region after an internal deletion

This is the H₁-to-H₃ chromatic ledger in the sequential induction. The
deleted set may be the union of all small connected pieces and a chordless
double fan.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_connected_region_after_deleting
    (G : SimpleGraph V) (R D : Finset V)
    (k oldLoss cost newLoss : ℕ)
    (hk : 0 < k)
    (hreserve : chromatic G ≤
      chromatic (G.induce (R : Set V)) + oldLoss)
    (hcost : chromatic (G.induce (D : Set V)) ≤ cost)
    (hχ : oldLoss + cost + 7 * k ≤ chromatic G)
    (hbudget : oldLoss + cost + 6 * k ≤ newLoss) :
    ∃ H : Finset V,
      H ⊆ R \ D ∧
      VertexConnected (G.induce (H : Set V)) k ∧
      chromatic G ≤ chromatic (G.induce (H : Set V)) + newLoss := by
  classical
  have hsplit := Woven.chromatic_induce_le_add_remainder G
    (R : Set V) (D : Set V)
  have hdiff : (R : Set V) \ (D : Set V) =
      ((R \ D : Finset V) : Set V) := by
    ext v
    simp
  rw [hdiff] at hsplit
  have hχres : 7 * k ≤ chromatic (G.induce ((R \ D : Finset V) : Set V)) := by
    omega
  obtain ⟨H,hHR,hHconn,hHχ⟩ :=
    Woven.exists_chromatic_connected_inside G (R \ D) k hk hχres
  refine ⟨H,hHR,hHconn,?_⟩
  omega

/-- A two-part deleted set pays the sum of its separate chromatic costs. -/
theorem exists_connected_region_after_deleting_two
    (G : SimpleGraph V) (R D₁ D₂ : Finset V)
    (k oldLoss cost₁ cost₂ newLoss : ℕ)
    (hk : 0 < k)
    (hreserve : chromatic G ≤
      chromatic (G.induce (R : Set V)) + oldLoss)
    (hcost₁ : chromatic (G.induce (D₁ : Set V)) ≤ cost₁)
    (hcost₂ : chromatic (G.induce (D₂ : Set V)) ≤ cost₂)
    (hχ : oldLoss + cost₁ + cost₂ + 7 * k ≤ chromatic G)
    (hbudget : oldLoss + cost₁ + cost₂ + 6 * k ≤ newLoss) :
    ∃ H : Finset V,
      H ⊆ R \ (D₁ ∪ D₂) ∧
      VertexConnected (G.induce (H : Set V)) k ∧
      chromatic G ≤ chromatic (G.induce (H : Set V)) + newLoss := by
  have hcost : chromatic (G.induce ((D₁ ∪ D₂ : Finset V) : Set V)) ≤
      cost₁ + cost₂ := by
    have h := chromatic_induce_union_le_add G D₁ D₂
    omega
  exact exists_connected_region_after_deleting G R (D₁ ∪ D₂)
    k oldLoss (cost₁ + cost₂) newLoss hk hreserve hcost
    (by omega) (by omega)

end Inseparability
end HadwigerLean
