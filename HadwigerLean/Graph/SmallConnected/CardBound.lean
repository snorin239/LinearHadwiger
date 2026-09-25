import HadwigerLean.Graph.SmallConnected.LocalCore
import Mathlib.Tactic

/-!
# Order bound for the contracted neighborhood
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The neighborhood after contracting H has at most the sum of the
degrees of vertices in H. -/
theorem localR_card_le_degree_sum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H X : Finset V) :
    (localR G H X).card ≤ ∑ v ∈ H, G.degree v := by
  calc
    (localR G H X).card ≤ (contractedNeighborFinset G H).card :=
      Finset.card_le_card Finset.sdiff_subset
    _ ≤ ∑ v ∈ H, G.degree v :=
      contractedNeighborFinset_card_le_sum_degrees G H

/-- The low-degree condition on the trimmed residual set controls
its contracted neighborhood. -/
theorem localR_card_le_degree_cap
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H X S : Finset V) (d : ℕ) (L : ℝ)
    (hHS : H ⊆ S)
    (hdeg : ∀ v ∈ S, (G.degree v : ℝ) ≤ 20 * (d : ℝ) * L) :
    ((localR G H X).card : ℝ) ≤
      20 * (d : ℝ) * L * (H.card : ℝ) := by
  have hcard := localR_card_le_degree_sum G H X
  have hcardR : ((localR G H X).card : ℝ) ≤
      ∑ v ∈ H, (G.degree v : ℝ) := by exact_mod_cast hcard
  have hsum : (∑ v ∈ H, (G.degree v : ℝ)) ≤
      ∑ v ∈ H, 20 * (d : ℝ) * L := by
    apply Finset.sum_le_sum
    intro v hv
    exact hdeg v (hHS hv)
  calc
    ((localR G H X).card : ℝ) ≤ ∑ v ∈ H, (G.degree v : ℝ) := hcardR
    _ ≤ ∑ v ∈ H, 20 * (d : ℝ) * L := hsum
    _ = 20 * (d : ℝ) * L * (H.card : ℝ) := by
      simp [mul_comm, mul_left_comm, mul_assoc]

end HadwigerLean