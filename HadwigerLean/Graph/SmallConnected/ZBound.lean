import HadwigerLean.Graph.DensityBasic
import Mathlib.Tactic

/-!
# Counting high-degree quotient vertices
-/

namespace HadwigerLean

universe u

/-- The degree-sum estimate used for `Z` in Equation (8.5), with `N`
allowed to be the order of the graph before contraction. -/
theorem high_degree_card_bound
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z : Finset V) (d N : ℕ) (L : ℝ)
    (hd : 0 < d) (hL : 0 ≤ L)
    (hedges : edgeCount G ≤ d * N)
    (hdegree : ∀ v ∈ Z, 20 * (d : ℝ) * L ≤ (G.degree v : ℝ)) :
    10 * L * (Z.card : ℝ) ≤ (N : ℝ) := by
  classical
  have hsumZ : 20 * (d : ℝ) * L * (Z.card : ℝ) ≤
      ∑ v ∈ Z, (G.degree v : ℝ) := by
    calc
      20 * (d : ℝ) * L * (Z.card : ℝ) =
          ∑ v ∈ Z, 20 * (d : ℝ) * L := by
            simp [mul_assoc, mul_comm, mul_left_comm]
      _ ≤ ∑ v ∈ Z, (G.degree v : ℝ) := by
        apply Finset.sum_le_sum
        intro v hv
        exact hdegree v hv
  have hsumall : (∑ v ∈ Z, (G.degree v : ℝ)) ≤
      ∑ v : V, (G.degree v : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Z)
    intros
    positivity
  have hhand : (∑ v : V, (G.degree v : ℝ)) =
      2 * (edgeCount G : ℝ) := by
    exact_mod_cast sum_degree_eq_two_edgeCount G
  have hedgeR : (edgeCount G : ℝ) ≤ (d : ℝ) * (N : ℝ) := by
    exact_mod_cast hedges
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  nlinarith [mul_nonneg hdR.le hL]

end HadwigerLean
