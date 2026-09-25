import HadwigerLean.Woven.UniformSparse
import HadwigerLean.Graph.RootedDensity.CliqueMatchingNumerics
import Mathlib.Tactic

/-! The explicit million-fold connectivity budget for uniform wovenness. -/

namespace HadwigerLean.Woven

open HadwigerLean.RootedDensity

universe u

/-- Once Appendix F supplies rooted density for every clique-plus-matching
target, its numerical constants give the exact uniform connectivity
coefficient `10^6` used in the proof document. -/
theorem woven_of_sharp_rooted_cliqueMatching
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (a b K : ℕ) (ha : 2 ≤ a)
    (hconn : VertexConnected G K)
    (hK : 1000000 * cliqueMatchingScale a b ≤ (K : ℝ))
    (hRD : ∀ j ≤ b, RootedDensityConclusion.{u,0}
      (cliqueMatchingGraph a j)
      (12 * cliqueMatchingThreshold a j +
        5000 * (Fintype.card (CliqueMatchingLabels a j) : ℝ))) :
    Woven G a b := by
  let R := a + 2 * b
  let M := cliqueMatchingScale a b
  have hM : 0 ≤ M := by
    dsimp [M, cliqueMatchingScale]
    exact le_max_of_le_right (Nat.cast_nonneg _)
  have hR : (R : ℝ) ≤ 4 * M := by
    dsimp [R, M]
    simpa [cliqueMatchingLabels_card] using
      cliqueMatching_order_le_four_scale a b ha
  have hRleK : R ≤ K := by
    have hRleKR : (R : ℝ) ≤ K := by nlinarith
    exact_mod_cast hRleKR
  let q := K - R
  have hqadd : q + R = K := Nat.sub_add_cancel hRleK
  have hqR : (q : ℝ) + R = K := by exact_mod_cast hqadd
  have hsmall (j : ℕ) (hj : j ≤ b) : a + 2 * j ≤ R := by
    dsimp [R]
    omega
  have hscalej (j : ℕ) (hj : j ≤ b) :
      cliqueMatchingScale a j ≤ M := by
    dsimp [M, cliqueMatchingScale]
    apply max_le
    · exact le_max_left _ _
    · exact (show (j : ℝ) ≤ b by exact_mod_cast hj).trans (le_max_right _ _)
  have hproxy (j : ℕ) (hj : j ≤ b) : 2 * (a + 2 * j) ≤ K := by
    have hRR : (2 * R : ℝ) ≤ K := by
      have hcast : (2 * R : ℝ) = 2 * (R : ℝ) := by push_cast; ring
      rw [hcast]
      nlinarith
    have hRRnat : 2 * R ≤ K := by exact_mod_cast hRR
    have := hsmall j hj
    omega
  have hcost (j : ℕ) (hj : j ≤ b) : (a + 2 * j) + q ≤ K := by
    have := hsmall j hj
    omega
  have hroot (j : ℕ) (hj : j ≤ b) : a + 2 * j ≤ q := by
    have hsmallR : ((a + 2 * j : ℕ) : ℝ) ≤ R := by
      exact_mod_cast hsmall j hj
    have hrR : ((a + 2 * j : ℕ) : ℝ) ≤ q := by nlinarith
    exact_mod_cast hrR
  have hdensity (j : ℕ) (hj : j ≤ b) :
      12 * cliqueMatchingThreshold a j +
        5000 * (Fintype.card (CliqueMatchingLabels a j) : ℝ) ≤
        (q : ℝ) / 2 := by
    have hα := cliqueMatching_alpha_le_scale a j ha
    have hscale := hscalej j hj
    have hbound : 12 * cliqueMatchingThreshold a j +
        5000 * (Fintype.card (CliqueMatchingLabels a j) : ℝ) ≤
        21000 * M := by nlinarith
    nlinarith
  exact woven_of_cliqueMatching_rootedDensity G a b K q hconn
    hproxy hcost hroot hdensity hRD

end HadwigerLean.Woven
