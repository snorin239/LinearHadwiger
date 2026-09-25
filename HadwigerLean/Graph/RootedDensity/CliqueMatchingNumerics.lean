import HadwigerLean.Graph.RootedDensity.CliqueMatching
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Numerical budgets for the clique-plus-matching target. -/

namespace HadwigerLean.RootedDensity

/-- The scale appearing in the uniform woven theorem. -/
noncomputable def cliqueMatchingScale (a b : ℕ) : ℝ :=
  max ((a : ℝ) * Real.sqrt (Real.log (a : ℝ))) (b : ℝ)

/-- At `a ≥ 2`, the target order is at most four times the natural
`max{a√log a,b}` scale. -/
theorem cliqueMatching_order_le_four_scale
    (a b : ℕ) (ha : 2 ≤ a) :
    (Fintype.card (CliqueMatchingLabels a b) : ℝ) ≤
      4 * cliqueMatchingScale a b := by
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    nlinarith
  have hlogle : Real.log 2 ≤ Real.log (a : ℝ) :=
    Real.log_le_log (by norm_num) haR
  have hloga : (1 / 2 : ℝ) ≤ Real.log (a : ℝ) := hlog2.trans hlogle
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt (Real.log (a : ℝ)) := by
    have hsq := Real.sq_sqrt (by linarith : 0 ≤ Real.log (a : ℝ))
    have hn := Real.sqrt_nonneg (Real.log (a : ℝ))
    nlinarith
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have haprod : (a : ℝ) / 2 ≤
      (a : ℝ) * Real.sqrt (Real.log (a : ℝ)) := by
    nlinarith [mul_nonneg ha0 (by linarith :
      0 ≤ Real.sqrt (Real.log (a : ℝ)) - 1 / 2)]
  have hfirst : (a : ℝ) * Real.sqrt (Real.log (a : ℝ)) ≤
      cliqueMatchingScale a b := le_max_left _ _
  have hsecond : (b : ℝ) ≤ cliqueMatchingScale a b := le_max_right _ _
  rw [cliqueMatchingLabels_card]
  push_cast
  nlinarith

/-- The sharp rooted-density constant from Appendix F, when applied to
`K_a + b K₂`, stays below `21000` times the woven scale. -/
theorem cliqueMatching_alpha_le_scale
    (a b : ℕ) (ha : 2 ≤ a) :
    12 * cliqueMatchingThreshold a b +
      5000 * (Fintype.card (CliqueMatchingLabels a b) : ℝ) ≤
      21000 * cliqueMatchingScale a b := by
  have hc : cliqueMatchingThreshold a b ≤
      32 * cliqueMatchingScale a b := by
    unfold cliqueMatchingThreshold cliqueMatchingScale
    have hfirst : (a : ℝ) * Real.sqrt (Real.log (a : ℝ)) ≤
        max ((a : ℝ) * Real.sqrt (Real.log (a : ℝ))) (b : ℝ) := le_max_left _ _
    have hsecond : (b : ℝ) ≤
        max ((a : ℝ) * Real.sqrt (Real.log (a : ℝ))) (b : ℝ) := le_max_right _ _
    nlinarith
  have hh := cliqueMatching_order_le_four_scale a b ha
  have hscale : 0 ≤ cliqueMatchingScale a b := by
    unfold cliqueMatchingScale
    exact le_max_of_le_right (Nat.cast_nonneg _)
  nlinarith

end HadwigerLean.RootedDensity
