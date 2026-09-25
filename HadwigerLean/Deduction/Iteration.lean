import HadwigerLean.Deduction.InitialLocal

/-! Nine iterations of the exponent bootstrap reach a power above four. -/

namespace HadwigerLean.Deduction

open HadwigerLean.Bootstrap

universe u

/-- The logarithmic exponent after `n` bootstrap steps from `1/3`. -/
noncomputable def bootstrapExponent (n : ℕ) : ℝ := ((4 : ℝ) / 3) ^ n / 3

theorem bootstrapExponent_pos (n : ℕ) : 0 < bootstrapExponent n := by
  unfold bootstrapExponent
  positivity

/-- The ninth bootstrap exponent exceeds four. -/
theorem bootstrapExponent_nine_gt_four : 4 < bootstrapExponent 9 := by
  norm_num [bootstrapExponent]

/-- Any proved bootstrap step can be iterated from checked Theorem 2. -/
theorem local_bound_iterate
    (hstep : ∀ (α : ℝ), 0 < α → LocalLinearBound.{u} α →
      LocalLinearBound.{u} (4 * α / 3)) (n : ℕ) :
    LocalLinearBound.{u} (bootstrapExponent n) := by
  induction n with
  | zero =>
      simpa [bootstrapExponent] using
        (initial_local_bound : LocalLinearBound.{u} ((1 : ℝ) / 3))
  | succ n ih =>
      have h := hstep (bootstrapExponent n) (bootstrapExponent_pos n) ih
      convert h using 1
      unfold bootstrapExponent
      rw [pow_succ]
      ring

end HadwigerLean.Deduction
