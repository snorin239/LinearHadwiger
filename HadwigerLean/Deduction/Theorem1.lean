import HadwigerLean.Deduction.FromLocal
import HadwigerLean.Deduction.Iteration

/-! The final quantitative deduction after the graph bootstrap is proved. -/

namespace HadwigerLean.Deduction

open HadwigerLean.Bootstrap

universe u

/-- Theorem 1 follows from the exact Delcourt--Postle input and a proved
exponent-bootstrap step. The latter is supplied by Corollary 24 and the graph
lemmas in `Bootstrap/Step.lean`. -/
theorem linear_of_bootstrap
    (h4 : Theorem4Statement.{u})
    (hstep : ∀ (α : ℝ), 0 < α → LocalLinearBound.{u} α →
      LocalLinearBound.{u} (4 * α / 3)) :
    ∃ C : ℕ,
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (t : ℕ),
        2 ≤ t → ¬ HadwigerLean.HasCliqueMinor G t →
        HadwigerLean.chromatic G ≤ C * t := by
  exact linear_of_local_and_window h4 (bootstrapExponent 9)
    (local_bound_iterate hstep 9)
    (fun C t₀ _ => eventual_dp_window bootstrapExponent_nine_gt_four C t₀)

end HadwigerLean.Deduction
