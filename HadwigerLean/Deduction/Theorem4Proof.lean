import HadwigerLean.Inseparability.CIComplete
import HadwigerLean.Deduction.Theorem4CompleteOfCI

/-! The unconditional Theorem 4 statement from chromatic inseparability. -/

namespace HadwigerLean.Deduction

open HadwigerLean.Inseparability

universe u

/-- The completed sharp chromatic inseparability theorem has exactly the
local-bound contract required by the Theorem 4 outer induction. -/
theorem theorem4CIInput_sharp :
    Theorem4CIInput.{u} ciCoefficient := by
  classical
  intro W instW Y q s hq hminor hlocal hχ
  letI : Fintype W := instW
  letI : DecidableEq W := Classical.decEq W
  letI : DecidableRel Y.Adj := Classical.decRel Y.Adj
  have hlocal' : ∀ U : Finset W,
      (U.card : ℝ) ≤ (ciCoefficient : ℝ) * (q : ℝ) *
        (Real.log (q : ℝ)) ^ 4 →
      chromatic (Y.induce (U : Set W)) ≤ q * s := by
    intro U hU
    apply hlocal U
    convert hU using 1
    norm_num [Real.rpow_natCast]
  have hχ' : 2 * ciChromaticBudget q s ≤ chromatic Y := by
    simpa only [ciChromaticBudget] using hχ
  exact chromatic_separable_of_local_bound_complete
    Y q s hq hminor hlocal' hχ'

/-- Theorem 4 in its exact maximum-ratio form. -/
theorem theorem4_proved : Theorem4Statement.{u} := by
  exact theorem4_of_ci ciCoefficient
    (by norm_num [ciCoefficient]) theorem4CIInput_sharp

end HadwigerLean.Deduction


