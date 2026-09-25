import HadwigerLean.Deduction.Corollary24Base
import Mathlib.Tactic

/-! The low-scale minor branch in the Corollary 24 outer induction. -/

namespace HadwigerLean.Deduction

/-- At a base scale, the `2000T` chromatic reserve forces the required
clique minor. -/
theorem cor24_base_hasCliqueMinor
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (T a : ℕ) (hT : 100 ≤ T) (ha : 1 ≤ a)
    (hscale : (a : ℝ) ≤ (T : ℝ) / Real.sqrt (Real.log (T : ℝ)))
    (hχ : 2000 * T ≤ HadwigerLean.chromatic G) :
    HadwigerLean.HasCliqueMinor G (14 * a) := by
  classical
  by_contra hminor
  have hlt := cor24_base_chromatic_lt G T a hT ha hscale hminor
  have hχR : 2000 * (T : ℝ) ≤ (HadwigerLean.chromatic G : ℝ) := by
    exact_mod_cast hχ
  exact (not_lt_of_ge hχR) hlt

end HadwigerLean.Deduction
