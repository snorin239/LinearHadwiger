import HadwigerLean.Deduction.Corollary24Numerics
import HadwigerLean.Graph.CliqueDensity.Coloring
import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The low-scale clique-minor coloring threshold for Corollary 24
-/

namespace HadwigerLean.Deduction

/-- At a base scale, the coefficient-30 clique-minor chromatic estimate
is strictly below the `2000T` reserve. The slack `14a ≤ T²` avoids
carrying a decimal estimate for `log 14 / log T`. -/
theorem cor24_base_chromatic_threshold
    (T a : ℕ) (hT : 100 ≤ T) (ha : 1 ≤ a)
    (hscale : (a : ℝ) ≤ (T : ℝ) / Real.sqrt (Real.log (T : ℝ))) :
    840 * (a : ℝ) * Real.sqrt (Real.log (14 * (a : ℝ))) + 1 <
      2000 * (T : ℝ) := by
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hT14 : (14 : ℝ) ≤ (T : ℝ) := by exact_mod_cast (by omega : 14 ≤ T)
  have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
  have hlogpos : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  have hsqrtpos : 0 < Real.sqrt (Real.log (T : ℝ)) := Real.sqrt_pos.2 hlogpos
  have haT : (a : ℝ) ≤ (T : ℝ) := by
    have hrootge : 1 ≤ Real.sqrt (Real.log (T : ℝ)) := by
      -- `log 100 > 1`, and the square root is monotone.
      have hlogge : 1 ≤ Real.log (T : ℝ) := by
        have h100 : (100 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
        have hlog100 : (1 : ℝ) ≤ Real.log 100 := by
          rw [Real.le_log_iff_exp_le (by norm_num)]
          nlinarith [Real.exp_one_lt_three]
        exact hlog100.trans (Real.log_le_log (by norm_num) h100)
      exact (Real.one_le_sqrt).2 hlogge
    have hdiv : (T : ℝ) / Real.sqrt (Real.log (T : ℝ)) ≤ (T : ℝ) := by
      apply (div_le_iff₀ hsqrtpos).2
      nlinarith
    exact hscale.trans hdiv
  have h14a : 14 * (a : ℝ) ≤ (T : ℝ) ^ 2 := by nlinarith
  have hlog14a : Real.log (14 * (a : ℝ)) ≤ 2 * Real.log (T : ℝ) := by
    have hleft : 0 < 14 * (a : ℝ) := by positivity
    calc
      Real.log (14 * (a : ℝ)) ≤ Real.log ((T : ℝ) ^ 2) :=
        Real.log_le_log hleft h14a
      _ = 2 * Real.log (T : ℝ) := by rw [Real.log_pow]; ring
  have hsqrtbound : Real.sqrt (Real.log (14 * (a : ℝ))) ≤
      2 * Real.sqrt (Real.log (T : ℝ)) := by
    have hle := Real.sqrt_le_sqrt hlog14a
    have hright : Real.sqrt (2 * Real.log (T : ℝ)) ≤
        2 * Real.sqrt (Real.log (T : ℝ)) := by
      have hsq : (Real.sqrt (2 * Real.log (T : ℝ))) ^ 2 ≤
          (2 * Real.sqrt (Real.log (T : ℝ))) ^ 2 := by
        rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt hlogpos.le]
        nlinarith
      nlinarith [Real.sqrt_nonneg (2 * Real.log (T : ℝ))]
    exact hle.trans hright
  have hprod : (a : ℝ) * Real.sqrt (Real.log (14 * (a : ℝ))) ≤
      2 * (T : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hsqrtbound ha_pos.le
    have hscale' : (a : ℝ) * Real.sqrt (Real.log (T : ℝ)) ≤ (T : ℝ) := by
      exact (le_div_iff₀ hsqrtpos).mp hscale
    nlinarith
  have hTge : (100 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  nlinarith


/-- The low-scale Corollary 24 base case follows from the checked
clique-minor density and greedy-coloring bounds. -/
theorem cor24_base_chromatic_lt
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (T a : ℕ) (hT : 100 ≤ T) (ha : 1 ≤ a)
    (hscale : (a : ℝ) ≤ (T : ℝ) / Real.sqrt (Real.log (T : ℝ)))
    (hminor : ¬ HadwigerLean.HasCliqueMinor G (14 * a)) :
    (HadwigerLean.chromatic G : ℝ) < 2000 * (T : ℝ) := by
  have hr : 2 ≤ 14 * a := by omega
  have hχ := HadwigerLean.chromatic_lt_kt_color_threshold G (14 * a) hr hminor
  calc
    (HadwigerLean.chromatic G : ℝ) <
        60 * ((14 * a : ℕ) : ℝ) * Real.sqrt (Real.log ((14 * a : ℕ) : ℝ)) + 1 := hχ
    _ = 840 * (a : ℝ) * Real.sqrt (Real.log (14 * (a : ℝ))) + 1 := by
      push_cast
      ring
    _ < 2000 * (T : ℝ) := cor24_base_chromatic_threshold T a hT ha hscale

end HadwigerLean.Deduction
