import HadwigerLean.Deduction.Corollary24Base
import Mathlib.Tactic

/-! The clique-minor coloring estimate at the low scales of Theorem 4. -/

namespace HadwigerLean.Deduction

/-- For every admissible low scale, the clique-minor coloring estimate fits
inside the `2000T` reserve. -/
theorem theorem4_base_chromatic_threshold
    (T a : ℕ) (hT : 3 ≤ T) (ha : 1 ≤ a)
    (hscale : (a : ℝ) ≤ (T : ℝ) / Real.sqrt (Real.log (T : ℝ))) :
    840 * (a : ℝ) * Real.sqrt (Real.log (14 * (a : ℝ))) + 1 <
      2000 * (T : ℝ) := by
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
  have hTge : (3 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hlogpos : 0 < Real.log (T : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  have hsqrtpos : 0 < Real.sqrt (Real.log (T : ℝ)) :=
    Real.sqrt_pos.2 hlogpos
  have hlogge : 1 ≤ Real.log (T : ℝ) := by
    have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      exact Real.exp_one_lt_three.le
    exact hlog3.trans (Real.log_le_log (by norm_num) hTge)
  have hrootge : 1 ≤ Real.sqrt (Real.log (T : ℝ)) :=
    (Real.one_le_sqrt).2 hlogge
  have haT : (a : ℝ) ≤ (T : ℝ) := by
    have hdiv : (T : ℝ) / Real.sqrt (Real.log (T : ℝ)) ≤ (T : ℝ) := by
      apply (div_le_iff₀ hsqrtpos).2
      nlinarith
    exact hscale.trans hdiv
  have h14T : (14 : ℝ) ≤ (T : ℝ) ^ 3 := by
    have hh : (3 : ℝ) ^ 3 ≤ (T : ℝ) ^ 3 := by gcongr
    norm_num at hh ⊢
    nlinarith
  have h14a : 14 * (a : ℝ) ≤ (T : ℝ) ^ 4 := by
    calc
      14 * (a : ℝ) ≤ 14 * (T : ℝ) := by gcongr
      _ ≤ (T : ℝ) ^ 3 * (T : ℝ) := by
        exact mul_le_mul_of_nonneg_right h14T hTpos.le
      _ = (T : ℝ) ^ 4 := by ring
  have hlog14a : Real.log (14 * (a : ℝ)) ≤ 4 * Real.log (T : ℝ) := by
    calc
      Real.log (14 * (a : ℝ)) ≤ Real.log ((T : ℝ) ^ 4) :=
        Real.log_le_log (by positivity) h14a
      _ = 4 * Real.log (T : ℝ) := by rw [Real.log_pow]; ring
  have hsqrtbound : Real.sqrt (Real.log (14 * (a : ℝ))) ≤
      2 * Real.sqrt (Real.log (T : ℝ)) := by
    have hle := Real.sqrt_le_sqrt hlog14a
    have hright : Real.sqrt (4 * Real.log (T : ℝ)) ≤
        2 * Real.sqrt (Real.log (T : ℝ)) := by
      have hsq : (Real.sqrt (4 * Real.log (T : ℝ))) ^ 2 ≤
          (2 * Real.sqrt (Real.log (T : ℝ))) ^ 2 := by
        rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt hlogpos.le]
        nlinarith
      nlinarith [Real.sqrt_nonneg (4 * Real.log (T : ℝ))]
    exact hle.trans hright
  have hprod : (a : ℝ) * Real.sqrt (Real.log (14 * (a : ℝ))) ≤
      2 * (T : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hsqrtbound ha_pos.le
    have hscale' : (a : ℝ) * Real.sqrt (Real.log (T : ℝ)) ≤ (T : ℝ) :=
      (le_div_iff₀ hsqrtpos).mp hscale
    nlinarith
  nlinarith

/-- The low-scale obstruction follows from the checked clique-minor
density and greedy-coloring bound. -/
theorem theorem4_base_chromatic_lt
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (T a : ℕ) (hT : 3 ≤ T) (ha : 1 ≤ a)
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
    _ < 2000 * (T : ℝ) := theorem4_base_chromatic_threshold T a hT ha hscale

end HadwigerLean.Deduction
