import HadwigerLean.Woven.OuterScales
import Mathlib.Tactic

/-! Comparison of the final integer outer scale with the logarithmic scale. -/

namespace HadwigerLean.Deduction

/-- A natural-number bound underlying the final scale comparison. -/
private theorem twice_mul_four_pow_le_nine_pow
    (m : ℕ) (hm : 2 ≤ m) : 2 * m * 4 ^ m ≤ 9 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      have hcoeff : 8 * (m + 1) ≤ 18 * m := by omega
      calc
        2 * (m + 1) * 4 ^ (m + 1) = 8 * (m + 1) * 4 ^ m := by
          rw [pow_succ]
          ring
        _ ≤ 18 * m * 4 ^ m := Nat.mul_le_mul_right _ hcoeff
        _ = 9 * (2 * m * 4 ^ m) := by ring
        _ ≤ 9 * 9 ^ m := Nat.mul_le_mul_left _ ih
        _ = 9 ^ (m + 1) := by rw [pow_succ]; ring

/-- For top scale `T=3^m≥100`, the final integer scale `2^m` is at most
`T/√(log T)`. -/
theorem cor24_outerScale_last_le_top_div_sqrt_log
    (m T : ℕ) (hT : T = 3 ^ m) (hlarge : 100 ≤ T) :
    (HadwigerLean.Woven.outerScale m m : ℝ) ≤
      (T : ℝ) / Real.sqrt (Real.log (T : ℝ)) := by
  subst T
  have hm : 2 ≤ m := by
    by_contra h
    have hm1 : m ≤ 1 := by omega
    interval_cases m <;> norm_num at hlarge
  have hnat := twice_mul_four_pow_le_nine_pow m hm
  have hnatR : (2 * m * 4 ^ m : ℝ) ≤ (9 ^ m : ℝ) := by
    exact_mod_cast hnat
  have htop : (1 : ℝ) < (3 ^ m : ℕ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 100) hlarge)
  have hlogpos : 0 < Real.log ((3 ^ m : ℕ) : ℝ) := Real.log_pos htop
  have hlog3 : Real.log (3 : ℝ) ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (3 : ℝ))
    norm_num at h
    exact h
  have hlogbound : Real.log ((3 ^ m : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hlog3
      (show (0 : ℝ) ≤ m by positivity)
    calc
      Real.log ((3 ^ m : ℕ) : ℝ) = (m : ℝ) * Real.log 3 := by
        simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      _ ≤ (m : ℝ) * 2 := hmul
      _ = 2 * (m : ℝ) := by ring
  have hfour : (((2 ^ m : ℕ) : ℝ)) ^ 2 = ((4 ^ m : ℕ) : ℝ) := by
    push_cast
    calc
      ((2 : ℝ) ^ m) ^ 2 = (2 : ℝ) ^ (m * 2) := by rw [pow_mul]
      _ = (2 : ℝ) ^ (2 * m) := by congr 1; omega
      _ = ((2 : ℝ) ^ 2) ^ m := by rw [pow_mul]
      _ = (4 : ℝ) ^ m := by norm_num
  have hnine : (((3 ^ m : ℕ) : ℝ)) ^ 2 = ((9 ^ m : ℕ) : ℝ) := by
    push_cast
    calc
      ((3 : ℝ) ^ m) ^ 2 = (3 : ℝ) ^ (m * 2) := by rw [pow_mul]
      _ = (3 : ℝ) ^ (2 * m) := by congr 1; omega
      _ = ((3 : ℝ) ^ 2) ^ m := by rw [pow_mul]
      _ = (9 : ℝ) ^ m := by norm_num
  have hsq : (((2 ^ m : ℕ) : ℝ) *
      Real.sqrt (Real.log ((3 ^ m : ℕ) : ℝ))) ^ 2 ≤
      (((3 ^ m : ℕ) : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hlogpos.le, hfour, hnine]
    have hmul := mul_le_mul_of_nonneg_left hlogbound
      (show (0 : ℝ) ≤ (4 ^ m : ℕ) by positivity)
    calc
      ((4 ^ m : ℕ) : ℝ) * Real.log ((3 ^ m : ℕ) : ℝ) ≤
          ((4 ^ m : ℕ) : ℝ) * (2 * (m : ℝ)) := hmul
      _ = 2 * (m : ℝ) * ((4 ^ m : ℕ) : ℝ) := by ring
      _ ≤ ((9 ^ m : ℕ) : ℝ) := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using hnatR
  have hproduct : (((2 ^ m : ℕ) : ℝ) *
      Real.sqrt (Real.log ((3 ^ m : ℕ) : ℝ))) ≤
      ((3 ^ m : ℕ) : ℝ) := by
    have hp : (0 : ℝ) ≤ (((2 ^ m : ℕ) : ℝ) *
        Real.sqrt (Real.log ((3 ^ m : ℕ) : ℝ))) := by positivity
    have hq : (0 : ℝ) ≤ ((3 ^ m : ℕ) : ℝ) := by positivity
    nlinarith
  simpa [HadwigerLean.Woven.outerScale_last] using
    ((le_div_iff₀ (Real.sqrt_pos.2 hlogpos)).2 hproduct)

end HadwigerLean.Deduction
