import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Numerical estimates for the Theorem 4 subgraph-ratio comparison. -/

namespace HadwigerLean.Deduction

/-- The logarithmic cost of enlarging the minor order from `t` to at most
`42t` fits within the final coefficient `3^9`. -/
theorem log_fortytwo_mul_le (t : ℕ) (ht : 3 ≤ t) :
    Real.log (42 * (t : ℝ)) ≤ (9 / 2 : ℝ) * Real.log (t : ℝ) := by
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hthree : (3 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hlogthree : Real.log (42 : ℝ) ≤ (7 / 2 : ℝ) * Real.log (3 : ℝ) := by
    have hp : (42 : ℝ) ^ 2 ≤ (3 : ℝ) ^ 7 := by norm_num
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 42 ^ 2) hp
    rw [Real.log_pow, Real.log_pow] at hh
    norm_num at hh
    linarith
  have hlogt : Real.log (3 : ℝ) ≤ Real.log (t : ℝ) :=
    Real.log_le_log (by norm_num) hthree
  rw [Real.log_mul (by norm_num : (42 : ℝ) ≠ 0) htpos.ne']
  nlinarith

/-- The final `3^9` coefficient pays for any graph of minor order at most
`42t`, even when its size was initially bounded at that larger order. -/
theorem fortytwo_order_log_budget (t q : ℕ) (ht : 3 ≤ t)
    (hq : q ≤ 42 * t) :
    (q : ℝ) * (Real.log (q : ℝ)) ^ 4 ≤
      (3 ^ 9 : ℕ) * (t : ℝ) * (Real.log (t : ℝ)) ^ 4 := by
  have hqreal : (q : ℝ) ≤ 42 * (t : ℝ) := by exact_mod_cast hq
  have hlogq : Real.log (q : ℝ) ≤ (9 / 2 : ℝ) * Real.log (t : ℝ) := by
    by_cases hq0 : q = 0
    · simp [hq0]
      have hlogt : 0 ≤ Real.log (t : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ t))
      positivity
    · have hqpos : (0 : ℝ) < (q : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hq0
      exact (Real.log_le_log hqpos hqreal).trans
        (log_fortytwo_mul_le t ht)
  have hlogq0 : 0 ≤ Real.log (q : ℝ) := by
    by_cases hq0 : q = 0
    · simp [hq0]
    · have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hq0)
      exact Real.log_nonneg hq1
  have hlogt0 : 0 ≤ Real.log (t : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ t))
  have hpow : (Real.log (q : ℝ)) ^ 4 ≤
      ((9 / 2 : ℝ) * Real.log (t : ℝ)) ^ 4 :=
    pow_le_pow_left₀ hlogq0 hlogq 4
  have hfirst : (q : ℝ) * (Real.log (q : ℝ)) ^ 4 ≤
      42 * (t : ℝ) * ((9 / 2 : ℝ) * Real.log (t : ℝ)) ^ 4 := by
    gcongr
  have hprod : 0 ≤ (t : ℝ) * (Real.log (t : ℝ)) ^ 4 := by positivity
  calc
    (q : ℝ) * (Real.log (q : ℝ)) ^ 4 ≤
        42 * (t : ℝ) * ((9 / 2 : ℝ) * Real.log (t : ℝ)) ^ 4 := hfirst
    _ = (42 * (9 / 2 : ℝ) ^ 4) *
        ((t : ℝ) * (Real.log (t : ℝ)) ^ 4) := by ring
    _ ≤ (3 ^ 9 : ℕ) * ((t : ℝ) * (Real.log (t : ℝ)) ^ 4) := by
      apply mul_le_mul_of_nonneg_right ?_ hprod
      norm_num
    _ = (3 ^ 9 : ℕ) * (t : ℝ) * (Real.log (t : ℝ)) ^ 4 := by ring


/-- The lower edge `x / sqrt (log x)` of the Delcourt--Postle window
is increasing for real orders at least three. -/
theorem dp_window_mono {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    x / Real.sqrt (Real.log x) ≤
      y / Real.sqrt (Real.log y) := by
  have hxpos : 0 < x := by linarith
  have hypos : 0 < y := by linarith
  have hlogxge : 1 ≤ Real.log x := by
    have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_three]
    exact hlog3.trans (Real.log_le_log (by norm_num) hx)
  have hlogxpos : 0 < Real.log x := by linarith
  have hlogypos : 0 < Real.log y :=
    lt_of_lt_of_le hlogxpos (Real.log_le_log hxpos hxy)
  let r : ℝ := y / x
  have hr : 1 ≤ r := by
    dsimp [r]
    exact (le_div_iff₀ hxpos).2 (by simpa using hxy)
  have hrpos : 0 < r := by linarith
  have hy : y = x * r := by
    dsimp [r]
    field_simp
  have hlogy : Real.log y = Real.log x + Real.log r := by
    rw [hy, Real.log_mul hxpos.ne' hrpos.ne']
  have hlogr : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hrpos
  have hmul : Real.log x + r - 1 ≤ r * Real.log x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr)
      (sub_nonneg.mpr hlogxge)]
  have hrsq : r ≤ r ^ 2 := by nlinarith
  have hsqmul : r * Real.log x ≤ r ^ 2 * Real.log x :=
    mul_le_mul_of_nonneg_right hrsq hlogxpos.le
  have hlogs : Real.log y ≤ r ^ 2 * Real.log x := by
    calc
      Real.log y = Real.log x + Real.log r := hlogy
      _ ≤ Real.log x + r - 1 := by linarith
      _ ≤ r * Real.log x := hmul
      _ ≤ r ^ 2 * Real.log x := hsqmul
  have hroot : Real.sqrt (Real.log y) ≤
      r * Real.sqrt (Real.log x) := by
    have hs : (Real.sqrt (Real.log y)) ^ 2 ≤
        (r * Real.sqrt (Real.log x)) ^ 2 := by
      rw [Real.sq_sqrt hlogypos.le, mul_pow, Real.sq_sqrt hlogxpos.le]
      exact hlogs
    have hrroot0 : 0 ≤ r * Real.sqrt (Real.log x) := by positivity
    nlinarith [Real.sqrt_nonneg (Real.log y)]
  have hprod : x * Real.sqrt (Real.log y) ≤
      y * Real.sqrt (Real.log x) := by
    have hh := mul_le_mul_of_nonneg_left hroot hxpos.le
    calc
      x * Real.sqrt (Real.log y) ≤
          x * (r * Real.sqrt (Real.log x)) := hh
      _ = y * Real.sqrt (Real.log x) := by rw [hy]; ring
  exact (div_le_div_iff₀ (Real.sqrt_pos.2 hlogxpos)
    (Real.sqrt_pos.2 hlogypos)).2 hprod
end HadwigerLean.Deduction




