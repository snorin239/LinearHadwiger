import Mathlib.Tactic

/-!
# An explicit exponential union budget

The rounding argument uses the fourth power of `exp (x / 4) ≥ x / 4`.
This gives enough decay for the paper's order threshold even with the
slightly weaker centered Chernoff exponent `μ² n / 256`.
-/

namespace HadwigerLean.Theorem2

private theorem fourth_power_exp_tail {x : ℝ} (hx : 0 ≤ x) :
    (x / 4) ^ 4 * Real.exp (-x) ≤ 1 := by
  have hlow : x / 4 ≤ Real.exp (x / 4) := by
    have h := Real.add_one_le_exp (x / 4)
    linarith
  have hpow : (x / 4) ^ 4 ≤ (Real.exp (x / 4)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hlow 4
  have heq : (Real.exp (x / 4)) ^ 4 = Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    (x / 4) ^ 4 * Real.exp (-x) ≤
        Real.exp x * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right (heq ▸ hpow) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- The fourth-order exponential estimate gives a strict union budget
for `r ≥ 2` and the scaled lower bound on the sampled order. -/
theorem sampled_union_budget_lt_one
    {r n μ : ℝ} (hr : 2 ≤ r) (hμ : 0 < μ)
    (hscale : 1000000 * r ^ 4 ≤ μ ^ 4 * n) :
    8 * r ^ 2 * n ^ 2 * Real.exp (-(μ ^ 2 * n / 256)) < 1 := by
  have hrpos : 0 < r := by linarith
  have hμ4 : 0 < μ ^ 4 := pow_pos hμ _
  have hnpos : 0 < n := by
    by_contra hn
    have hnonpos : n ≤ 0 := le_of_not_gt hn
    have hprod : μ ^ 4 * n ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hμ4.le hnonpos
    nlinarith [pow_pos hrpos 4]
  have hr6 : (64 : ℝ) ≤ r ^ 6 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hr 6
    norm_num at h
    exact h
  have hcoef : 8 * (1024 : ℝ) ^ 4 < 1000000000000 * r ^ 6 := by
    nlinarith [hr6]
  have hbase :
      8 * (1024 : ℝ) ^ 4 * r ^ 2 < (1000000 * r ^ 4) ^ 2 := by
    calc
      8 * (1024 : ℝ) ^ 4 * r ^ 2 <
          (1000000000000 * r ^ 6) * r ^ 2 :=
        mul_lt_mul_of_pos_right hcoef (sq_pos_of_pos hrpos)
      _ = (1000000 * r ^ 4) ^ 2 := by ring
  have hsq : (1000000 * r ^ 4) ^ 2 ≤ (μ ^ 4 * n) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hscale 2
  have hstrong :
      8 * (1024 : ℝ) ^ 4 * r ^ 2 < (μ ^ 4 * n) ^ 2 :=
    hbase.trans_le hsq
  have hmul := mul_lt_mul_of_pos_right hstrong (sq_pos_of_pos hnpos)
  have hleft :
      (8 * (1024 : ℝ) ^ 4 * r ^ 2) * n ^ 2 =
        (8 * r ^ 2 * n ^ 2) * (1024 : ℝ) ^ 4 := by ring
  have hright : ((μ ^ 4 * n) ^ 2) * n ^ 2 = μ ^ 8 * n ^ 4 := by ring
  rw [hleft, hright] at hmul
  have htarget0 :
      8 * r ^ 2 * n ^ 2 < μ ^ 8 * n ^ 4 / (1024 : ℝ) ^ 4 :=
    (lt_div_iff₀ (by norm_num : (0 : ℝ) < (1024 : ℝ) ^ 4)).2 hmul
  have heq :
      (μ ^ 2 * n / 256 / 4) ^ 4 =
        μ ^ 8 * n ^ 4 / (1024 : ℝ) ^ 4 := by ring
  have htarget :
      8 * r ^ 2 * n ^ 2 < (μ ^ 2 * n / 256 / 4) ^ 4 := by
    rw [heq]
    exact htarget0
  have hexp := fourth_power_exp_tail
    (show 0 ≤ μ ^ 2 * n / 256 by positivity)
  calc
    8 * r ^ 2 * n ^ 2 * Real.exp (-(μ ^ 2 * n / 256)) <
        (μ ^ 2 * n / 256 / 4) ^ 4 *
          Real.exp (-(μ ^ 2 * n / 256)) :=
      mul_lt_mul_of_pos_right htarget (Real.exp_pos _)
    _ ≤ 1 := hexp

end HadwigerLean.Theorem2