import HadwigerLean.Quantitative.Theorem2FinalBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Eventual estimates for the conditional Theorem 1 deduction. -/

namespace HadwigerLean.Deduction

open Filter

/-- A convenient consequence of logarithm being little-o of the identity. -/
theorem eventually_log_mul_bound :
    ∀ᶠ x : ℝ in atTop, 2000 * Real.log (100 * x) ≤ x := by
  have h := (Real.isLittleO_log_id_atTop.const_mul_left (200000 : ℝ)).eventuallyLE
  have h' : ∀ᶠ x : ℝ in atTop,
      200000 * Real.log x ≤ x := by
    filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with x hx hx0
    have hx' : ‖x‖ = x := Real.norm_eq_abs x |>.trans (abs_of_nonneg hx0)
    calc
      200000 * Real.log x ≤ ‖(200000 : ℝ) * Real.log x‖ := by
        simpa only [Real.norm_eq_abs] using le_abs_self ((200000 : ℝ) * Real.log x)
      _ ≤ ‖x‖ := hx
      _ = x := hx'
  have hcomp : Tendsto (fun x : ℝ => 100 * x) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  filter_upwards [hcomp.eventually h'] with x hx
  nlinarith


/-- The exact additive term of Theorem 2 is dominated by an exponential
once the logarithmic factor is below the cube-root scale. -/
theorem Aepsilon_inv_le_exp_cube {x : ℝ} (hx : 0 < x)
    (hlog : 2000 * Real.log (100 * x) ≤ x) :
    HadwigerLean.Theorem2.Aepsilon (x⁻¹) ≤ Real.exp (x ^ 3) := by
  have hx0 : x ≠ 0 := hx.ne'
  have hbase : 100 / x⁻¹ = 100 * x := by field_simp
  have hexp : 2000 / (x⁻¹) ^ 2 = 2000 * x ^ 2 := by field_simp
  rw [HadwigerLean.Theorem2.Aepsilon, hbase, hexp]
  have hbasepos : 0 < 100 * x := by positivity
  apply (Real.log_le_iff_le_exp (Real.rpow_pos_of_pos hbasepos _)).mp
  rw [Real.log_rpow hbasepos]
  have hmul := mul_le_mul_of_nonneg_right hlog (sq_nonneg x)
  nlinarith

/-- The cube-root logarithmic choice of epsilon eventually satisfies all
analytic requirements for the initial local bound. -/
theorem eventually_initial_epsilon :
    ∀ᶠ t : ℕ in atTop,
      2 ≤ t ∧
      let x : ℝ := (Real.log (t : ℝ)) ^ ((1 : ℝ) / 3)
      1 ≤ x ∧
      0 < x⁻¹ ∧
      x⁻¹ ≤ 1 ∧
      HadwigerLean.Theorem2.Aepsilon (x⁻¹) ≤ (t : ℝ) ∧
      x⁻¹ * ((t : ℝ) * x) = (t : ℝ) := by
  have htop : Tendsto
      (fun t : ℕ => (Real.log (t : ℝ)) ^ ((1 : ℝ) / 3)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlog : ∀ᶠ t : ℕ in atTop,
      2000 * Real.log (100 * (Real.log (t : ℝ)) ^ ((1 : ℝ) / 3)) ≤
        (Real.log (t : ℝ)) ^ ((1 : ℝ) / 3) :=
    htop.eventually eventually_log_mul_bound
  filter_upwards [eventually_ge_atTop (2 : ℕ), htop.eventually_ge_atTop (1 : ℝ), hlog]
    with t ht hx hsmall
  dsimp
  refine ⟨ht, hx, inv_pos.mpr (lt_of_lt_of_le (by norm_num) hx),
    inv_le_one_of_one_le₀ hx, ?_, ?_⟩
  · have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
    have hL : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ t))
    have hx3 : ((Real.log (t : ℝ)) ^ ((1 : ℝ) / 3)) ^ 3 = Real.log (t : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
      norm_num
    have hA := Aepsilon_inv_le_exp_cube (lt_of_lt_of_le (by norm_num) hx) hsmall
    rw [hx3, Real.exp_log htpos] at hA
    exact hA
  · have hxpos : 0 < (Real.log (t : ℝ)) ^ ((1 : ℝ) / 3) :=
      lt_of_lt_of_le (by norm_num) hx
    field_simp

/-- For exponent greater than four, the extra logarithmic power absorbs any
fixed coefficient at sufficiently large integer arguments. -/
theorem eventually_log_power_window {α : ℝ} (hα : 4 < α) (C : ℕ) :
    ∀ᶠ a : ℕ in atTop,
      (C : ℝ) * (Real.log (a : ℝ)) ^ (4 : ℝ) ≤
        (Real.log (a : ℝ)) ^ α := by
  have htop : Tendsto
      (fun a : ℕ => (Real.log (a : ℝ)) ^ (α - 4)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [htop.eventually_ge_atTop (C : ℝ), eventually_ge_atTop (2 : ℕ)]
    with a hpow ha
  have hlogpos : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < a))
  calc
    (C : ℝ) * (Real.log (a : ℝ)) ^ (4 : ℝ) ≤
        (Real.log (a : ℝ)) ^ (α - 4) *
          (Real.log (a : ℝ)) ^ (4 : ℝ) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hlogpos.le _)
    _ = (Real.log (a : ℝ)) ^ α := by
      simpa only [sub_add_cancel] using
        (Real.rpow_add hlogpos (α - 4) (4 : ℝ)).symm

/-- The lower edge of the Delcourt--Postle window is at least the square root
of `t` for `t ≥ 2`. -/
theorem sqrt_le_dp_window {t : ℝ} (ht : 2 ≤ t) :
    Real.sqrt t ≤ t / Real.sqrt (Real.log t) := by
  have htpos : 0 < t := by linarith
  have hlogpos : 0 < Real.log t := Real.log_pos (by linarith)
  have hdenpos : 0 < Real.sqrt (Real.log t) := Real.sqrt_pos.2 hlogpos
  have hlogle : Real.log t ≤ t := Real.log_le_self htpos.le
  have hsqrtle : Real.sqrt (Real.log t) ≤ Real.sqrt t := Real.sqrt_le_sqrt hlogle
  apply (le_div_iff₀ hdenpos).2
  calc
    Real.sqrt t * Real.sqrt (Real.log t) ≤ Real.sqrt t * Real.sqrt t :=
      mul_le_mul_of_nonneg_left hsqrtle (Real.sqrt_nonneg t)
    _ = t := Real.mul_self_sqrt htpos.le

/-- Uniform control of every integer in the Theorem 4 window. -/
theorem eventual_dp_window {α : ℝ} (hα : 4 < α) (C t₀ : ℕ) :
    ∃ T₀ : ℕ, 3 ≤ T₀ ∧
      ∀ (t a : ℕ), T₀ ≤ t →
        (t : ℝ) / Real.sqrt (Real.log (t : ℝ)) ≤ (a : ℝ) →
        a ≤ t →
        t₀ ≤ a ∧
        (C : ℝ) * (Real.log (a : ℝ)) ^ (4 : ℝ) ≤
          (Real.log (a : ℝ)) ^ α := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    ((eventually_ge_atTop t₀).and (eventually_log_power_window hα C))
  refine ⟨max 3 (B * B), by omega, ?_⟩
  intro t a ht hwindow _
  have ht2 : 2 ≤ (t : ℝ) := by exact_mod_cast (by omega : 2 ≤ t)
  have hBsq : (B : ℝ) ^ 2 ≤ (t : ℝ) := by
    exact_mod_cast (by nlinarith [Nat.le_max_right 3 (B * B), ht] : B ^ 2 ≤ t)
  have hBsqrt : (B : ℝ) ≤ Real.sqrt (t : ℝ) := Real.le_sqrt_of_sq_le hBsq
  have hBreal : (B : ℝ) ≤ (a : ℝ) :=
    hBsqrt.trans ((sqrt_le_dp_window ht2).trans hwindow)
  have hBnat : B ≤ a := by exact_mod_cast hBreal
  exact hB a hBnat

/-- Every nonbase outer scale has logarithm at least half that of the
excluded-minor order after the factor `14`. -/
theorem bootstrap_scale_log_lower {t T a : ℕ} (ht : 2 ≤ t) (htT : t ≤ T)
    (ha : (T : ℝ) / Real.sqrt (Real.log (T : ℝ)) < (a : ℝ)) :
    Real.log (t : ℝ) / 2 ≤ Real.log (14 * (a : ℝ)) := by
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hT2 : 2 ≤ (T : ℝ) := by exact_mod_cast (ht.trans htT)
  have htsqrt : Real.sqrt (t : ℝ) ≤ Real.sqrt (T : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast htT)
  have hasqrt : Real.sqrt (t : ℝ) ≤ (a : ℝ) :=
    htsqrt.trans ((sqrt_le_dp_window hT2).trans ha.le)
  have hapos : (0 : ℝ) < (a : ℝ) :=
    (Real.sqrt_pos.2 htpos).trans_le hasqrt
  have ha14 : (a : ℝ) ≤ 14 * (a : ℝ) := by nlinarith
  calc
    Real.log (t : ℝ) / 2 = Real.log (Real.sqrt (t : ℝ)) :=
      (Real.log_sqrt htpos.le).symm
    _ ≤ Real.log (14 * (a : ℝ)) :=
      Real.log_le_log (Real.sqrt_pos.2 htpos) (hasqrt.trans ha14)
end HadwigerLean.Deduction
