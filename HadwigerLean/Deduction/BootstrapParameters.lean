import HadwigerLean.Deduction.Asymptotics
import HadwigerLean.Bootstrap.Definitions
import Mathlib.Algebra.Order.Floor.Semifield

/-! Uniform parameter estimates for the exponent bootstrap. -/

namespace HadwigerLean.Deduction

open Filter

/-- The quotient-order exponent identity used after packing. -/
theorem bootstrap_order_power (α x : ℝ) (hx : 0 < x) :
    x ^ (4 * α / 3) = x ^ (α / 3) * x ^ α := by
  calc
    x ^ (4 * α / 3) = x ^ (α / 3 + α) := by congr 1; ring
    _ = x ^ (α / 3) * x ^ α := Real.rpow_add hx _ _

/-- Uniform numerical parameters at every outer-recursion scale. The
assumptions `t ≤ T` and the strict scale cutoff are the only parts of the
least-power-of-three condition needed for these estimates. -/
theorem eventual_bootstrap_parameters {α : ℝ} (hα : 0 < α) (t₀ : ℕ) :
    ∃ T₀ : ℕ, 3 ≤ T₀ ∧
      ∀ (t T a : ℕ), T₀ ≤ t → t ≤ T →
        (T : ℝ) / Real.sqrt (Real.log (T : ℝ)) < (a : ℝ) →
        a ≤ T →
        let k : ℕ := ⌈(Real.log (t : ℝ)) ^ (α / 3)⌉₊
        3 ≤ k ∧
        (k : ℝ) ≤ 2 * (Real.log (t : ℝ)) ^ (α / 3) ∧
        t₀ ≤ 14 * a ∧
        2 * (k : ℝ) ^ 2 ≤ (Real.log ((14 * a : ℕ) : ℝ)) ^ α := by
  have hβ : 0 < α / 3 := by positivity
  have htop : Tendsto
      (fun t : ℕ => (Real.log (t : ℝ)) ^ (α / 3)) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (htop.eventually_ge_atTop (max 3 (8 * (2 : ℝ) ^ α)))
  refine ⟨max N (max 3 (t₀ * t₀)), by omega, ?_⟩
  intro t T a ht htT ha _
  dsimp
  let x : ℝ := Real.log (t : ℝ)
  let y : ℝ := x ^ (α / 3)
  let k : ℕ := ⌈y⌉₊
  have hybig : max (3 : ℝ) (8 * (2 : ℝ) ^ α) ≤ y :=
    hN t ((Nat.le_max_left _ _).trans ht)
  have hy3 : (3 : ℝ) ≤ y := (le_max_left _ _).trans hybig
  have hycoef : 8 * (2 : ℝ) ^ α ≤ y := (le_max_right _ _).trans hybig
  have ht3 : 3 ≤ t := by omega
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hxpos : 0 < x := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
  have hypos : 0 < y := Real.rpow_pos_of_pos hxpos _
  have hk3real : (3 : ℝ) ≤ (k : ℝ) :=
    hy3.trans (Nat.le_ceil y)
  have hk3 : 3 ≤ k := by exact_mod_cast hk3real
  have hkupper : (k : ℝ) ≤ 2 * y :=
    Nat.ceil_le_two_mul (by norm_num; linarith)
  have htsq : t₀ ^ 2 ≤ t := by
    have h₁ : t₀ * t₀ ≤ max N (max 3 (t₀ * t₀)) :=
      (Nat.le_max_right 3 (t₀ * t₀)).trans
        (Nat.le_max_right N (max 3 (t₀ * t₀)))
    simpa only [pow_two] using h₁.trans ht
  have ht₀sqrt : (t₀ : ℝ) ≤ Real.sqrt (t : ℝ) :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast htsq)
  have hT2 : 2 ≤ (T : ℝ) := by exact_mod_cast (by omega : 2 ≤ T)
  have htsqrt : Real.sqrt (t : ℝ) ≤ Real.sqrt (T : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast htT)
  have ht₀a : t₀ ≤ a := by
    have hreal : (t₀ : ℝ) ≤ (a : ℝ) :=
      ht₀sqrt.trans (htsqrt.trans ((sqrt_le_dp_window hT2).trans ha.le))
    exact_mod_cast hreal
  have ht₀u : t₀ ≤ 14 * a := by omega
  have hloglower : x / 2 ≤ Real.log ((14 * a : ℕ) : ℝ) := by
    simpa [x, Nat.cast_mul] using
      (bootstrap_scale_log_lower (by omega : 2 ≤ t) htT ha)
  have hpoweq : x ^ α = y ^ 3 := by
    dsimp [y]
    calc
      x ^ α = x ^ ((α / 3) * 3) := by congr 1; ring
      _ = (x ^ (α / 3)) ^ 3 := by rw [Real.rpow_mul hxpos.le]; norm_num
  have hdenpos : 0 < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) _
  have hmid : 8 * y ^ 2 ≤ (x / 2) ^ α := by
    rw [Real.div_rpow hxpos.le (by norm_num) α, hpoweq]
    apply (le_div_iff₀ hdenpos).2
    have hmul := mul_le_mul_of_nonneg_right hycoef (sq_nonneg y)
    nlinarith
  have hk2 : (k : ℝ) ^ 2 ≤ (2 * y) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hkupper 2
  have hleft : 2 * (k : ℝ) ^ 2 ≤ 8 * y ^ 2 := by nlinarith
  have hright : (x / 2) ^ α ≤ (Real.log ((14 * a : ℕ) : ℝ)) ^ α :=
    Real.rpow_le_rpow (by positivity) hloglower hα.le
  exact ⟨hk3, hkupper, ht₀u, hleft.trans (hmid.trans hright)⟩

end HadwigerLean.Deduction
