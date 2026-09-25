import HadwigerLean.Inseparability.ScaleCeilEstimates
import HadwigerLean.Inseparability.CINatBudgets
import Mathlib.Tactic

/-!
# The local chromatic window covers every CI core

The quadratic core budget at the last stage is small enough for the
local chromatic hypothesis with coefficient `ciCoefficient`.
-/

namespace HadwigerLean.Inseparability

noncomputable def ciPieceOrderBound (t : ℕ) : ℕ :=
  Nat.ceil (((480 * 6400 : ℝ)^2) * (t : ℝ) *
    (Real.log (t : ℝ))^3)

theorem ciPieceOrderBound_ge (t : ℕ) :
    (480 * 6400 : ℝ)^2 * (t : ℝ) *
      (Real.log (t : ℝ))^3 ≤ (ciPieceOrderBound t : ℝ) := by
  exact Nat.le_ceil _

private theorem ci_log_one_le (t : ℕ) (ht : 3 ≤ t) :
    (1 : ℝ) ≤ Real.log (t : ℝ) := by
  have h3 : Real.log (3 : ℝ) ≤ Real.log (t : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast ht)
  linarith [Real.log_three_gt_d9]

theorem ciCoreBound_local_window
    (t : ℕ) (ht : 3 ≤ t) :
    ((3 * ciCoreBound (ciPieceOrderBound t)
      (stageBlockSize t) (stageCount t) : ℕ) : ℝ) ≤
      (ciCoefficient : ℝ) * (t : ℝ) *
        (Real.log (t : ℝ))^4 := by
  let L : ℝ := Real.log (t : ℝ)
  let r : ℕ := stageCount t
  let x : ℕ := stageBlockSize t
  let N : ℕ := ciPieceOrderBound t
  let A : ℝ := (480 * 6400 : ℝ)^2
  have hL1 : 1 ≤ L := ci_log_one_le t ht
  have hL0 : 0 ≤ L := by linarith
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (by omega : 1 ≤ t)
  have hx : (x : ℝ) ≤ t := by
    exact_mod_cast stageBlockSize_le t ht
  have hr : (r : ℝ) ≤ 2 * Real.sqrt L := by
    simpa [r,L] using stageCount_le_two_sqrt_log t ht
  have hs0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hs2 : (Real.sqrt L)^2 = L := Real.sq_sqrt hL0
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hr2 : (r : ℝ)^2 ≤ 4 * L := by nlinarith
  have hNarg : 0 ≤ A * (t : ℝ) * L^3 := by
    dsimp [A]
    positivity
  have hNceil : (N : ℝ) < A * (t : ℝ) * L^3 + 1 := by
    simpa [N,ciPieceOrderBound,A,L] using
      Nat.ceil_lt_add_one hNarg
  have hNsum : (N : ℝ) + x ≤ A * (t : ℝ) * L^3 + 2 * t := by
    linarith
  have hNSum0 : 0 ≤ (N : ℝ) + x := by positivity
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hBound0 : 0 ≤ A * (t : ℝ) * L^3 + 2 * t := by positivity
  have hprod₁ := mul_le_mul_of_nonneg_right hr2 hNSum0
  have hprod₂ := mul_le_mul_of_nonneg_left hNsum (by positivity : 0 ≤ 4 * L)
  have hprod : 6 * (r : ℝ)^2 * ((N : ℝ) + x) ≤
      24 * L * (A * (t : ℝ) * L^3 + 2 * t) := by
    nlinarith [hprod₁,hprod₂]
  have hL2 : L ≤ L^2 := by nlinarith
  have hL3 : L^2 ≤ L^3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hL1) (sq_nonneg L)]
  have hL4 : L^3 ≤ L^4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hL1) (pow_nonneg hL0 3)]
  have hLto4 : L ≤ L^4 := le_trans hL2 (le_trans hL3 hL4)
  have hTL : (t : ℝ) * L ≤ (t : ℝ) * L^4 :=
    mul_le_mul_of_nonneg_left hLto4 (by positivity)
  have hconst :
      24 * L * (A * (t : ℝ) * L^3 + 2 * t) ≤
        (ciCoefficient : ℝ) * (t : ℝ) * L^4 := by
    dsimp [A,ciCoefficient]
    norm_num1
    nlinarith [hTL, mul_nonneg (show (0:ℝ) ≤ t by positivity)
      (show (0:ℝ) ≤ L^4 by positivity)]
  have hcast : ((3 * ciCoreBound N x r : ℕ) : ℝ) =
      6 * (r : ℝ)^2 * ((N : ℝ) + x) := by
    simp [ciCoreBound]
    ring
  change ((3 * ciCoreBound N x r : ℕ) : ℝ) ≤
    (ciCoefficient : ℝ) * (t : ℝ) * L^4
  rw [hcast]
  exact hprod.trans hconst

end HadwigerLean.Inseparability
