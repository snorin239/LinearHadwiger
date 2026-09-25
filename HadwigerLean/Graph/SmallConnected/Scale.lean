import HadwigerLean.Graph.SmallConnected.ExceptionalSets
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Choosing the connected-block size
-/

namespace HadwigerLean

noncomputable def smallConnectedBlockSize (t k : ℕ) : ℕ :=
  Nat.ceil (10 * (Real.log (t : ℝ))^2 * (t : ℝ)^2 / (k : ℝ)^2) + 1

/-- The block size is large enough for the packing exceptional-set estimate. -/
theorem smallConnectedBlockSize_lower
    (t k : ℕ) (hk : 0 < k) :
    10 * (Real.log (t : ℝ))^2 * (t : ℝ)^2 ≤
      ((smallConnectedBlockSize t k - 1 : ℕ) : ℝ) * (k : ℝ)^2 := by
  let a : ℝ := 10 * (Real.log (t : ℝ))^2 * (t : ℝ)^2 / (k : ℝ)^2
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk2 : (0 : ℝ) < (k : ℝ)^2 := sq_pos_of_pos hkR
  have ha : a ≤ (Nat.ceil a : ℝ) := Nat.le_ceil a
  have hmul := mul_le_mul_of_nonneg_right ha hk2.le
  have hdef : smallConnectedBlockSize t k - 1 = Nat.ceil a := by
    simp [smallConnectedBlockSize, a]
  rw [hdef]
  dsimp [a] at hmul
  field_simp at hmul
  nlinarith

/-- A constant-factor upper bound on the chosen block size. -/
theorem smallConnectedBlockSize_upper
    (t k : ℕ) (ht : 3 ≤ t) (hk : 0 < k)
    (hKT : (k : ℝ)^2 ≤ (t : ℝ)^2 * Real.log (t : ℝ)) :
    (smallConnectedBlockSize t k : ℝ) * (k : ℝ)^2 ≤
      12 * (Real.log (t : ℝ))^2 * (t : ℝ)^2 := by
  let L : ℝ := Real.log (t : ℝ)
  let a : ℝ := 10 * L^2 * (t : ℝ)^2 / (k : ℝ)^2
  have hL : 1 ≤ L := by
    have h3 : (1 : ℝ) < Real.log 3 := by
      have h := Real.log_three_gt_d9
      norm_num at h ⊢
      linarith
    have htR : (3 : ℝ) ≤ t := by exact_mod_cast ht
    exact (le_of_lt h3).trans (Real.log_le_log (by norm_num) htR)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk2 : (0 : ℝ) < (k : ℝ)^2 := sq_pos_of_pos hkR
  have htR : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have ht2 : (0 : ℝ) < (t : ℝ)^2 := sq_pos_of_pos htR
  have hL2 : 0 ≤ L^2 := sq_nonneg L
  have hmul := mul_le_mul_of_nonneg_left hKT (by linarith : 0 ≤ 10 * L)
  have ha10 : 10 ≤ a := by
    apply (le_div_iff₀ hk2).mpr
    nlinarith [hmul]
  have hceil : (Nat.ceil a : ℝ) < a + 1 :=
    Nat.ceil_lt_add_one (by positivity : 0 ≤ a)
  have hsize : (smallConnectedBlockSize t k : ℝ) < a + 2 := by
    simp only [smallConnectedBlockSize, Nat.cast_add, Nat.cast_one]
    linarith
  have hupper : (smallConnectedBlockSize t k : ℝ) ≤ 12 * a / 10 := by
    linarith
  have hprod := mul_le_mul_of_nonneg_right hupper hk2.le
  dsimp [a] at hprod
  field_simp at hprod
  nlinarith

end HadwigerLean