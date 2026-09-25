import Mathlib.Tactic

/-!
# Numerical surplus estimate for the global trimming step
-/

namespace HadwigerLean

theorem global_trimming_surplus_numerical
    (s q N t k L eS eT eCross eTotal : ℝ)
    (hs : 0 ≤ s) (hsN : s ≤ N) (hq : 0 ≤ q)
    (hN : 0 < N) (ht : 3 ≤ t) (htk : t ≤ k)
    (hL : 1 ≤ L) (hT : 10 * L * q ≤ 3 * N)
    (hcross : eCross ≤
      6400 * t * Real.sqrt L * Real.sqrt (s * q) +
        (t - 2) * (s + q))
    (hinsideT : eT ≤ 30 * t * Real.sqrt L * q)
    (hbalance : eTotal = eS + eT + eCross)
    (hretained : (9 / 10) * (480 * 6400 * k) * N ≤ eTotal) :
    (4 / 5) * (480 * 6400 * k) * s + eCross < eS := by
  have hL0 : 0 ≤ L := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hqN : q ≤ N := by nlinarith [hT, mul_nonneg (sub_nonneg.mpr hL) hq]
  have hNs : N * s ≤ N * N :=
    mul_le_mul_of_nonneg_left hsN hN.le
  have hTprod : (10 * L * q) * s ≤ (3 * N) * s :=
    mul_le_mul_of_nonneg_right hT hs
  have hLprod : L * (s * q) ≤ N^2 := by
    nlinarith [hNs, hTprod]
  have hrootbound : Real.sqrt L * Real.sqrt (s * q) ≤ N := by
    rw [← Real.sqrt_mul hL0]
    exact Real.sqrt_le_iff.mpr ⟨hN.le, hLprod⟩
  have hrootL : Real.sqrt L ≤ L := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact hL0
    · nlinarith
  have hterm : (t - 2) * (s + q) ≤ 2 * t * N := by
    have hsq : s + q ≤ 2 * N := by linarith
    have htnonneg : 0 ≤ t - 2 := by linarith
    have h1 := mul_le_mul_of_nonneg_left hsq htnonneg
    have h2 := mul_le_mul_of_nonneg_right (by linarith : t - 2 ≤ t)
      (by linarith : 0 ≤ 2 * N)
    nlinarith
  have hcross' : eCross ≤ 2 * 6400 * t * N := by
    have hmain := mul_le_mul_of_nonneg_left hrootbound
      (by positivity : 0 ≤ 6400 * t)
    nlinarith [hcross, hmain, hterm]
  have hT' : 30 * t * Real.sqrt L * q ≤ 9 * t * N := by
    have hrootq := mul_le_mul_of_nonneg_right hrootL hq
    have hq' := mul_le_mul_of_nonneg_left hT
      (by positivity : 0 ≤ 3 * t)
    nlinarith [hrootq, hq']
  have hinsideT' : eT ≤ 9 * t * N :=
    hinsideT.trans hT'
  have htkN := mul_le_mul_of_nonneg_right htk hN.le
  have hcrosssmall : eCross < (1 / 20) * (480 * 6400 * k) * N := by
    nlinarith [hcross', htkN]
  have hsmall : eT + eCross <
      (1 / 20) * (480 * 6400 * k) * N := by
    nlinarith [hinsideT', hcross', htkN]
  nlinarith [mul_le_mul_of_nonneg_left hsN
    (by positivity : 0 ≤ (4 / 5 : ℝ) * (480 * 6400 * k))]

end HadwigerLean
