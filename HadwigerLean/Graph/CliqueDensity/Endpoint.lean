import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Endpoint estimate for the coefficient-30 clique-minor density proof

The exposed sample bound has the form
  (m₀-b) exp(-s(δ₀-b)/(m₀-b)).
The two correlated order/degree cases imply a common algebraic estimate.
Using exp(x) ≥ 1+x directly bounds every intermediate deletion count.
-/

namespace HadwigerLean
namespace CliqueDensity

/-- A common form of the E.5 endpoint estimate. Both correlated cases
satisfy the order and degree hypotheses. -/
theorem endpoint_exponential_bound
    (d m₀ b s δ₀ : ℝ)
    (hd : 0 < d) (hb0 : 0 ≤ b) (hb : b ≤ d / 3)
    (hs : 7 ≤ s)
    (horder : 7 * d ≤ 16 * m₀)
    (hdegree : 2 * m₀ + d ≤ 5 * δ₀) :
    (m₀ - b) * Real.exp (-s * (δ₀ - b) / (m₀ - b)) ≤
      (m₀ - d / 3) * Real.exp (-2 * s / 5) := by
  let mstar : ℝ := m₀ - d / 3
  let m : ℝ := m₀ - b
  let t : ℝ := d / 3 - b
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hmstar : 0 < mstar := by
    dsimp [mstar]
    nlinarith
  have hm : 0 < m := by
    dsimp [m]
    nlinarith
  have hmsum : m = mstar + t := by
    dsimp [m, mstar, t]
    ring
  have hden : 2 * m + 3 * t ≤ 5 * (δ₀ - b) := by
    dsimp [m, t]
    nlinarith [hdegree]
  have hscale : 5 * m ≤ 3 * s * mstar := by
    have hsnon : 0 ≤ s - 7 := by linarith
    have hprod : 0 ≤ (s - 7) * mstar := mul_nonneg hsnon hmstar.le
    dsimp [m, mstar]
    nlinarith [horder, hprod]
  have hbase : (2 : ℝ) / 5 + 3 * t / (5 * m) ≤ (δ₀ - b) / m := by
    apply (le_div_iff₀ hm).2
    have heq : ((2 : ℝ) / 5 + 3 * t / (5 * m)) * m =
        (2 * m + 3 * t) / 5 := by
      field_simp
    rw [heq]
    linarith [hden]
  have hsnon : 0 ≤ s := by linarith
  have htm : t / mstar ≤ (3 * s * t) / (5 * m) := by
    apply (div_le_div_iff₀ hmstar (by positivity : 0 < 5 * m)).2
    have hprod := mul_le_mul_of_nonneg_right hscale ht
    nlinarith
  have hz : t / mstar ≤ s * ((δ₀ - b) / m - 2 / 5) := by
    calc
      t / mstar ≤ s * (3 * t / (5 * m)) := by
        convert htm using 1 <;> ring
      _ ≤ s * ((δ₀ - b) / m - 2 / 5) := by
        apply mul_le_mul_of_nonneg_left _ hsnon
        linarith [hbase]
  have hratio : m / mstar ≤
      Real.exp (s * ((δ₀ - b) / m - 2 / 5)) := by
    have heq : m / mstar = 1 + t / mstar := by
      rw [hmsum]
      field_simp
    rw [heq]
    have hlin := Real.add_one_le_exp (t / mstar)
    have hmono : Real.exp (t / mstar) ≤
        Real.exp (s * ((δ₀ - b) / m - 2 / 5)) :=
      Real.exp_le_exp.mpr hz
    linarith
  change m * Real.exp (-s * (δ₀ - b) / m) ≤
    mstar * Real.exp (-2 * s / 5)
  calc
    m * Real.exp (-s * (δ₀ - b) / m) =
        mstar * (m / mstar) * Real.exp (-s * (δ₀ - b) / m) := by
      field_simp
    _ ≤ mstar * Real.exp (s * ((δ₀ - b) / m - 2 / 5)) *
        Real.exp (-s * (δ₀ - b) / m) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio hmstar.le)
        (Real.exp_pos _).le
    _ = mstar * Real.exp (-2 * s / 5) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring

/-- E.5 in the high degree, order-at-most-2d case. -/
theorem endpoint_exponential_bound_caseI
    (d m₀ b s δ₀ : ℝ)
    (hd : 0 < d) (hmlo : d < m₀) (hmhi : m₀ ≤ 2 * d)
    (hδ : d ≤ δ₀) (hb0 : 0 ≤ b) (hb : b ≤ d / 3)
    (hs : 7 ≤ s) :
    (m₀ - b) * Real.exp (-s * (δ₀ - b) / (m₀ - b)) ≤
      (m₀ - d / 3) * Real.exp (-2 * s / 5) := by
  apply endpoint_exponential_bound d m₀ b s δ₀ hd hb0 hb hs
  · linarith
  · linarith

/-- E.5 in the smaller order, degree-at-least-2d/3 case. -/
theorem endpoint_exponential_bound_caseII
    (d m₀ b s δ₀ : ℝ)
    (hd : 0 < d) (hmlo : 2 * d / 3 < m₀) (hmhi : m₀ ≤ d)
    (hδ : 2 * d / 3 ≤ δ₀) (hb0 : 0 ≤ b) (hb : b ≤ d / 3)
    (hs : 7 ≤ s) :
    (m₀ - b) * Real.exp (-s * (δ₀ - b) / (m₀ - b)) ≤
      (m₀ - d / 3) * Real.exp (-2 * s / 5) := by
  apply endpoint_exponential_bound d m₀ b s δ₀ hd hb0 hb hs
  · linarith
  · linarith

end CliqueDensity
end HadwigerLean
