import HadwigerLean.Woven.Uniform
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! The sharp-order zero-terminal case of the uniform woven statement. -/

namespace HadwigerLean.Woven

/-- A constant multiple of `a √(log a)` connectivity yields every rooted
`K_a` model, hence the zero-pair woven property. -/
theorem woven_zero_of_uniform_connectivity
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (a k : ℕ) (ha : 2 ≤ a)
    (hconn : VertexConnected G k)
    (hbudget : 1000 * (a : ℝ) * Real.sqrt (Real.log (a : ℝ)) ≤ (k : ℝ)) :
    Woven G a 0 := by
  classical
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hapos : (0 : ℝ) < a := by linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    nlinarith
  have hlogle : Real.log 2 ≤ Real.log (a : ℝ) :=
    Real.log_le_log (by norm_num) haR
  have hloga : (1 / 2 : ℝ) ≤ Real.log (a : ℝ) := hlog2.trans hlogle
  have hsqrtLow : (1 / 2 : ℝ) ≤ Real.sqrt (Real.log (a : ℝ)) := by
    have hs := Real.sq_sqrt (by linarith : 0 ≤ Real.log (a : ℝ))
    have hn := Real.sqrt_nonneg (Real.log (a : ℝ))
    nlinarith
  have hrootconn : a ≤ k := by
    have hprod : (a : ℝ) ≤
        1000 * (a : ℝ) * Real.sqrt (Real.log (a : ℝ)) := by
      nlinarith
    exact_mod_cast (hprod.trans hbudget)
  have h2a : 2 * (a : ℝ) ≤ (a : ℝ) ^ 2 := by nlinarith
  have hlog2a : Real.log (2 * (a : ℝ)) ≤
      2 * Real.log (a : ℝ) := by
    calc
      Real.log (2 * (a : ℝ)) ≤ Real.log ((a : ℝ) ^ 2) :=
        Real.log_le_log (by positivity) h2a
      _ = 2 * Real.log (a : ℝ) := by rw [Real.log_pow]; ring
  have hsqrtUpper : Real.sqrt (Real.log (2 * (a : ℝ))) ≤
      2 * Real.sqrt (Real.log (a : ℝ)) := by
    have hle := Real.sqrt_le_sqrt hlog2a
    have hright : Real.sqrt (2 * Real.log (a : ℝ)) ≤
        2 * Real.sqrt (Real.log (a : ℝ)) := by
      have hsq : (Real.sqrt (2 * Real.log (a : ℝ))) ^ 2 ≤
          (2 * Real.sqrt (Real.log (a : ℝ))) ^ 2 := by
        rw [Real.sq_sqrt (by linarith : 0 ≤ 2 * Real.log (a : ℝ)),
          mul_pow, Real.sq_sqrt (by linarith : 0 ≤ Real.log (a : ℝ))]
        nlinarith
      nlinarith [Real.sqrt_nonneg (2 * Real.log (a : ℝ))]
    exact hle.trans hright
  have hKT : 60 * (a : ℝ) * Real.sqrt (Real.log (2 * (a : ℝ))) ≤
      (k : ℝ) / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hsqrtUpper (by positivity : 0 ≤ (a : ℝ))
    nlinarith
  apply Woven.of_rooted_minor_zero
  intro root hroot
  have haCard : 1 ≤ Fintype.card (Fin a) := by simpa using (show 1 ≤ a by omega)
  have hconnCard : Fintype.card (Fin a) ≤ k := by simpa using hrootconn
  have h := RootedDensity.rootedMinor_of_connected_clique_threshold
    (SimpleGraph.completeGraph (Fin a)) G haCard k hconn hconnCard
    (by simpa only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] using hKT)
    root hroot
  exact h

end HadwigerLean.Woven

