import HadwigerLean.Coloring.RobustFractional
import HadwigerLean.Quantitative.Constants

/-!
# Robust fractional bound for Theorem 2

This module instantiates the finite greedy weighted-matching bound at the
parameters used by the quantitative theorem.
-/

namespace HadwigerLean.Theorem2

universe u

/-- The robust fractional-coloring input to the bounded-independence and
quantitative Theorem 2 arguments, with its full quantification over induced
residual vertex types. -/
theorem robust_fractional_bound_at_theorem2_parameters
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H F : SimpleGraph W),
      independenceNumber H ≤ m ε →
      F ≤ Hᶜ →
      (letI : DecidableRel F.Adj := Classical.decRel F.Adj
       F.maxDegree) ≤ d ε →
      fractionalChromaticNumber (H ⊔ F) ≤
        4 * (cliqueMinorNumber H : ℝ) +
          (robustAdditive ε : ℝ) := by
  intro W _ _ H F hα hF hdegree
  classical
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  letI : DecidableRel F.Adj := Classical.decRel F.Adj
  have hm : 1 ≤ m ε := (by decide : 1 ≤ 2).trans (m_ge_two hε hε1)
  have hdeg : F.maxDegree ≤ d ε := hdegree
  have hmain := robust_fractional_bound_maxDegree H F hF (m ε) (d ε)
    hm hα hdeg
  have hconstant : (robustAdditive ε : ℝ) =
      2 * ((m ε *
        ((∑ j ∈ Finset.range (2 * m ε), (d ε + 1) ^ j) + 1) : ℕ) : ℝ) := by
    simp only [robustAdditive, Nat.cast_mul]
    ring_nf
  rw [hconstant]
  exact hmain

end HadwigerLean.Theorem2