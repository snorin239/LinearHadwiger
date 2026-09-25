import HadwigerLean.Graph.CliqueDensity.Theorem
import HadwigerLean.Graph.DensityBasic
import Mathlib.Tactic

/-!
# The coefficient-30 density upper bound for minor-free graphs
-/

namespace HadwigerLean

universe u

theorem minor_free_edgeCount_le_kt
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : ℕ) (ht : 2 ≤ t) (hminor : ¬ HasCliqueMinor G t) :
    (edgeCount G : ℝ) ≤
      30 * (t : ℝ) * Real.sqrt (Real.log (t : ℝ)) *
        (Fintype.card V : ℝ) := by
  classical
  by_cases hcard : 0 < Fintype.card V
  · have hden : edgeDensity G <
        30 * (t : ℝ) * Real.sqrt (Real.log (t : ℝ)) := by
      by_contra h
      exact hminor (hasCliqueMinor_of_edgeDensity_ge G t ht
        (le_of_not_gt h))
    have hcardR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hcard
    have h := mul_lt_mul_of_pos_right hden hcardR
    rw [edgeDensity, div_mul_cancel₀ _ hcardR.ne'] at h
    exact h.le
  · have hzero : Fintype.card V = 0 := by omega
    have hbound : edgeCount G ≤ (Fintype.card V).choose 2 := by
      rw [edgeCount_eq_card_edgeFinset]
      exact G.card_edgeFinset_le_card_choose_two
    have hedge : edgeCount G = 0 := by simpa [hzero] using hbound
    simp [hedge, hzero]

/-- The global density assumption in Section 8 implies the auxiliary
inequality `k ≤ t√log t`. -/
theorem density_forces_k_le_kt_scale
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t k : ℕ) (ht : 3 ≤ t) (hk : t ≤ k)
    (hminor : ¬ HasCliqueMinor G t)
    (hcard : 0 < Fintype.card V)
    (hdense : 480 * 6400 * k * Fintype.card V ≤ edgeCount G) :
    (k : ℝ) ≤ (t : ℝ) * Real.sqrt (Real.log (t : ℝ)) := by
  have hden : (480 * 6400 * (k : ℝ)) ≤ edgeDensity G := by
    have hcardR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hcard
    have hnat : (480 * 6400 * (k : ℝ)) * (Fintype.card V : ℝ) ≤
        (edgeCount G : ℝ) := by exact_mod_cast hdense
    apply (le_div_iff₀ hcardR).mpr
    simpa [edgeDensity] using hnat
  have hupper : edgeDensity G <
      30 * (t : ℝ) * Real.sqrt (Real.log (t : ℝ)) := by
    by_contra h
    exact hminor (hasCliqueMinor_of_edgeDensity_ge G t (by omega)
      (le_of_not_gt h))
  have hroot : 0 ≤ Real.sqrt (Real.log (t : ℝ)) := Real.sqrt_nonneg _
  have htR : 0 ≤ (t : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg htR hroot]

end HadwigerLean
