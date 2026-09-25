import HadwigerLean.Graph.SmallConnected.CrossGraph
import Mathlib.Tactic

/-!
# Bound for quotient vertices with many neighbors in the packed set
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Equation (8.4), multiplied through by `k²`, under the lower incidence
threshold supplied by the definition of `Y`. -/
theorem high_cross_degree_card_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) (hdisj : Disjoint X Y)
    (t k : ℕ) (ht : 3 ≤ t) (htk : t ≤ k)
    (hminor : ¬ HasCliqueMinor G t)
    (hKT : (k : ℝ) ≤ (t : ℝ) * Real.sqrt (Real.log (t : ℝ)))
    (hdegree : ∀ y ∈ Y,
      3 * 6400 * (k : ℝ) ≤
        ((G.neighborFinset y ∩ X).card : ℝ)) :
    (k : ℝ)^2 * (Y.card : ℝ) ≤
      (t : ℝ)^2 * Real.log (t : ℝ) * (X.card : ℝ) := by
  classical
  let L : ℝ := Real.log (t : ℝ)
  let x : ℝ := X.card
  let y : ℝ := Y.card
  have htpos : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ t))
  have hx : 0 ≤ x := Nat.cast_nonneg _
  have hy : 0 ≤ y := Nat.cast_nonneg _
  have hroot : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hksq : (k : ℝ)^2 ≤ (t : ℝ)^2 * L := by
    have hsq := mul_self_le_mul_self hkpos.le hKT
    have hsqrt := Real.sq_sqrt hL
    nlinarith
  by_cases hsmall : Y.card ≤ X.card
  · have hyx : y ≤ x := by change (Y.card : ℝ) ≤ X.card; exact_mod_cast hsmall
    have hmul := mul_le_mul_of_nonneg_right hksq hx
    nlinarith
  · have hbig : X.card ≤ Y.card := by omega
    have hxy : x ≤ y := by change (X.card : ℝ) ≤ Y.card; exact_mod_cast hbig
    have hypos : 0 < y := by
      have : 0 < Y.card := by omega
      change (0 : ℝ) < (Y.card : ℝ)
      exact_mod_cast this
    have hNP := cross_edges_le_unbalanced_bound G Y X hdisj.symm t ht hminor
    have hsum : 3 * 6400 * (k : ℝ) * y ≤
        ∑ v ∈ Y, ((G.neighborFinset v ∩ X).card : ℝ) := by
      calc
        3 * 6400 * (k : ℝ) * y =
            ∑ v ∈ Y, 3 * 6400 * (k : ℝ) := by
              simp [y, mul_assoc, mul_comm, mul_left_comm]
        _ ≤ ∑ v ∈ Y, ((G.neighborFinset v ∩ X).card : ℝ) := by
          apply Finset.sum_le_sum
          intro v hv
          exact hdegree v hv
    have hsub : (((t - 2 : ℕ) : ℝ)) ≤ (k : ℝ) := by
      exact_mod_cast (by omega : t - 2 ≤ k)
    have hterm : ((t - 2 : ℕ) : ℝ) * (y + x) ≤
        2 * 6400 * (k : ℝ) * y := by
      have hsumxy : y + x ≤ 2 * y := by linarith
      have h1 := mul_le_mul_of_nonneg_left hsumxy
        (by exact_mod_cast (Nat.zero_le (t - 2)) : (0 : ℝ) ≤ (t - 2 : ℕ))
      have h2 := mul_le_mul_of_nonneg_right hsub (by linarith : 0 ≤ y + x)
      have h3 : 2 * (k : ℝ) * y ≤ 2 * 6400 * (k : ℝ) * y := by
        nlinarith [mul_nonneg hkpos.le hy]
      nlinarith
    have hrootxy : 0 ≤ Real.sqrt (y * x) := Real.sqrt_nonneg _
    have hmain : (k : ℝ) * y ≤
        (t : ℝ) * Real.sqrt L * Real.sqrt (y * x) := by
      change _ ≤ 6400 * ((t : ℝ) * Real.sqrt L) *
        Real.sqrt (y * x) + _ at hNP
      nlinarith [hNP, hsum, hterm]
    have hsq := mul_self_le_mul_self (mul_nonneg hkpos.le hy) hmain
    have hsqrtyx := Real.sq_sqrt (mul_nonneg hy hx)
    have hsqL := Real.sq_sqrt hL
    have hprod : ((k : ℝ)^2 * y) * y ≤
        ((t : ℝ)^2 * L * x) * y := by
      calc
        ((k : ℝ)^2 * y) * y =
            ((k : ℝ) * y) * ((k : ℝ) * y) := by ring
        _ ≤ ((t : ℝ) * Real.sqrt L * Real.sqrt (y * x)) *
            ((t : ℝ) * Real.sqrt L * Real.sqrt (y * x)) := hsq
        _ = (t : ℝ)^2 * (Real.sqrt L)^2 *
            (Real.sqrt (y * x))^2 := by ring
        _ = (t : ℝ)^2 * L * (y * x) := by rw [hsqL, hsqrtyx]
        _ = ((t : ℝ)^2 * L * x) * y := by ring
    exact (mul_le_mul_iff_of_pos_right hypos).mp hprod

end HadwigerLean
