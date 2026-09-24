import Mathlib.Tactic

/-!
# Finite loss recurrence

A generic deterministic estimate for the expected survivor count, normalized
degree deficit, and waste in a sequence of matching rounds.
-/

namespace HadwigerLean.Theorem2

/-- Sum the three one-step estimates used by the almost-perfect matching
iteration. The quadratic error term is deliberately loose; the final proof
has ample slack and does not need a finite arithmetic-series identity. -/
theorem finite_loss_recurrence
    (T : ℕ) (n z w : ℕ → ℝ) (N q a δ β : ℝ)
    (hN : 0 ≤ N) (hq : 0 ≤ q) (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hn0 : n 0 ≤ N)
    (hnstep : ∀ i < T, n (i + 1) ≤ q * n i)
    (hzstep : ∀ i < T, z (i + 1) ≤ z i + δ * N)
    (hwstep : ∀ i < T, w i ≤ a * z i + β * N) :
    n T + ∑ i ∈ Finset.range T, w i ≤
      q ^ T * N + a * (T : ℝ) * z 0 +
        (a * δ * (T : ℝ) ^ 2 + β * (T : ℝ)) * N := by
  have hn : ∀ i ≤ T, n i ≤ q ^ i * N := by
    intro i hi
    induction i with
    | zero => simpa using hn0
    | succ i ih =>
        have hiT : i < T := by omega
        calc
          n (i + 1) ≤ q * n i := hnstep i hiT
          _ ≤ q * (q ^ i * N) :=
            mul_le_mul_of_nonneg_left (ih (by omega)) hq
          _ = q ^ (i + 1) * N := by rw [pow_succ]; ring
  have hz : ∀ i ≤ T, z i ≤ z 0 + (i : ℝ) * δ * N := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
        have hiT : i < T := by omega
        calc
          z (i + 1) ≤ z i + δ * N := hzstep i hiT
          _ ≤ (z 0 + (i : ℝ) * δ * N) + δ * N :=
            by linarith [ih (by omega)]
          _ = z 0 + (i + 1 : ℕ) * δ * N := by push_cast; ring
  have hδN : 0 ≤ δ * N := mul_nonneg hδ hN
  have hsum :
      (∑ i ∈ Finset.range T, w i) ≤
        (T : ℝ) * (a * z 0 + (a * δ * (T : ℝ) + β) * N) := by
    calc
      (∑ i ∈ Finset.range T, w i) ≤
          ∑ _i ∈ Finset.range T,
            (a * z 0 + (a * δ * (T : ℝ) + β) * N) := by
        apply Finset.sum_le_sum
        intro i hi
        have hiT : i < T := Finset.mem_range.mp hi
        have hicast : (i : ℝ) ≤ (T : ℝ) := by exact_mod_cast hiT.le
        have hzi : z i ≤ z 0 + (T : ℝ) * δ * N := by
          have hscale := mul_le_mul_of_nonneg_right hicast hδN
          have hzi0 := hz i hiT.le
          nlinarith [hscale, hzi0]
        calc
          w i ≤ a * z i + β * N := hwstep i hiT
          _ ≤ a * (z 0 + (T : ℝ) * δ * N) + β * N :=
            by linarith [mul_le_mul_of_nonneg_left hzi ha]
          _ = a * z 0 + (a * δ * (T : ℝ) + β) * N := by ring
      _ = (T : ℝ) * (a * z 0 + (a * δ * (T : ℝ) + β) * N) := by
        simp [nsmul_eq_mul]
        ring
  calc
    n T + ∑ i ∈ Finset.range T, w i ≤
        q ^ T * N +
          (T : ℝ) * (a * z 0 + (a * δ * (T : ℝ) + β) * N) :=
      add_le_add (hn T le_rfl) hsum
    _ = q ^ T * N + a * (T : ℝ) * z 0 +
          (a * δ * (T : ℝ) ^ 2 + β * (T : ℝ)) * N := by ring

end HadwigerLean.Theorem2