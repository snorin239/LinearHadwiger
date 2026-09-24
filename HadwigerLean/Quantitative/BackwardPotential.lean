import Mathlib.Tactic

/-!
# Backward potential coefficients for matching rounds

The potential weights are defined by elapsed rounds, then read backward
along a fixed finite horizon. This makes the one-round conditional
expectation estimate telescope without constructing a global sample space.
-/

namespace HadwigerLean.Theorem2

/-- Coefficient of the surviving-vertex count after `k` remaining rounds. -/
def potentialCoeff (q c β : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => q * potentialCoeff q c β k + c * (k : ℝ) + β


theorem potentialCoeff_nonneg (q c β : ℝ)
    (hq : 0 ≤ q) (hc : 0 ≤ c) (hβ : 0 ≤ β)
    (k : ℕ) : 0 ≤ potentialCoeff q c β k := by
  induction k with
  | zero => norm_num [potentialCoeff]
  | succ k ih =>
      simp only [potentialCoeff]
      positivity
theorem potentialCoeff_le (q c β : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : 0 ≤ c) (hβ : 0 ≤ β)
    (k : ℕ) :
    potentialCoeff q c β k ≤
      q ^ k + c * (k : ℝ) ^ 2 + β * (k : ℝ) := by
  induction k with
  | zero => simp [potentialCoeff]
  | succ k ih =>
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      have hpoly : 0 ≤ c * (k : ℝ) ^ 2 + β * (k : ℝ) := by positivity
      have hqpoly :
          q * (c * (k : ℝ) ^ 2 + β * (k : ℝ)) ≤
            c * (k : ℝ) ^ 2 + β * (k : ℝ) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hq1) hpoly]
      have hmul := mul_le_mul_of_nonneg_left ih hq0
      have hslack : 0 ≤ c * ((k : ℝ) + 1) := by positivity
      change q * potentialCoeff q c β k + c * (k : ℝ) + β ≤
        q ^ (k + 1) + c * ((k + 1 : ℕ) : ℝ) ^ 2 +
          β * ((k + 1 : ℕ) : ℝ)
      rw [pow_succ]
      push_cast
      nlinarith [hmul, hqpoly, hslack]

/-- Coefficient of the degree-deficit state at round `i` in a horizon `T`. -/
def lossPotentialB (a : ℝ) (T i : ℕ) : ℝ :=
  a * (T - i : ℕ)

/-- Coefficient of the survivor-count state at round `i`. -/
def lossPotentialA (q δ a β : ℝ) (T i : ℕ) : ℝ :=
  potentialCoeff q (δ * a) β (T - i)


theorem lossPotentialA_nonneg (q δ a β : ℝ)
    (hq : 0 ≤ q) (hδ : 0 ≤ δ) (ha : 0 ≤ a) (hβ : 0 ≤ β)
    (T i : ℕ) : 0 ≤ lossPotentialA q δ a β T i := by
  exact potentialCoeff_nonneg q (δ * a) β hq (mul_nonneg hδ ha) hβ _

theorem lossPotentialB_nonneg (a : ℝ) (ha : 0 ≤ a) (T i : ℕ) :
    0 ≤ lossPotentialB a T i := by
  unfold lossPotentialB
  positivity
theorem lossPotentialB_terminal (a : ℝ) (T : ℕ) :
    lossPotentialB a T T = 0 := by simp [lossPotentialB]

theorem lossPotentialA_terminal (q δ a β : ℝ) (T : ℕ) :
    lossPotentialA q δ a β T T = 1 := by
  simp [lossPotentialA, potentialCoeff]

theorem lossPotentialB_step (a : ℝ) {T i : ℕ} (hi : i < T) :
    lossPotentialB a T i = lossPotentialB a T (i + 1) + a := by
  have hsub : T - i = T - (i + 1) + 1 := by omega
  simp only [lossPotentialB, hsub, Nat.cast_add, Nat.cast_one]
  ring

theorem lossPotentialA_step (q δ a β : ℝ) {T i : ℕ} (hi : i < T) :
    lossPotentialA q δ a β T i =
      q * lossPotentialA q δ a β T (i + 1) +
        δ * lossPotentialB a T (i + 1) + β := by
  have hsub : T - i = T - (i + 1) + 1 := by omega
  simp only [lossPotentialA, lossPotentialB, hsub, potentialCoeff]
  ring

theorem lossPotentialA_zero_le (q δ a β : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hδ : 0 ≤ δ) (ha : 0 ≤ a) (hβ : 0 ≤ β)
    (T : ℕ) :
    lossPotentialA q δ a β T 0 ≤
      q ^ T + δ * a * (T : ℝ) ^ 2 + β * (T : ℝ) := by
  simpa [lossPotentialA, mul_assoc] using
    potentialCoeff_le q (δ * a) β hq0 hq1 (mul_nonneg hδ ha) hβ T

theorem lossPotentialB_zero (a : ℝ) (T : ℕ) :
    lossPotentialB a T 0 = a * (T : ℝ) := by
  simp [lossPotentialB]

end HadwigerLean.Theorem2