import HadwigerLean.Woven.OuterBudget
import Mathlib.Tactic

/-! Integer budgets for the Theorem 4 outer induction. -/

namespace HadwigerLean.Deduction

/-- Round the real extremal ratio upward to pay integer separation costs. -/
noncomputable def theorem4RatioCeil (f : ℝ) : ℕ := ⌈f⌉₊

def theorem4B (D s : ℕ) : ℕ := 276 * D * (1 + s)

def theorem4Sigma (D s a : ℕ) : ℕ := 14 * D * (1 + s) * a

theorem theorem4_ratio_le_ceil (f : ℝ) :
    f ≤ (theorem4RatioCeil f : ℝ) := by
  exact Nat.le_ceil f

theorem theorem4_ratio_ceil_lt_add_one (f : ℝ) (hf : 0 ≤ f) :
    (theorem4RatioCeil f : ℝ) < f + 1 := by
  exact Nat.ceil_lt_add_one hf

theorem theorem4_B_ge (D s : ℕ) (hD : 2000 ≤ D) :
    994 ≤ theorem4B D s := by
  dsimp [theorem4B]
  have h1 : 1 ≤ 1 + s := by omega
  have hmul := Nat.mul_le_mul_left (276 * D) h1
  nlinarith

theorem theorem4_child_budget (D s a : ℕ) (hD : 2000 ≤ D) :
    3 * Woven.outerChildLoss a D (980 * a) (theorem4Sigma D s a) ≤
      theorem4B D s * a := by
  have hc : 3 * (1025 + 12 * D + 28 * D * (1 + s)) ≤
      276 * D * (1 + s) := by
    have hbase : 3075 ≤ 156 * D := by omega
    nlinarith
  have hmul := Nat.mul_le_mul_right a hc
  dsimp [Woven.outerChildLoss, theorem4Sigma, theorem4B]
  nlinarith

theorem theorem4_outer_gn_budget
    (m i T D s : ℕ) (hi : i < m) (hD : 2000 ≤ D) :
    D * Woven.outerScale m i ≤
      D * T + theorem4B D s * Woven.outerScale m (i + 1) := by
  let a := Woven.outerScale m i
  let c := Woven.outerScale m (i + 1)
  have hs : 3 * c = 2 * a := Woven.outerScale_child m i hi
  have hBa : 2 * D * a ≤ theorem4B D s * a := by
    have hc : 2 * D ≤ theorem4B D s := by
      dsimp [theorem4B]
      have hh : 1 ≤ 1 + s := by omega
      have hmul := Nat.mul_le_mul_left (276 * D) hh
      omega
    exact Nat.mul_le_mul_right a hc
  have hscale : 3 * (theorem4B D s * c) = 2 * (theorem4B D s * a) := by
    calc
      3 * (theorem4B D s * c) = theorem4B D s * (3 * c) := by ring
      _ = theorem4B D s * (2 * a) := by rw [hs]
      _ = 2 * (theorem4B D s * a) := by ring
  change D * a ≤ D * T + theorem4B D s * c
  nlinarith [hBa, hscale]

theorem theorem4_outer_sep_budget
    (m i T D s : ℕ) (hi : i < m) (hD : 2000 ≤ D) :
    theorem4Sigma D s (Woven.outerScale m i) <
      D * T + theorem4B D s * Woven.outerScale m (i + 1) +
        6 * (D * Woven.outerScale m i) := by
  let a := Woven.outerScale m i
  let c := Woven.outerScale m (i + 1)
  have hs : 3 * c = 2 * a := Woven.outerScale_child m i hi
  have hc : 0 < c := Woven.outerScale_pos m (i + 1)
  have hBa : 21 * D * (1 + s) * a ≤ theorem4B D s * a := by
    have hcoef : 21 * D * (1 + s) ≤ theorem4B D s := by
      dsimp [theorem4B]
      have hh := Nat.mul_le_mul_right (D * (1 + s)) (by omega : 21 ≤ 276)
      nlinarith
    exact Nat.mul_le_mul_right a hcoef
  have hscale : 3 * (theorem4B D s * c) = 2 * (theorem4B D s * a) := by
    calc
      3 * (theorem4B D s * c) = theorem4B D s * (3 * c) := by ring
      _ = theorem4B D s * (2 * a) := by rw [hs]
      _ = 2 * (theorem4B D s * a) := by ring
  have hBc : 0 < theorem4B D s * c :=
    Nat.mul_pos (by have hh := theorem4_B_ge D s hD; omega) hc
  have hσ : theorem4Sigma D s a ≤ theorem4B D s * c := by
    dsimp [theorem4Sigma]
    nlinarith [hBa, hscale]
  change theorem4Sigma D s a < D * T + theorem4B D s * c + 6 * (D * a)
  have ha : 0 < a := Woven.outerScale_pos m i
  have hDa : 0 < D * a := Nat.mul_pos (by omega) ha
  omega

end HadwigerLean.Deduction
