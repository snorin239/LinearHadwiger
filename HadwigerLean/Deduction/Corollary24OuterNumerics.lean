import HadwigerLean.Deduction.Corollary24Numerics
import HadwigerLean.Woven.OuterScales
import Mathlib.Tactic

/-!
# Remaining integer inequalities in the Corollary 24 outer recursion
-/

namespace HadwigerLean.Deduction

theorem cor24_outer_gn_budget
    (m i T d : ℕ) (hi : i < m) :
    10000 * Woven.outerScale m i ≤
      2000 * T + cor24B d * Woven.outerScale m (i + 1) := by
  let a := Woven.outerScale m i
  let c := Woven.outerScale m (i + 1)
  have hs : 3 * c = 2 * a := Woven.outerScale_child m i hi
  have hB : 15000 ≤ cor24B d := by
    dsimp [cor24B]
    omega
  have hBa : 15000 * a ≤ cor24B d * a :=
    Nat.mul_le_mul_right a hB
  have hscale : 3 * (cor24B d * c) = 2 * (cor24B d * a) := by
    calc
      3 * (cor24B d * c) = cor24B d * (3 * c) := by ring
      _ = cor24B d * (2 * a) := by rw [hs]
      _ = 2 * (cor24B d * a) := by ring
  change 10000 * a ≤ 2000 * T + cor24B d * c
  omega

theorem cor24_outer_sep_budget
    (m i T d : ℕ) (hi : i < m) :
    14 * d * Woven.outerScale m i <
      2000 * T + cor24B d * Woven.outerScale m (i + 1) +
        6 * (10000 * Woven.outerScale m i) := by
  let a := Woven.outerScale m i
  let c := Woven.outerScale m (i + 1)
  have hs : 3 * c = 2 * a := Woven.outerScale_child m i hi
  have ha : 0 < a := Woven.outerScale_pos m i
  have hc : 0 < c := Woven.outerScale_pos m (i + 1)
  have hB : 21 * d ≤ cor24B d := by
    dsimp [cor24B]
    omega
  have hBa : (21 * d) * a ≤ cor24B d * a :=
    Nat.mul_le_mul_right a hB
  have hscale : 3 * (cor24B d * c) = 2 * (cor24B d * a) := by
    calc
      3 * (cor24B d * c) = cor24B d * (3 * c) := by ring
      _ = cor24B d * (2 * a) := by rw [hs]
      _ = 2 * (cor24B d * a) := by ring
  have hBc : 0 < cor24B d * c :=
    Nat.mul_pos (by dsimp [cor24B]; omega) hc
  have hσ : 14 * d * a ≤ cor24B d * c := by
    nlinarith [hBa, hscale]
  change 14 * d * a < 2000 * T + cor24B d * c + 6 * (10000 * a)
  omega

end HadwigerLean.Deduction
