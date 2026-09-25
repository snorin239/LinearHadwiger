import Mathlib.Tactic

/-!
# Numerical budgets for Corollary 24

The shared woven induction is specialized with connectivity coefficient
`10000`, hub coloring cost `980a`, separation cost `14da`, and outer
coloring coefficient `10^6(d+1)`. All inequalities below are exact
integer inequalities; no asymptotic constant is hidden.
-/

namespace HadwigerLean.Deduction

/-- The coefficient of the chromatic budget at each outer scale. -/
def cor24B (d : ℕ) : ℕ := 10 ^ 6 * (d + 1)

/-- The first GN threshold after the hub and double fan are removed. -/
theorem cor24_gn_first_budget (d a T : ℕ) :
    7 * 10000 * a + (14 + 28 + 980) * a ≤
      2000 * T + cor24B d * a := by
  have hc : 7 * 10000 + (14 + 28 + 980) ≤ cor24B d := by
    dsimp [cor24B]
    omega
  calc
    7 * 10000 * a + (14 + 28 + 980) * a =
        (7 * 10000 + (14 + 28 + 980)) * a := by ring
    _ ≤ cor24B d * a := Nat.mul_le_mul_right a hc
    _ ≤ 2000 * T + cor24B d * a := Nat.le_add_left _ _

/-- The second GN threshold, after deleting the inner roots and their
two neighbors and paying both separability losses. -/
theorem cor24_gn_second_budget (d a T : ℕ) :
    7 * 10000 * a +
      (14 + 28 + 3 + 980 + 12 * 10000) * a +
      2 * (14 * d * a) ≤ 2000 * T + cor24B d * a := by
  have hc : 7 * 10000 + (14 + 28 + 3 + 980 + 12 * 10000) +
      28 * d ≤ cor24B d := by
    dsimp [cor24B]
    omega
  calc
    7 * 10000 * a +
        (14 + 28 + 3 + 980 + 12 * 10000) * a +
        2 * (14 * d * a) =
        (7 * 10000 + (14 + 28 + 3 + 980 + 12 * 10000) +
          28 * d) * a := by ring
    _ ≤ cor24B d * a := Nat.mul_le_mul_right a hc
    _ ≤ 2000 * T + cor24B d * a := Nat.le_add_left _ _

/-- The two separability inputs remain strictly above twice the
separation cost at every positive scale. -/
theorem cor24_separation_budget (d a : ℕ) (ha : 0 < a) :
    (1025 + 6 * 10000 + 42 * d) * a < cor24B d * a := by
  have hc : 1025 + 6 * 10000 + 42 * d < cor24B d := by
    dsimp [cor24B]
    omega
  exact Nat.mul_lt_mul_of_pos_right hc ha

/-- The child scale receives enough coloring budget after all losses.
This is the boxed inequality (4.1) multiplied by three. -/
theorem cor24_child_budget (d a : ℕ) :
    3 * ((45 + 12 * 10000) * a + 980 * a +
      2 * (14 * d * a)) ≤ cor24B d * a := by
  have hc : 3 * (45 + 12 * 10000 + 980 + 28 * d) ≤ cor24B d := by
    dsimp [cor24B]
    omega
  calc
    3 * ((45 + 12 * 10000) * a + 980 * a +
        2 * (14 * d * a)) =
        (3 * (45 + 12 * 10000 + 980 + 28 * d)) * a := by ring
    _ ≤ cor24B d * a := Nat.mul_le_mul_right a hc

end HadwigerLean.Deduction