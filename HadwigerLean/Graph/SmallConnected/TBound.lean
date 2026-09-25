import HadwigerLean.Graph.SmallConnected.YBound
import HadwigerLean.Graph.SmallConnected.ZBound
import Mathlib.Tactic

/-!
# Numerical assembly of the exceptional-set bound
-/

namespace HadwigerLean

/-- Equation (8.5) after clearing the positive factor `k²`. -/
theorem exceptional_set_numerical_bound
    (x y z N t k L : ℝ)
    (hx0 : 0 ≤ x) (hL : 0 ≤ L) (hk : 0 < k)
    (hKT : k^2 ≤ t^2 * L)
    (hpack : 10 * L^2 * t^2 * x ≤ N * k^2)
    (hY : k^2 * y ≤ t^2 * L * x)
    (hZ : 10 * L * z ≤ N) :
    10 * L * (x + y + z) ≤ 3 * N := by
  have hk2 : 0 < k^2 := sq_pos_of_pos hk
  have hLx : 0 ≤ 10 * L * x := by positivity
  have hLy : 0 ≤ 10 * L := by positivity
  have hxmul : (10 * L * x) * k^2 ≤ N * k^2 := by
    calc
      (10 * L * x) * k^2 ≤
          (10 * L * x) * (t^2 * L) :=
            mul_le_mul_of_nonneg_left hKT hLx
      _ = 10 * L^2 * t^2 * x := by ring
      _ ≤ N * k^2 := hpack
  have hX : 10 * L * x ≤ N :=
    (mul_le_mul_iff_of_pos_right hk2).mp hxmul
  have hymul : (10 * L * y) * k^2 ≤ N * k^2 := by
    calc
      (10 * L * y) * k^2 =
          (10 * L) * (k^2 * y) := by ring
      _ ≤ (10 * L) * (t^2 * L * x) :=
        mul_le_mul_of_nonneg_left hY hLy
      _ = 10 * L^2 * t^2 * x := by ring
      _ ≤ N * k^2 := hpack
  have hY' : 10 * L * y ≤ N :=
    (mul_le_mul_iff_of_pos_right hk2).mp hymul
  linarith

end HadwigerLean
