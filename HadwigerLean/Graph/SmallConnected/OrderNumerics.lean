import HadwigerLean.Graph.SmallConnected.Scale
import HadwigerLean.Graph.SmallConnected.CardBound
import Mathlib.Tactic

/-!
# Final order arithmetic for the small connected witness
-/

namespace HadwigerLean

/-- The degree cap and the block-size cap yield the advertised order
constant. The proof keeps every factor explicit for later changes. -/
theorem small_connected_order_numerical
    (r h t k L : ℝ)
    (hr : 0 ≤ r) (hh : 0 ≤ h) (ht : 0 < t)
    (htk : t ≤ k) (hL : 0 ≤ L)
    (hdegree : r ≤ 20 * (480 * 6400 * k) * L * h)
    (hsize : h * k^2 ≤ 12 * L^2 * t^2) :
    r ≤ (480 * 6400)^2 * t * L^3 := by
  let C : ℝ := 480 * 6400
  have hk : 0 < k := lt_of_lt_of_le ht htk
  have hL3 : 0 ≤ L^3 := pow_nonneg hL _
  have ht2 : 0 ≤ t^2 := sq_nonneg t
  have h1 : r * k ≤ 240 * C * L^3 * t^2 := by
    calc
      r * k ≤ (20 * (C * k) * L * h) * k :=
        mul_le_mul_of_nonneg_right (by simpa [C] using hdegree) hk.le
      _ = (20 * C * L) * (h * k^2) := by ring
      _ ≤ (20 * C * L) * (12 * L^2 * t^2) :=
        mul_le_mul_of_nonneg_left hsize (by positivity)
      _ = 240 * C * L^3 * t^2 := by ring
  have hcoeff : 240 * C ≤ C^2 := by norm_num [C]
  have h2 : 240 * C * L^3 * t^2 ≤ C^2 * L^3 * (t * k) := by
    calc
      240 * C * L^3 * t^2 ≤ C^2 * L^3 * t^2 := by
        gcongr
      _ ≤ C^2 * L^3 * (t * k) := by
        have htk' : t * t ≤ t * k :=
          mul_le_mul_of_nonneg_left htk ht.le
        nlinarith [mul_nonneg (show 0 ≤ C^2 * L^3 by positivity)
          (sub_nonneg.mpr htk')]
  have h3 : r * k ≤ (C^2 * t * L^3) * k := by
    nlinarith [h1, h2]
  have h4 : r ≤ C^2 * t * L^3 :=
    (mul_le_mul_iff_of_pos_right hk).mp h3
  simpa [C] using h4

end HadwigerLean