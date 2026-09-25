import HadwigerLean.Woven.CommonLemmas

/-!
# Integer scales for the shared woven induction

With top scale `3^m`, the integer scales are `2^i * 3^(m-i)` for
`0 ≤ i ≤ m`. Successive scales satisfy `3 * child = 2 * parent`, so
the pair budget of the child is exactly twice the parent scale.
-/

namespace HadwigerLean

namespace Woven

/-- The `i`th integer scale below `3^m`. -/
def outerScale (m i : ℕ) : ℕ := 2 ^ i * 3 ^ (m - i)

@[simp] theorem outerScale_zero (m : ℕ) : outerScale m 0 = 3 ^ m := by
  simp [outerScale]

@[simp] theorem outerScale_last (m : ℕ) : outerScale m m = 2 ^ m := by
  simp [outerScale]

theorem outerScale_pos (m i : ℕ) : 0 < outerScale m i := by
  simp [outerScale]

/-- The exact integer child recurrence, with no rounding loss. -/
theorem outerScale_child (m i : ℕ) (hi : i < m) :
    3 * outerScale m (i + 1) = 2 * outerScale m i := by
  have hsub : m - i = (m - (i + 1)) + 1 := by omega
  simp only [outerScale, pow_succ]
  rw [hsub]
  simp only [pow_succ]
  ac_rfl

/-- The child at a nonfinal scale is smaller than its parent. -/
theorem outerScale_child_lt (m i : ℕ) (hi : i < m) :
    outerScale m (i + 1) < outerScale m i := by
  have hp := outerScale_pos m i
  have hc := outerScale_child m i hi
  omega

/-- The next scale's threefold path budget is the current scale's
twofold budget. -/
theorem outerScale_child_pair_budget (m i : ℕ) (hi : i < m) :
    3 * outerScale m (i + 1) = 2 * outerScale m i :=
  outerScale_child m i hi

end Woven

end HadwigerLean
