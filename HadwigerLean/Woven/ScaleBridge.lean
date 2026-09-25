import HadwigerLean.Woven.OuterScales
import HadwigerLean.Bootstrap.Definitions
import Mathlib.Tactic

/-!
# The exact integer scales used by the outer induction

The paper's equation `3^i a = 2^i T` agrees exactly with the finite
sequence `2^i 3^(m-i)` when `T=3^m` and `i≤m`.
-/

namespace HadwigerLean
namespace Woven

open Bootstrap

/-- The defining equation for an indexed scale. -/
theorem outerScale_mul_identity (m i : ℕ) (hi : i ≤ m) :
    3 ^ i * outerScale m i = 2 ^ i * 3 ^ m := by
  have hsum : i + (m - i) = m := Nat.add_sub_of_le hi
  calc
    3 ^ i * outerScale m i = 2 ^ i * (3 ^ i * 3 ^ (m - i)) := by
      simp only [outerScale]
      ac_rfl
    _ = 2 ^ i * 3 ^ m := by rw [← pow_add, hsum]

/-- Every indexed scale in the finite recursion is an outer scale in
the endpoint theorem's definition. -/
theorem outerScale_isOuterScale (m i : ℕ) (hi : i ≤ m) :
    IsOuterScale (3 ^ m) (outerScale m i) :=
  ⟨i, outerScale_mul_identity m i hi⟩

/-- At an index within the finite recursion, the scale equation has
exactly the expected solution. -/
theorem outerScale_eq_of_isOuterScale_index (m i a : ℕ)
    (hi : i ≤ m) (h : 3 ^ i * a = 2 ^ i * 3 ^ m) :
    a = outerScale m i := by
  have hscale := outerScale_mul_identity m i hi
  have heq : 3 ^ i * a = 3 ^ i * outerScale m i :=
    h.trans hscale.symm
  exact mul_left_cancel₀ (by positivity) heq

/-- No later index can satisfy the integer outer-scale equation for a
power-of-three top scale. -/
theorem outerScale_index_le (m i a : ℕ)
    (h : 3 ^ i * a = 2 ^ i * 3 ^ m) : i ≤ m := by
  by_cases hi : i = 0
  · omega
  have hipos : 0 < i := Nat.pos_of_ne_zero hi
  have hcop : Nat.Coprime (3 ^ i) (2 ^ i) := by
    rw [Nat.coprime_pow_left_iff hipos, Nat.coprime_pow_right_iff hipos]
    norm_num
  have hdiv : 3 ^ i ∣ 2 ^ i * 3 ^ m := ⟨a, h.symm⟩
  have hpow : 3 ^ i ∣ 3 ^ m := (hcop.dvd_mul_left).mp hdiv
  exact (Nat.pow_dvd_pow_iff_le_right (by omega)).mp hpow

/-- Every integer outer scale of a power-of-three top scale belongs to
the finite sequence used in the downward induction. -/
theorem isOuterScale_iff_exists_index (m a : ℕ) :
    IsOuterScale (3 ^ m) a ↔
      ∃ i : ℕ, i ≤ m ∧ a = outerScale m i := by
  constructor
  · rintro ⟨i, hi⟩
    have him := outerScale_index_le m i a hi
    exact ⟨i, him, outerScale_eq_of_isOuterScale_index m i a him hi⟩
  · rintro ⟨i, hi, rfl⟩
    exact outerScale_isOuterScale m i hi

end Woven
end HadwigerLean