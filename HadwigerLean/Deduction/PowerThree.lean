import HadwigerLean.Bootstrap.Definitions
import Mathlib.Data.Nat.Log

/-! The least power of three above a given clique-minor order. -/

namespace HadwigerLean.Deduction

open HadwigerLean.Bootstrap

/-- The least power of three at least `t` is `3 ^ clog 3 t`. -/
theorem least_power_of_three_spec (t : ℕ) :
    IsLeastPowerOfThreeAtLeast t (3 ^ Nat.clog 3 t) := by
  refine ⟨⟨Nat.clog 3 t, rfl⟩, Nat.le_pow_clog (by decide) t, ?_⟩
  intro U hpow htU
  obtain ⟨m, rfl⟩ := hpow
  have hm : Nat.clog 3 t ≤ m :=
    (Nat.clog_le_iff_le_pow (by decide)).mpr htU
  exact Nat.pow_le_pow_right (by decide) hm

/-- For `t ≥ 2`, the least power of three above `t` is strictly below `3t`. -/
theorem least_power_of_three_lt_three_mul {t T : ℕ}
    (ht : 2 ≤ t) (hT : IsLeastPowerOfThreeAtLeast t T) : T < 3 * t := by
  obtain ⟨⟨m, rfl⟩, hle, hminimal⟩ := hT
  have hmpos : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    simp [hm0] at hle
    omega
  have hpred : 3 ^ m.pred < t := by
    by_contra h
    have ht : t ≤ 3 ^ m.pred := by omega
    have h := hminimal (3 ^ m.pred) ⟨m.pred, rfl⟩ ht
    have hp : m ≤ m.pred :=
      (Nat.pow_le_pow_iff_right (by decide)).mp h
    have hpredlt : m.pred < m := Nat.pred_lt hmpos.ne'
    omega
  have hm : m = m.pred + 1 := by
    simpa only [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hmpos).symm
  calc
    3 ^ m = 3 ^ (m.pred + 1) := congrArg (3 ^ ·) hm
    _ = 3 ^ m.pred * 3 := pow_succ 3 m.pred
    _ < t * 3 := Nat.mul_lt_mul_of_pos_right hpred (by decide)
    _ = 3 * t := by omega

end HadwigerLean.Deduction
