import Mathlib.Tactic

/-!
# Polynomial core budget for the CI stage invariant

The quadratic bound pays for one small piece per old block, the
knitting piece, and the new region tangencies at every stage.
-/

namespace HadwigerLean.Inseparability

def ciCoreBound (N x u : ℕ) : ℕ := 2 * u * u * (N + x)

@[simp] theorem ciCoreBound_zero (N x : ℕ) :
    ciCoreBound N x 0 = 0 := by
  simp [ciCoreBound]

theorem ciCoreBound_mono (N x u r : ℕ) (hur : u ≤ r) :
    ciCoreBound N x u ≤ ciCoreBound N x r := by
  unfold ciCoreBound
  calc
    2 * u * u * (N + x) = 2 * (u * u) * (N + x) := by ring
    _ ≤ 2 * (r * r) * (N + x) :=
      Nat.mul_le_mul_right (N + x)
        (Nat.mul_le_mul_left 2 (Nat.mul_self_le_mul_self hur))
    _ = 2 * r * r * (N + x) := by ring

theorem ciCoreBound_first (N x : ℕ) :
    N + x ≤ ciCoreBound N x 1 := by
  simp only [ciCoreBound, mul_one, one_mul]
  omega

theorem ciCoreBound_step (N x u : ℕ) :
    ciCoreBound N x u + u * N + N + (u + 1) * x ≤
      ciCoreBound N x (u + 1) := by
  unfold ciCoreBound
  nlinarith [Nat.zero_le (u * (N + x))]

theorem ciCoreBound_localWindow (N x r : ℕ) (hr : 0 < r) :
    r * N ≤ 3 * ciCoreBound N x r := by
  unfold ciCoreBound
  have hr1 : 1 ≤ r := hr
  nlinarith [Nat.zero_le (r * x), Nat.zero_le (r * N)]

end HadwigerLean.Inseparability

