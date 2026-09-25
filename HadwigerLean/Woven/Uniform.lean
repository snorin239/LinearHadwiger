import HadwigerLean.Woven.UniformClique
import Mathlib.Tactic

/-! A complete-minor quantitative woven bound for all finite pair budgets. -/

namespace HadwigerLean.Woven

/-- A natural upper bound on the KT density needed for a complete minor
on every normalized role slot. -/
noncomputable def uniformCliqueQ (a b : ℕ) : ℕ :=
  (a + 2 * b) +
    ⌈30 * ((2 * (a + 2 * b) : ℕ) : ℝ) *
      Real.sqrt (Real.log ((2 * (a + 2 * b) : ℕ) : ℝ))⌉₊

/-- Connectivity sufficient for the complete-minor proof of wovenness. -/
noncomputable def uniformCliqueK (a b : ℕ) : ℕ :=
  (a + 2 * b) + 2 * uniformCliqueQ a b

/-- The normalized KT and KR construction gives wovenness for every
number of terminal pairs up to `b` under this explicit connectivity bound. -/
theorem woven_of_uniformCliqueK
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (a b : ℕ) (ha : 1 ≤ a)
    (hconn : VertexConnected G (uniformCliqueK a b)) :
    Woven G a b := by
  classical
  let R := a + 2 * b
  let t : ℝ := 30 * ((2 * R : ℕ) : ℝ) *
    Real.sqrt (Real.log ((2 * R : ℕ) : ℝ))
  let q := uniformCliqueQ a b
  have hceil : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
  have hq : t ≤ (q : ℝ) := by
    have hqdef : q = R + ⌈t⌉₊ := by rfl
    rw [hqdef, Nat.cast_add]
    have hR : (0 : ℝ) ≤ R := by positivity
    linarith
  apply woven_of_clique_threshold G a b (uniformCliqueK a b) q ha hconn
  · dsimp [uniformCliqueK, uniformCliqueQ, q]
    omega
  · dsimp [uniformCliqueK]
    omega
  · dsimp [uniformCliqueQ, q]
    omega
  · simpa [R, t] using hq

end HadwigerLean.Woven

