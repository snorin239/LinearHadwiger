import HadwigerLean.Deduction.Corollary24BaseBridge
import HadwigerLean.Deduction.Corollary24Numerics
import HadwigerLean.Woven.NormalizedBase
import HadwigerLean.Woven.OuterDeletion
import HadwigerLean.Graph.CliqueMinorOrder
import Mathlib.Tactic

/-!
# Wovenness at every Corollary 24 base scale

All scales below the logarithmic cutoff use the normalized clique-minor
branch, not just the last integer scale.
-/

namespace HadwigerLean.Deduction

theorem cor24_base_woven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T d a : ℕ)
    (hT : 100 ≤ T) (ha : 1 ≤ a)
    (hcut : (a : ℝ) ≤
      (T : ℝ) / Real.sqrt (Real.log (T : ℝ)))
    (hconn : VertexConnected G (10000 * a))
    (hχ : 2000 * T + cor24B d * a ≤ chromatic G) :
    HadwigerLean.Woven G a (3 * a) := by
  classical
  have hB : 7 ≤ cor24B d := by
    dsimp [cor24B]
    omega
  have hBa7 : 7 * a ≤ cor24B d * a :=
    Nat.mul_le_mul_right a hB
  intro root hroot j hj P hP
  let N := G.induce (Woven.normalizedSet root P)
  have hχdel :=
    Woven.chromatic_le_normalized_add_seven G root P hj
  have hχN : 2000 * T ≤ chromatic N := by
    change chromatic G ≤ 7 * a + chromatic N at hχdel
    omega
  have hminor : HasCliqueMinor N (14 * a) :=
    cor24_base_hasCliqueMinor N T a hT ha hcut hχN
  have horder : 2 * (a + 2 * j) ≤ 14 * a := by omega
  have hsmall : HasCliqueMinor N (2 * (a + 2 * j)) :=
    hasCliqueMinor_of_le hminor horder
  have hbudget : 2 * (a + 2 * j) ≤ 10000 * a := by omega
  exact Woven.exists_solution_of_ambient_normalized_minor
    G root P hroot hP hconn hbudget hsmall

end HadwigerLean.Deduction
