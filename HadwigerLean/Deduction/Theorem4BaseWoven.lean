import HadwigerLean.Deduction.Theorem4Base
import HadwigerLean.Woven.NormalizedBase
import HadwigerLean.Woven.OuterDeletion
import HadwigerLean.Graph.CliqueMinorOrder
import Mathlib.Tactic

/-! The low-scale branch of the Theorem 4 woven induction. -/

namespace HadwigerLean.Deduction

theorem theorem4_base_hasCliqueMinor
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (T a : ℕ) (hT : 3 ≤ T) (ha : 1 ≤ a)
    (hscale : (a : ℝ) ≤ (T : ℝ) / Real.sqrt (Real.log (T : ℝ)))
    (hχ : 2000 * T ≤ HadwigerLean.chromatic G) :
    HadwigerLean.HasCliqueMinor G (14 * a) := by
  classical
  by_contra hminor
  have hlt := theorem4_base_chromatic_lt G T a hT ha hscale hminor
  have hχR : 2000 * (T : ℝ) ≤ (HadwigerLean.chromatic G : ℝ) := by
    exact_mod_cast hχ
  exact (not_lt_of_ge hχR) hlt

theorem theorem4_base_woven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T D B a : ℕ)
    (hT : 3 ≤ T) (ha : 1 ≤ a)
    (hcut : (a : ℝ) ≤
      (T : ℝ) / Real.sqrt (Real.log (T : ℝ)))
    (hD : 2000 ≤ D) (hB : 7 ≤ B)
    (hconn : VertexConnected G (D * a))
    (hχ : D * T + B * a ≤ chromatic G) :
    HadwigerLean.Woven G a (3 * a) := by
  classical
  intro root hroot j hj P hP
  let N := G.induce (Woven.normalizedSet root P)
  have hχdel :=
    Woven.chromatic_le_normalized_add_seven G root P hj
  have hχN : 2000 * T ≤ chromatic N := by
    change chromatic G ≤ 7 * a + chromatic N at hχdel
    have hDmul : 2000 * T ≤ D * T := Nat.mul_le_mul_right T hD
    have hBmul : 7 * a ≤ B * a := Nat.mul_le_mul_right a hB
    omega
  have hminor : HasCliqueMinor N (14 * a) :=
    theorem4_base_hasCliqueMinor N T a hT ha hcut hχN
  have horder : 2 * (a + 2 * j) ≤ 14 * a := by omega
  have hsmall : HasCliqueMinor N (2 * (a + 2 * j)) :=
    hasCliqueMinor_of_le hminor horder
  have hbudget : 2 * (a + 2 * j) ≤ D * a := by
    have hDmul : 14 * a ≤ D * a :=
      Nat.mul_le_mul_right a (by omega : 14 ≤ D)
    omega
  exact Woven.exists_solution_of_ambient_normalized_minor
    G root P hroot hP hconn hbudget hsmall

end HadwigerLean.Deduction
