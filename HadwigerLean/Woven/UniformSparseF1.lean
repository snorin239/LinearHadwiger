import HadwigerLean.Woven.UniformSparseNumerics
import HadwigerLean.Graph.RootedDensity.F1AmbientReverse
import HadwigerLean.Graph.RootedDensity.TwoLabels
import Mathlib.Tactic

/-! Conditional sharp woven conclusion with F.a's two torso model
transports exposed as the only remaining structural inputs. -/

namespace HadwigerLean.RootedDensity

/-- The clique-plus-matching density threshold exceeds one for `a ≥ 2`. -/
theorem cliqueMatchingThreshold_gt_one
    (a b : ℕ) (ha : 2 ≤ a) :
    1 < cliqueMatchingThreshold a b := by
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    nlinarith
  have hlogle : Real.log 2 ≤ Real.log (a : ℝ) :=
    Real.log_le_log (by norm_num) haR
  have hloga : (1 / 2 : ℝ) ≤ Real.log (a : ℝ) := hlog2.trans hlogle
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt (Real.log (a : ℝ)) := by
    have hsq := Real.sq_sqrt (by linarith : 0 ≤ Real.log (a : ℝ))
    have hn := Real.sqrt_nonneg (Real.log (a : ℝ))
    nlinarith
  have hprod : (1 : ℝ) ≤
      (a : ℝ) * Real.sqrt (Real.log (a : ℝ)) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ (a : ℝ) - 2)
      (by linarith : 0 ≤ Real.sqrt (Real.log (a : ℝ)) - 1 / 2)]
  unfold cliqueMatchingThreshold
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  nlinarith

end HadwigerLean.RootedDensity

namespace HadwigerLean.Woven

open HadwigerLean.RootedDensity

universe u

/-- The sharp million-fold woven conclusion follows from the two F.a
torso model transports for every clique-plus-matching target used in the
induction. The lone two-label target uses connectivity directly. -/
theorem woven_of_torso_transports
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (a b K : ℕ) (ha : 2 ≤ a)
    (hconn : VertexConnected G K)
    (hK : 1000000 * cliqueMatchingScale a b ≤ (K : ℝ))
    (htransport : ∀ j ≤ b,
      ∀ B : BadMassedWitness.{u,0} (cliqueMatchingGraph a j)
        (12 * cliqueMatchingThreshold a j +
          5000 * (Fintype.card (CliqueMatchingLabels a j) : ℝ)),
        BadMassedTorsoTransports B) :
    Woven G a b := by
  apply woven_of_sharp_rooted_cliqueMatching G a b K ha hconn hK
  intro j hj
  by_cases htwo : Fintype.card (CliqueMatchingLabels a j) = 2
  · exact rootedDensity_of_target_card_two
      (cliqueMatchingGraph a j)
      (12 * cliqueMatchingThreshold a j +
        5000 * (Fintype.card (CliqueMatchingLabels a j) : ℝ)) htwo
  · have hh : 3 ≤ Fintype.card (CliqueMatchingLabels a j) := by
      rw [cliqueMatchingLabels_card] at htwo ⊢
      omega
    exact rootedDensity_of_torso_transports
      (cliqueMatchingGraph a j) (cliqueMatchingThreshold a j)
      (cliqueMatchingThreshold_gt_one a j ha)
      (densityForcesMinor_cliqueMatching a j ha) hh
      (htransport j hj)


/-- A uniform ambient-target reverse truncation principle for the
clique-plus-matching targets gives the exact sharp woven bound. -/
theorem woven_of_ambientReverse
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (a b K : ℕ) (ha : 2 ≤ a)
    (hconn : VertexConnected G K)
    (hK : 1000000 * cliqueMatchingScale a b ≤ (K : ℝ))
    (hreverse : ∀ j ≤ b,
      AmbientRigidReversePrinciple.{u,0} (cliqueMatchingGraph a j)) :
    Woven G a b := by
  apply woven_of_torso_transports G a b K ha hconn hK
  intro j hj B
  exact badMassedTorsoTransports_of_ambientReverse (hreverse j hj) B
end HadwigerLean.Woven
