import HadwigerLean.Deduction.Theorem4BaseWoven
import HadwigerLean.Deduction.Theorem4HubContract
import HadwigerLean.Deduction.Theorem4Numerics
import HadwigerLean.Deduction.Corollary24Scale
import HadwigerLean.Deduction.Theorem4Scale
import HadwigerLean.Woven.OuterInductionMixed
import Mathlib.Tactic

/-! The shared outer woven induction with Theorem 4's integer budgets. -/

namespace HadwigerLean.Deduction

universe u

theorem theorem4_outerAt_top_of_sep_contracts
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m T D : ℕ) (hT : T = 3 ^ m) (hT3 : 3 ≤ T)
    (hD : 2000 ≤ D)
    (hsep : ∀ i, (hi : i < m) →
      (T : ℝ) / Real.sqrt (Real.log (T : ℝ)) <
        (Woven.outerScale m i : ℝ) →
      ∀ F : Finset V,
        Woven.OuterSepContract (G.induce (F : Set V))
          (Woven.outerScale m i)
          (theorem4Sigma D
            (theorem4RatioCeil (theorem4ScaleMaxRatio G D T))
            (Woven.outerScale m i))) :
    Woven.OuterAt G m 0 D (D * T)
      (theorem4B D (theorem4RatioCeil (theorem4ScaleMaxRatio G D T))) := by
  classical
  let s := theorem4RatioCeil (theorem4ScaleMaxRatio G D T)
  let B := theorem4B D s
  let cutoff : ℝ := (T : ℝ) / Real.sqrt (Real.log (T : ℝ))
  let hh : ℕ → ℕ := fun i => 980 * Woven.outerScale m i
  let ss : ℕ → ℕ := fun i => theorem4Sigma D s (Woven.outerScale m i)
  have hlast : (Woven.outerScale m m : ℝ) ≤ cutoff :=
    cor24_outerScale_last_le_top_div_sqrt_log m T hT hT3
  have hB : 7 ≤ B := by
    have hh := theorem4_B_ge D s hD
    omega
  have hbase : Woven.OuterAt G m m D (D * T) B := by
    intro F hconn hχ
    exact theorem4_base_woven (G.induce (F : Set V)) T D B
      (Woven.outerScale m m) hT3
      (Woven.outerScale_pos m m) hlast hD hB hconn hχ
  have hsmall : ∀ i, i < m →
      ¬ cutoff < (Woven.outerScale m i : ℝ) →
      Woven.OuterAt G m i D (D * T) B := by
    intro i hi hcut F hconn hχ
    exact theorem4_base_woven (G.induce (F : Set V)) T D B
      (Woven.outerScale m i) hT3
      (Woven.outerScale_pos m i) (le_of_not_gt hcut)
      hD hB hconn hχ
  have hbudget : ∀ i, i < m →
      3 * Woven.outerChildLoss (Woven.outerScale m i) D
        (hh i) (ss i) ≤ B * Woven.outerScale m i := by
    intro i hi
    exact theorem4_child_budget D s (Woven.outerScale m i) hD
  have hGN : ∀ i, i < m →
      D * Woven.outerScale m i ≤
        D * T + B * Woven.outerScale m (i + 1) := by
    intro i hi
    exact theorem4_outer_gn_budget m i T D s hi hD
  have hsepThreshold : ∀ i, i < m →
      ss i <
        D * T + B * Woven.outerScale m (i + 1) +
          6 * (D * Woven.outerScale m i) := by
    intro i hi
    exact theorem4_outer_sep_budget m i T D s hi hD
  have hhub : ∀ i, (hi : i < m) →
      cutoff < (Woven.outerScale m i : ℝ) →
      ∀ F : Finset V,
        VertexConnected (G.induce (F : Set V))
          (D * Woven.outerScale m i) →
        D * T + B * Woven.outerScale m i ≤
          chromatic (G.induce (F : Set V)) →
        Woven.OuterHubContract (G.induce (F : Set V))
          (Woven.outerScale m i) (hh i) := by
    intro i hi hcut F hconn hχ
    have hcoef : 994 ≤ B := theorem4_B_ge D s hD
    have hmul : 994 * Woven.outerScale m i ≤
        B * Woven.outerScale m i :=
      Nat.mul_le_mul_right _ hcoef
    exact theorem4_hub_contract (G.induce (F : Set V))
      (Woven.outerScale m i) (Woven.outerScale_pos m i)
      (by omega)
  have hseps : ∀ i, (hi : i < m) →
      cutoff < (Woven.outerScale m i : ℝ) →
      ∀ F : Finset V,
        Woven.OuterSepContract (G.induce (F : Set V))
          (Woven.outerScale m i) (ss i) := by
    intro i hi hcut F
    exact hsep i hi hcut F
  exact Woven.outerAt_top_of_base_or_contracts
    G m D (D * T) B cutoff hh ss
    (by omega) hbase hsmall hbudget hGN hsepThreshold hhub hseps

end HadwigerLean.Deduction
