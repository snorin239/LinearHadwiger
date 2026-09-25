import HadwigerLean.Deduction.Corollary24BaseWoven
import HadwigerLean.Deduction.Corollary24HubContract
import HadwigerLean.Deduction.Corollary24SepContract
import HadwigerLean.Deduction.Corollary24OuterNumerics
import HadwigerLean.Deduction.Corollary24Scale
import HadwigerLean.Deduction.Corollary24Final
import HadwigerLean.Woven.OuterInductionMixed
import HadwigerLean.Woven.ScaleBridge
import Mathlib.Tactic

/-!
# Unconditional proof of paper Corollary 24

The checked shared outer induction is specialized to K=10000,
B=10^6(d+1), U=2000T, h(a)=980a, and sigma(a)=14da.
-/

namespace HadwigerLean.Deduction

universe u

theorem cor24_outerAt_top
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m T d : ℕ) (hT : T = 3 ^ m) (hT100 : 100 ≤ T)
    (hsep : Bootstrap.OuterSeparation G T d) :
    Woven.OuterAt G m 0 10000 (2000 * T) (cor24B d) := by
  classical
  let cutoff : ℝ := (T : ℝ) / Real.sqrt (Real.log (T : ℝ))
  let hh : ℕ → ℕ := fun i => 980 * Woven.outerScale m i
  let ss : ℕ → ℕ := fun i => 14 * d * Woven.outerScale m i
  have hlast : (Woven.outerScale m m : ℝ) ≤ cutoff := by
    exact cor24_outerScale_last_le_top_div_sqrt_log m T hT hT100
  have hbase : Woven.OuterAt G m m 10000 (2000 * T) (cor24B d) := by
    intro F hconn hχ
    exact cor24_base_woven (G.induce (F : Set V)) T d
      (Woven.outerScale m m) hT100 (by
        exact Woven.outerScale_pos m m)
      hlast hconn hχ
  have hsmall : ∀ i, i < m →
      ¬ cutoff < (Woven.outerScale m i : ℝ) →
      Woven.OuterAt G m i 10000 (2000 * T) (cor24B d) := by
    intro i hi hcut
    intro F hconn hχ
    exact cor24_base_woven (G.induce (F : Set V)) T d
      (Woven.outerScale m i) hT100
      (Woven.outerScale_pos m i)
      (le_of_not_gt hcut) hconn hχ
  have hbudget : ∀ i, i < m →
      3 * Woven.outerChildLoss (Woven.outerScale m i) 10000
        (hh i) (ss i) ≤ cor24B d * Woven.outerScale m i := by
    intro i hi
    simpa [hh, ss, cor24B] using
      Woven.cor24_outer_child_budget (Woven.outerScale m i) d
  have hGN : ∀ i, i < m →
      10000 * Woven.outerScale m i ≤
        2000 * T + cor24B d * Woven.outerScale m (i + 1) := by
    intro i hi
    exact cor24_outer_gn_budget m i T d hi
  have hsepThreshold : ∀ i, i < m →
      ss i <
        2000 * T + cor24B d * Woven.outerScale m (i + 1) +
          6 * (10000 * Woven.outerScale m i) := by
    intro i hi
    exact cor24_outer_sep_budget m i T d hi
  have hhub : ∀ i, (hi : i < m) →
      cutoff < (Woven.outerScale m i : ℝ) →
      ∀ F : Finset V,
        VertexConnected (G.induce (F : Set V))
          (10000 * Woven.outerScale m i) →
        2000 * T + cor24B d * Woven.outerScale m i ≤
          chromatic (G.induce (F : Set V)) →
        Woven.OuterHubContract (G.induce (F : Set V))
          (Woven.outerScale m i) (hh i) := by
    intro i hi hcut F hconn hχ
    exact cor24_hub_contract (G.induce (F : Set V))
      T d (Woven.outerScale m i)
      (Woven.outerScale_pos m i) hχ
  have hseps : ∀ i, (hi : i < m) →
      cutoff < (Woven.outerScale m i : ℝ) →
      ∀ F : Finset V,
        Woven.OuterSepContract (G.induce (F : Set V))
          (Woven.outerScale m i) (ss i) := by
    intro i hi hcut F
    have hscale : Bootstrap.IsOuterScale T (Woven.outerScale m i) := by
      rw [hT]
      exact Woven.outerScale_isOuterScale m i (Nat.le_of_lt hi)
    have hsepF : Bootstrap.OuterSeparation
        (G.induce (F : Set V)) T d :=
      outerSeparation_induce G T d hsep (F : Set V)
    exact cor24_sep_contract (G.induce (F : Set V))
      T d (Woven.outerScale m i) hscale hcut hsepF
  exact Woven.outerAt_top_of_base_or_contracts
    G m 10000 (2000 * T) (cor24B d) cutoff hh ss
    (by omega) hbase hsmall hbudget hGN hsepThreshold hhub hseps

/-- The paper's Corollary 24, with no additional theorem assumptions. -/
theorem corollary24_proved : Corollary24Statement.{u} := by
  classical
  intro V _ G t T d ht hT hd hminor hsep
  obtain ⟨m,hm⟩ := hT.1
  have hT100 : 100 ≤ T := le_trans ht hT.2.1
  have htop : Woven.OuterAt G m 0 10000 (2000 * T) (cor24B d) :=
    cor24_outerAt_top G m T d hm hT100 hsep
  apply cor24_final_of_top_woven G t T d ht hT hminor
  intro F hconn hχ
  have hW := htop F
    (by simpa [Woven.outerScale_zero, ← hm] using hconn)
    (by simpa [Woven.outerScale_zero, ← hm] using hχ)
  simpa [Woven.outerScale_zero, ← hm] using hW

end HadwigerLean.Deduction
