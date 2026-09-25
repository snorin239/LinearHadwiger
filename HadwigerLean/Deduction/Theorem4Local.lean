import HadwigerLean.Deduction.Theorem4ScaleTransport
import HadwigerLean.Graph.CliqueMinorOrder
import Mathlib.Tactic

/-! Local chromatic bounds supplied by the enlarged-scale ratio maximum. -/

namespace HadwigerLean.Deduction

universe u

theorem theorem4_local_chromatic_bound
    {V : Type u} [Fintype V] (Y : SimpleGraph V)
    (D T q s : ℕ) (hqpos : 0 < q)
    (hwindow : (T : ℝ) / Real.sqrt (Real.log (T : ℝ)) ≤ (q : ℝ))
    (hqT : q ≤ 14 * T)
    (hminor : ¬ HasCliqueMinor Y q)
    (hf : theorem4ScaleMaxRatio Y D T ≤ (s : ℝ))
    (U : Finset V)
    (horder : (U.card : ℝ) ≤
      (D : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ (4 : ℝ)) :
    chromatic (Y.induce (U : Set V)) ≤ q * s := by
  classical
  let H : Y.Subgraph := (⊤ : Y.Subgraph).induce (U : Set V)
  have hHcoe : H.coe = Y.induce (U : Set V) := by
    exact (Y.induce_eq_coe_induce_top (U : Set V)).symm
  have hHminor : ¬ HasCliqueMinor H.coe q := by
    rw [hHcoe]
    intro h
    let e : Y.induce (U : Set V) ↪g Y := SimpleGraph.Embedding.induce _
    exact hminor (hasCliqueMinor_map e.toHom e.injective h)
  have hHorder : (Nat.card H.verts : ℝ) ≤
      (D : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ (4 : ℝ) := by
    simpa [H, Nat.card_eq_fintype_card] using horder
  have hratio : (chromatic H.coe : ℝ) / (q : ℝ) ≤
      theorem4ScaleMaxRatio Y D T :=
    theorem4_scale_candidate_le_max Y D T q H
      hwindow hqT hHminor hHorder
  have hqposR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hχR : (chromatic (Y.induce (U : Set V)) : ℝ) ≤
      (q : ℝ) * (s : ℝ) := by
    have hratio' : (chromatic (Y.induce (U : Set V)) : ℝ) /
        (q : ℝ) ≤ (s : ℝ) := by
      rw [← hHcoe]
      exact hratio.trans hf
    nlinarith [(div_le_iff₀ hqposR).mp hratio']
  exact_mod_cast hχR

end HadwigerLean.Deduction
