import HadwigerLean.Deduction.Theorem4Scale
import HadwigerLean.Graph.SubgraphImageIso
import Mathlib.Tactic

/-! The enlarged-scale ratio maximum is monotone under induced subgraphs. -/

namespace HadwigerLean.Deduction

universe u

theorem theorem4_scale_candidate_le_max
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (D T q : ℕ) (H : G.Subgraph)
    (hwindow : (T : ℝ) / Real.sqrt (Real.log (T : ℝ)) ≤ (q : ℝ))
    (hq : q ≤ 14 * T)
    (hminor : ¬ HasCliqueMinor H.coe q)
    (horder : (Nat.card H.verts : ℝ) ≤
      (D : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ (4 : ℝ)) :
    (chromatic H.coe : ℝ) / (q : ℝ) ≤
      theorem4ScaleMaxRatio G D T := by
  classical
  unfold theorem4ScaleMaxRatio
  apply le_csSup (theorem4ScaleRatioSet_finite G D T).bddAbove
  exact Or.inr ⟨q, H, hwindow, hq, hminor, horder, rfl⟩

theorem theorem4_scale_candidate_induce_le_max
    {V : Type u} [Fintype V] (G : SimpleGraph V) (U : Set V)
    [Fintype U] (D T q : ℕ)
    (hwindow : (T : ℝ) / Real.sqrt (Real.log (T : ℝ)) ≤ (q : ℝ))
    (hq : q ≤ 14 * T)
    (H : (G.induce U).Subgraph)
    (hminor : ¬ HasCliqueMinor H.coe q)
    (horder : (Nat.card H.verts : ℝ) ≤
      (D : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ (4 : ℝ)) :
    (chromatic H.coe : ℝ) / (q : ℝ) ≤
      theorem4ScaleMaxRatio G D T := by
  classical
  let f : G.induce U ↪g G := SimpleGraph.Embedding.induce _
  let J : G.Subgraph := H.map f.toHom
  let e : H.coe ≃g J.coe := subgraphMapIso f H
  have hcard : Nat.card J.verts = Nat.card H.verts := by
    have hc : Fintype.card H.verts = Fintype.card J.verts :=
      Fintype.card_congr e.toEquiv
    simpa only [Nat.card_eq_fintype_card] using hc.symm
  have hχ : chromatic H.coe = chromatic J.coe := by
    unfold chromatic
    exact congrArg ENat.toNat (SimpleGraph.chromaticNumber_congr e)
  have hJminor : ¬ HasCliqueMinor J.coe q := by
    intro h
    exact hminor (hasCliqueMinor_map e.symm.toHom
      e.symm.injective h)
  have hJorder : (Nat.card J.verts : ℝ) ≤
      (D : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ (4 : ℝ) := by
    rw [hcard]
    exact horder
  simpa only [hχ] using
    theorem4_scale_candidate_le_max G D T q J hwindow hq hJminor hJorder

theorem theorem4ScaleMaxRatio_induce_le
    {V : Type u} [Fintype V] (G : SimpleGraph V) (U : Set V)
    [Fintype U] (D T : ℕ) :
    theorem4ScaleMaxRatio (G.induce U) D T ≤
      theorem4ScaleMaxRatio G D T := by
  unfold theorem4ScaleMaxRatio
  apply csSup_le
    (theorem4ScaleRatioSet_nonempty (G.induce U) D T)
  intro r hr
  change r ∈ ({0} ∪ {s : ℝ | ∃ (q : ℕ)
    (H : (G.induce U).Subgraph),
    (T : ℝ) / Real.sqrt (Real.log (T : ℝ)) ≤ (q : ℝ) ∧
    q ≤ 14 * T ∧
    ¬ HasCliqueMinor H.coe q ∧
    (Nat.card H.verts : ℝ) ≤
      (D : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ (4 : ℝ) ∧
    s = (chromatic H.coe : ℝ) / (q : ℝ)}) at hr
  rcases hr with hr | ⟨q, H, hwindow, hq, hHminor, horder, rfl⟩
  · have hr0 : r = 0 := by simpa using hr
    subst r
    exact theorem4ScaleMaxRatio_nonneg G D T
  · exact theorem4_scale_candidate_induce_le_max G U D T q
      hwindow hq H hHminor horder

end HadwigerLean.Deduction
