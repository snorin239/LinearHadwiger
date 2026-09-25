import HadwigerLean.Graph.Finite

/-! Coloring a graph by separate palettes on two covering induced subgraphs. -/

namespace HadwigerLean.Bootstrap

universe u

/-- If two vertex sets cover the graph, separate palettes for their induced
subgraphs give a coloring with the sum of their chromatic numbers. -/
theorem chromatic_le_add_induce {V : Type u} [Fintype V]
    (G : SimpleGraph V) (W R : Set V) (hcover : W ∪ R = Set.univ) :
    HadwigerLean.chromatic G ≤
      HadwigerLean.chromatic (G.induce W) +
        HadwigerLean.chromatic (G.induce R) := by
  classical
  let m := HadwigerLean.chromatic (G.induce W)
  let n := HadwigerLean.chromatic (G.induce R)
  let cW : (G.induce W).Coloring (Fin m) :=
    (HadwigerLean.colorable_chromatic (G.induce W)).some
  let cR : (G.induce R).Coloring (Fin n) :=
    (HadwigerLean.colorable_chromatic (G.induce R)).some
  have hmem (v : V) : v ∈ W ∨ v ∈ R := by
    have hv : v ∈ W ∪ R := hcover.symm ▸ Set.mem_univ v
    simpa only [Set.mem_union] using hv
  let c : G.Coloring (Fin m ⊕ Fin n) :=
    SimpleGraph.Coloring.mk
      (fun v => if hv : v ∈ W then Sum.inl (cW ⟨v, hv⟩)
        else Sum.inr (cR ⟨v, (hmem v).resolve_left hv⟩))
      (by
        intro v w hvw
        dsimp
        split_ifs with hvW hwW
        · exact Sum.inl_injective.ne (cW.valid hvw)
        · intro h
          cases h
        · intro h
          cases h
        · exact Sum.inr_injective.ne (cR.valid hvw))
  have hc : G.Colorable (m + n) := by
    simpa [Fintype.card_sum] using c.colorable
  exact (HadwigerLean.chromatic_le_iff_colorable G (m + n)).mpr hc

end HadwigerLean.Bootstrap
