import HadwigerLean.Graph.IndexedLinkage

/-!
# Mapping a linkage out of an induced subgraph
-/

namespace HadwigerLean

namespace IndexedLinkage

/-- Forget the induced-subgraph subtype on every path of a linkage. -/
def mapInduce {ι V : Type*} {G : SimpleGraph V} {U : Set V}
    {P : IndexedPairs ι U} (L : IndexedLinkage (G.induce U) P) :
    IndexedLinkage G
      ⟨fun i => (P.start i : V), fun i => (P.finish i : V)⟩ := by
  let E : (G.induce U) ↪g G := SimpleGraph.Embedding.induce U
  let P' : IndexedPairs ι V :=
    ⟨fun i => (P.start i : V), fun i => (P.finish i : V)⟩
  have hsupport (i : ι) (v : V) :
      v ∈ pathVertexSet ((L.path i).mapEmbedding E) ↔
        ∃ x ∈ pathVertexSet (L.path i), (x : V) = v := by
    constructor
    · intro hv
      change v ∈ ((L.path i : (G.induce U).Walk (P.start i) (P.finish i)).map E.toHom).support at hv
      rw [SimpleGraph.Walk.support_map] at hv
      obtain ⟨x, hx, hxv⟩ := List.mem_map.mp hv
      exact ⟨x, hx, hxv⟩
    · rintro ⟨x, hx, hxv⟩
      change v ∈ ((L.path i : (G.induce U).Walk (P.start i) (P.finish i)).map E.toHom).support
      rw [SimpleGraph.Walk.support_map]
      exact List.mem_map.mpr ⟨x, hx, hxv⟩
  refine {
    path := fun i => (L.path i).mapEmbedding E
    disjoint := ?_
  }
  intro i j hij
  apply Set.disjoint_left.mpr
  intro v hvi hvj
  obtain ⟨x, hxi, hxv⟩ := (hsupport i v).mp hvi
  obtain ⟨y, hyj, hyv⟩ := (hsupport j v).mp hvj
  have hxy : x = y := Subtype.ext (hxv.trans hyv.symm)
  exact (Set.disjoint_left.mp (L.disjoint hij)) hxi (hxy ▸ hyj)

end IndexedLinkage

end HadwigerLean
