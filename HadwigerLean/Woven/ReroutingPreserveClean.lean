import HadwigerLean.Woven.ManyChildRerouting

/-!
# Clean endpoint sets survive rerouting

If a rerouted linkage uses only old path vertices and new vertices outside
a distinguished endpoint set, then a path can meet that set only at its
own old endpoint. Vertex disjointness prevents a path from taking another
path's endpoint.
-/

namespace HadwigerLean.Woven

variable {I V : Type*} {G : SimpleGraph V}
  {P : IndexedPairs I V}

theorem IndexedLinkage.clean_finish_of_supported_reroute
    (L₀ L : IndexedLinkage G P) (D J : Set V)
    (hOldClean : ∀ i v, v ∈ pathVertexSet (L₀.path i) →
      v ∈ D → v = P.finish i)
    (hSupport : L.vertices ⊆ L₀.vertices ∪ J)
    (hJD : Disjoint J D) :
    ∀ i v, v ∈ pathVertexSet (L.path i) →
      v ∈ D → v = P.finish i := by
  intro i v hv hvD
  have hvAll : v ∈ L.vertices := L.path_subset_vertices i hv
  have hvOld : v ∈ L₀.vertices := by
    rcases hSupport hvAll with hvOld | hvJ
    · exact hvOld
    · exact False.elim ((Set.disjoint_left.mp hJD) hvJ hvD)
  obtain ⟨j,hvj⟩ := Set.mem_iUnion.mp hvOld
  have hvFinish : v = P.finish j := hOldClean j v hvj hvD
  by_cases hij : i = j
  · subst j
    exact hvFinish
  · have hvjL : v ∈ pathVertexSet (L.path j) := by
      rw [hvFinish]
      exact pathVertexSet.finish_mem (L.path j)
    exact False.elim ((Set.disjoint_left.mp (L.disjoint hij)) hv hvjL)

theorem IndexedLinkage.clean_start_of_supported_reroute
    (L₀ L : IndexedLinkage G P) (U J : Set V)
    (hOldClean : ∀ i v, v ∈ pathVertexSet (L₀.path i) →
      v ∈ U → v = P.start i)
    (hSupport : L.vertices ⊆ L₀.vertices ∪ J)
    (hJU : Disjoint J U) :
    ∀ i v, v ∈ pathVertexSet (L.path i) →
      v ∈ U → v = P.start i := by
  intro i v hv hvU
  have hvAll : v ∈ L.vertices := L.path_subset_vertices i hv
  have hvOld : v ∈ L₀.vertices := by
    rcases hSupport hvAll with hvOld | hvJ
    · exact hvOld
    · exact False.elim ((Set.disjoint_left.mp hJU) hvJ hvU)
  obtain ⟨j,hvj⟩ := Set.mem_iUnion.mp hvOld
  have hvStart : v = P.start j := hOldClean j v hvj hvU
  by_cases hij : i = j
  · subst j
    exact hvStart
  · have hvjL : v ∈ pathVertexSet (L.path j) := by
      rw [hvStart]
      exact pathVertexSet.start_mem (L.path j)
    exact False.elim ((Set.disjoint_left.mp (L.disjoint hij)) hv hvjL)

end HadwigerLean.Woven
