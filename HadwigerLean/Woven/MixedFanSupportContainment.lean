import HadwigerLean.Woven.MixedFanTrim
import HadwigerLean.Woven.DoubleFanCost
import Mathlib.Tactic

/-!
# Vertex support of a mixed-fan linkage

The mixed Menger argument runs in the graph made of the supplied fan and
connector edges. A path beginning on one of those paths cannot introduce
any other vertex. This records the containment needed when routing around
the old model and the child pieces.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {Z H : Finset V} {a : ℕ}
  {P : IndexedPairs (Fin a × Fin 2) V}

theorem mixedSupportGraph_path_subset_used
    (F : DoubleFan G Z H) (L : IndexedLinkage G P)
    {s t : V} (p : (mixedSupportGraph F L).Path s t)
    (hs : s ∈ (F.vertexFinset : Set V) ∪ L.vertices) :
    pathVertexSet p ⊆ (F.vertexFinset : Set V) ∪ L.vertices := by
  classical
  let E := mixedSupportGraph F L
  have hedge (e : Sym2 V)
      (he : e ∈ (p : E.Walk s t).edges)
      (v : V) (hve : v ∈ e) :
      v ∈ (F.vertexFinset : Set V) ∪ L.vertices := by
    have heE : e ∈ E.edgeSet := (p : E.Walk s t).edges_subset_edgeSet he
    have heUsed : e ∈ mixedUsedEdges F L := by
      have h : e ∈ G.edgeSet ∧ e ∈ mixedUsedEdges F L := by
        simpa [E, mixedSupportGraph] using heE
      exact h.2
    rcases heUsed with ⟨slot,heslot⟩ | ⟨slot,heslot⟩
    · apply Or.inl
      change v ∈ F.vertexFinset
      apply Finset.mem_biUnion.mpr
      refine ⟨slot,Finset.mem_univ _,?_⟩
      apply List.mem_toFinset.mpr
      exact (SimpleGraph.Walk.mem_support_iff_exists_mem_edges).mpr
        (Or.inr ⟨e,heslot,hve⟩)
    · apply Or.inr
      exact L.path_subset_vertices slot
        ((SimpleGraph.Walk.mem_support_iff_exists_mem_edges).mpr
          (Or.inr ⟨e,heslot,hve⟩))
  intro v hv
  by_cases hnil : (p : E.Walk s t).Nil
  · have hst : s = t := hnil.eq
    have hsingle : pathVertexSet p = {s} :=
      pathVertexSet.eq_singleton_of_eq p hst
    rw [hsingle] at hv
    simpa using hv ▸ hs
  · obtain ⟨e,he,hve⟩ :=
      (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hnil).mp hv
    exact hedge e he v hve


/-- A clean mixed linkage supported on the supplied fan and connector vertices. -/
theorem exists_mixed_linkage_clean_supported
    (F : DoubleFan G Z H) (L : IndexedLinkage G P)
    (U : Finset V)
    (hU : ∀ slot, P.start slot ∈ U)
    (hfinish : ∀ slot, P.finish slot ∈ H)
    (havoidZ : ∀ slot v, v ∈ pathVertexSet (L.path slot) → v ∉ Z)
    (hfanU : ∀ slot v, v ∈ pathVertexSet (F.path slot) → v ∉ U)
    (hlinkU : ∀ slot v, v ∈ pathVertexSet (L.path slot) →
      v ∈ U → v = P.start slot)
    (hZU : Disjoint Z U) (hHU : Disjoint H U) :
    ∃ (R : IndexedPairs (Z ⊕ Fin a) V) (N : IndexedLinkage G R),
      (∀ z : Z, R.start (.inl z) = z.1) ∧
      (∀ i : Fin a, ∃ b : Fin 2, R.start (.inr i) = P.start (i,b)) ∧
      SetMenger.IsABLinkage N (Z ∪ U) H ∧
      (∀ x v, v ∈ pathVertexSet (N.path x) →
        v ∈ Z ∪ U ∪ H → v = R.start x ∨ v = R.finish x) ∧
      (∀ x, pathVertexSet (N.path x) ⊆
        (F.vertexFinset : Set V) ∪ L.vertices) := by
  classical
  let E := mixedSupportGraph F L
  let F' : DoubleFan E Z H := F.toMixedSupport L
  let L' : IndexedLinkage E P := HadwigerLean.Woven.IndexedLinkage.toMixedSupport F L
  have hFsupp (slot : Z × Fin 2) :
      pathVertexSet (F'.path slot) = pathVertexSet (F.path slot) := by
    ext v
    simp only [F', DoubleFan.toMixedSupport, pathVertexSet]
    rw [SimpleGraph.Walk.support_transfer]
  have hLsupp (slot : Fin a × Fin 2) :
      pathVertexSet (L'.path slot) = pathVertexSet (L.path slot) := by
    ext v
    simp only [L', IndexedLinkage.toMixedSupport, pathVertexSet]
    rw [SimpleGraph.Walk.support_transfer]
  have havoidZ' (slot) (v) (hv : v ∈ pathVertexSet (L'.path slot)) :
      v ∉ Z := havoidZ slot v ((hLsupp slot) ▸ hv)
  have hfanU' (slot) (v) (hv : v ∈ pathVertexSet (F'.path slot)) :
      v ∉ U := hfanU slot v ((hFsupp slot) ▸ hv)
  have hlinkU' (slot) (v) (hv : v ∈ pathVertexSet (L'.path slot))
      (hvU : v ∈ U) : v = P.start slot :=
    hlinkU slot v ((hLsupp slot) ▸ hv) hvU
  obtain ⟨R,N₀,hproxy,hpair,hAB,hclean⟩ :=
    exists_mixed_linkage_clean F' L' hU hfinish havoidZ'
      hfanU' hlinkU' hZU hHU
  let N : IndexedLinkage G R := N₀.mono (mixedSupportGraph_le F L)
  have hNsupp (x) :
      pathVertexSet (N.path x) = pathVertexSet (N₀.path x) := by
    simp [N, IndexedLinkage.mono, pathVertexSet,
      SimpleGraph.Walk.support_mapLe_eq_support]
  refine ⟨R,N,hproxy,hpair,hAB,?_,?_⟩
  · intro x v hv hvset
    exact hclean x v ((hNsupp x) ▸ hv) hvset
  · intro x
    have hs : R.start x ∈ (F.vertexFinset : Set V) ∪ L.vertices := by
      cases x with
      | inl z =>
          apply Or.inl
          rw [hproxy]
          change z.1 ∈ F.vertexFinset
          apply Finset.mem_biUnion.mpr
          refine ⟨(z,0),Finset.mem_univ _,?_⟩
          exact List.mem_toFinset.mpr
            (pathVertexSet.start_mem (F.path (z,0)))
      | inr i =>
          obtain ⟨b,hb⟩ := hpair i
          exact Or.inr (hb ▸ L.start_mem_vertices (i,b))
    intro v hv
    exact mixedSupportGraph_path_subset_used F L (N₀.path x) hs
      ((hNsupp x) ▸ hv)

end Woven
end HadwigerLean



