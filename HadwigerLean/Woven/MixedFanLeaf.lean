import HadwigerLean.Woven.MixedFanSupportGraph
import Mathlib.Tactic

/-!
# Residual starts are leaves in the path-edge-supported graph
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {Z U H : Finset V} {a : ℕ}
  {P : IndexedPairs (Fin a × Fin 2) V}

private theorem support_adj_used
    (F : DoubleFan G Z H) (L : IndexedLinkage G P)
    {u v : V} (huv : (mixedSupportGraph F L).Adj u v) :
    s(u,v) ∈ mixedUsedEdges F L := by
  have h : G.Adj u v ∧
      s(u,v) ∉ G.edgeSet \ mixedUsedEdges F L := by
    simpa [mixedSupportGraph] using huv
  by_contra hnot
  exact h.2 ⟨G.mem_edgeSet.mpr h.1, hnot⟩

/-- At every vertex of U, all supported edges have the same opposite
endpoint, provided fan paths avoid U and each connector meets U only
at its own start. -/
theorem mixedSupportGraph_unique_neighbor_at_U
    (F : DoubleFan G Z H) (L : IndexedLinkage G P)
    (hfanU : ∀ slot v, v ∈ pathVertexSet (F.path slot) → v ∉ U)
    (hlinkU : ∀ slot v, v ∈ pathVertexSet (L.path slot) →
      v ∈ U → v = P.start slot)
    {u v w : V} (hu : u ∈ U)
    (huv : (mixedSupportGraph F L).Adj u v)
    (huw : (mixedSupportGraph F L).Adj u w) : v = w := by
  have edge_from_link {y : V} (huy : (mixedSupportGraph F L).Adj u y) :
      ∃ slot : Fin a × Fin 2,
        u = P.start slot ∧
        s(u,y) ∈ (L.path slot : G.Walk (P.start slot) (P.finish slot)).edges := by
    have hused := support_adj_used F L huy
    rcases hused with ⟨slot, he⟩ | ⟨slot, he⟩
    · have huF : u ∈ pathVertexSet (F.path slot) :=
        (F.path slot : G.Walk slot.1.1 (F.finish slot)).fst_mem_support_of_mem_edges he
      exact False.elim (hfanU slot u huF hu)
    · have huL : u ∈ pathVertexSet (L.path slot) :=
        (L.path slot : G.Walk (P.start slot) (P.finish slot)).fst_mem_support_of_mem_edges he
      exact ⟨slot, hlinkU slot u huL hu, he⟩
  obtain ⟨slotV, hslotV, heV⟩ := edge_from_link huv
  obtain ⟨slotW, hslotW, heW⟩ := edge_from_link huw
  have hslots : slotV = slotW :=
    L.start_injective (hslotV.symm.trans hslotW)
  subst slotW
  have hv : v = (L.path slotV : G.Walk (P.start slotV) (P.finish slotV)).snd := by
    apply SimpleGraph.Walk.IsPath.eq_snd_of_mem_edges (L.path slotV).property
    simpa [hslotV] using heV
  have hw : w = (L.path slotV : G.Walk (P.start slotV) (P.finish slotV)).snd := by
    apply SimpleGraph.Walk.IsPath.eq_snd_of_mem_edges (L.path slotV).property
    simpa [hslotW] using heW
  exact hv.trans hw.symm


/-- A vertex whose neighbor set is a singleton cannot occur internally
on a simple path. -/
theorem path_support_U_only_endpoints
    {E : SimpleGraph V} (U : Finset V)
    (hunique : ∀ u ∈ U, ∀ v w, E.Adj u v → E.Adj u w → v = w)
    {s t u : V} (p : E.Path s t)
    (hu : u ∈ U) (hp : u ∈ pathVertexSet p) :
    u = s ∨ u = t := by
  by_cases hs : u = s
  · exact Or.inl hs
  by_cases ht : u = t
  · exact Or.inr ht
  have hsub : (E.neighborSet u).Subsingleton := by
    intro v hv w hw
    exact hunique u hu v w hv hw
  have hnot := p.property.isTrail.not_mem_support_of_subsingleton_neighborSet
    hs ht hsub
  exact False.elim (hnot hp)

/-- The mixed fan chosen in the supplied-path graph has interiors outside
U. Proxy paths avoid U entirely, while residual paths meet U only at
their own starts. -/
theorem exists_mixed_linkage_avoiding_residual
    (F : DoubleFan G Z H) (L : IndexedLinkage G P)
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
      (∀ z : Z, ∀ v ∈ pathVertexSet (N.path (.inl z)), v ∉ U) ∧
      (∀ i : Fin a, ∀ v ∈ pathVertexSet (N.path (.inr i)),
        v ∈ U → v = R.start (.inr i)) := by
  obtain ⟨R,Ns,hproxy,hpair,hAB⟩ :=
    exists_supported_mixed_linkage F L U hU hfinish havoidZ
  let E := mixedSupportGraph F L
  have hunique : ∀ u ∈ U, ∀ v w,
      E.Adj u v → E.Adj u w → v = w := by
    intro u hu v w huv huw
    exact mixedSupportGraph_unique_neighbor_at_U F L hfanU hlinkU hu huv huw
  let N : IndexedLinkage G R := Ns.mono (mixedSupportGraph_le F L)
  have hsupp (x : Z ⊕ Fin a) :
      pathVertexSet (N.path x) = pathVertexSet (Ns.path x) := by
    simp [N, IndexedLinkage.mono, pathVertexSet,
      SimpleGraph.Walk.support_mapLe_eq_support]
  refine ⟨R,N,hproxy,hpair,hAB,?_,?_⟩
  · intro z v hv hvU
    have hv' : v ∈ pathVertexSet (Ns.path (.inl z)) := by
      rw [← hsupp]
      exact hv
    rcases path_support_U_only_endpoints U hunique (Ns.path (.inl z))
        hvU hv' with hstart | hend
    · have hvZ : v ∈ Z := by
        rw [hstart, hproxy z]
        exact z.2
      exact (Finset.disjoint_left.mp hZU) hvZ hvU
    · have hvH : v ∈ H := by
        rw [hend]
        exact hAB.2 (.inl z)
      exact (Finset.disjoint_left.mp hHU) hvH hvU
  · intro i v hv hvU
    have hv' : v ∈ pathVertexSet (Ns.path (.inr i)) := by
      rw [← hsupp]
      exact hv
    rcases path_support_U_only_endpoints U hunique (Ns.path (.inr i))
        hvU hv' with hstart | hend
    · exact hstart
    · have hvH : v ∈ H := by
        rw [hend]
        exact hAB.2 (.inr i)
      exact False.elim ((Finset.disjoint_left.mp hHU) hvH hvU)
end Woven
end HadwigerLean
