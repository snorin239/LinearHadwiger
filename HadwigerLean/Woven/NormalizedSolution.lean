import HadwigerLean.Woven.NormalizedRootedModel

/-!
# Lifting a normalized woven solution

The original roots and terminals lie outside the normalized graph, while
their distinct proxies lie inside it. Extending the rooted model and each
linkage path by the proxy edges preserves exact intersection.
-/

namespace HadwigerLean

universe v

namespace WovenSolution

variable {V : Type v} {G : SimpleGraph V} {S : Set V}
  {a j : ℕ} {proxy : Fin a → S}
  {Q : IndexedPairs (Fin j) S}
  {root : Fin a → V} {P : IndexedPairs (Fin j) V}

/-- Lift a proxy woven solution to prescribed original roles, assuming
original roles are outside the normalized graph and proxy root roles are
disjoint from proxy terminal roles. -/
noncomputable def extendFromInduced
    (T : WovenSolution (G.induce S) proxy Q)
    (hproxyRoles : Disjoint (Set.range proxy) Q.allTerminals)
    (hroot : Function.Injective root)
    (hrootOutside : ∀ i, root i ∉ S)
    (hP : P.DisjointTerminals)
    (hPOutside : ∀ i, P.start i ∉ S ∧ P.finish i ∉ S)
    (hrootEdge : ∀ i, G.Adj (root i) (proxy i).1)
    (hstartEdge : ∀ i, G.Adj (P.start i) (Q.start i).1)
    (hfinishEdge : ∀ i, G.Adj (Q.finish i).1 (P.finish i)) :
    WovenSolution G root P := by
  let M := T.model.extendFromInduced root hroot hrootOutside hrootEdge
  let L := T.linkage.extendFromInduced hP hPOutside hstartEdge hfinishEdge
  have hinner : Disjoint T.model.toMinorModel.vertices T.linkage.vertices := by
    apply Set.disjoint_left.mpr
    intro z hzM hzL
    have hzroles := (T.overlap_iff z).mp ⟨hzM, hzL⟩
    exact (Set.disjoint_left.mp hproxyRoles) hzroles.1 hzroles.2
  refine ⟨M, L, ?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    have hxM := T.model.extendFromInduced_vertices_subset
      root hroot hrootOutside hrootEdge hx.1
    have hxL := T.linkage.extendFromInduced_vertices_subset
      hP hPOutside hstartEdge hfinishEdge hx.2
    rcases hxM with hxRoot | hxInnerM
    · rcases hxL with hxTerm | hxInnerL
      · exact ⟨hxRoot, hxTerm⟩
      · rcases hxRoot with ⟨i, rfl⟩
        rcases hxInnerL with ⟨z, _, hz⟩
        exact (hrootOutside i (hz ▸ z.property)).elim
    · rcases hxL with hxTerm | hxInnerL
      · rcases hxInnerM with ⟨z, _, rfl⟩
        rcases Set.mem_iUnion.mp hxTerm with ⟨i, hi⟩
        rcases hi with hs | ht
        · exact ((hPOutside i).1 (hs ▸ z.property)).elim
        · exact ((hPOutside i).2 (ht ▸ z.property)).elim
      · rcases hxInnerM with ⟨z, hzM, rfl⟩
        rcases hxInnerL with ⟨w, hwL, heq⟩
        have hzw : z = w := Subtype.ext heq.symm
        subst w
        exact ((Set.disjoint_left.mp hinner) hzM hwL).elim
  · intro x hx
    have hxM : x ∈ M.toMinorModel.vertices := by
      rcases hx.1 with ⟨i, rfl⟩
      exact Set.mem_iUnion.mpr ⟨i, M.root_mem i⟩
    have hxL : x ∈ L.vertices := by
      rcases Set.mem_iUnion.mp hx.2 with ⟨i, hi⟩
      rcases hi with hs | ht
      · subst x
        exact L.start_mem_vertices i
      · subst x
        exact L.finish_mem_vertices i
    exact ⟨hxM, hxL⟩

end WovenSolution

namespace Woven

variable {V : Type v} {G : SimpleGraph V} {S : Set V}
  {n a j : ℕ}

/-- A rooted clique minor at distinct proxies in the normalized graph
supplies a woven solution at arbitrary original roles outside that graph,
provided each role has its prescribed proxy edge. -/
theorem exists_solution_of_normalized_minor
    (role : Fin n → S)
    (f : DistinctRoleIndex a j ↪ Fin n)
    (hminor : HasRootedCliqueMinor (G.induce S) role)
    (root : Fin a → V) (P : IndexedPairs (Fin j) V)
    (hroot : Function.Injective root)
    (hrootOutside : ∀ i, root i ∉ S)
    (hP : P.DisjointTerminals)
    (hPOutside : ∀ i, P.start i ∉ S ∧ P.finish i ∉ S)
    (hrootEdge : ∀ i, G.Adj (root i) (selectedRoots f role i).1)
    (hstartEdge : ∀ i, G.Adj (P.start i) ((selectedPairs f role).start i).1)
    (hfinishEdge : ∀ i, G.Adj ((selectedPairs f role).finish i).1 (P.finish i)) :
    Nonempty (WovenSolution G root P) := by
  obtain ⟨M⟩ := hminor
  obtain ⟨T⟩ := exists_solution_of_distinct_roles M f
  have hdis := selectedRoles_disjoint f role M.root_injective
  exact ⟨T.extendFromInduced hdis hroot hrootOutside hP hPOutside
    hrootEdge hstartEdge hfinishEdge⟩

end Woven
end HadwigerLean
