import HadwigerLean.Woven.DistinctRoles

/-!
# Extending a path from an induced subgraph to prescribed outer endpoints

The normalized woven construction first works after deleting original
terminal roles, then joins proxy endpoints back to those roles. The path
obtained by appending these two edges can be shortened without leaving the
original path and the two prescribed endpoints.
-/

namespace HadwigerLean

universe v

/-- Extend an inner path by one edge at either end, then shorten the
resulting walk to a simple path. -/
noncomputable def extendInducedPath {V : Type v} {G : SimpleGraph V}
    (S : Set V) {s t : V} (u w : S)
    (p : (G.induce S).Path u w)
    (hs : G.Adj s u.1) (ht : G.Adj w.1 t) : G.Path s t := by
  classical
  let e : (G.induce S) ↪g G := SimpleGraph.Embedding.induce S
  let q : G.Path u.1 w.1 := SimpleGraph.Path.mapEmbedding e p
  exact (SimpleGraph.Walk.cons hs
    ((q : G.Walk u.1 w.1).append (SimpleGraph.Walk.cons ht SimpleGraph.Walk.nil))).toPath

/-- The extended path uses only the original terminal vertices and vertices
of the inner path. -/
theorem extendInducedPath_vertices_subset {V : Type v} {G : SimpleGraph V}
    (S : Set V) {s t : V} (u w : S)
    (p : (G.induce S).Path u w)
    (hs : G.Adj s u.1) (ht : G.Adj w.1 t) :
    pathVertexSet (extendInducedPath S u w p hs ht) ⊆
      ({s, t} : Set V) ∪ (Subtype.val '' pathVertexSet p) := by
  classical
  intro x hx
  let e : (G.induce S) ↪g G := SimpleGraph.Embedding.induce S
  let q : G.Path u.1 w.1 := SimpleGraph.Path.mapEmbedding e p
  let v : G.Walk s t := SimpleGraph.Walk.cons hs
    ((q : G.Walk u.1 w.1).append (SimpleGraph.Walk.cons ht SimpleGraph.Walk.nil))
  have hxpath : x ∈ (v.toPath : G.Walk s t).support := by
    simpa only [extendInducedPath, pathVertexSet, Set.mem_setOf_eq] using hx
  have hxv : x ∈ v.support := v.support_toPath_subset_support hxpath
  have hxcase : x = s ∨ x ∈ (q : G.Walk u.1 w.1).support ∨ x = w.1 ∨ x = t := by
    simpa only [v, SimpleGraph.Walk.support_cons, List.mem_cons,
      SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_nil, List.mem_singleton, List.not_mem_nil,
      or_false] using hxv
  rcases hxcase with hxs | hxq | hxw | hxt
  · exact Or.inl (by simp [hxs])
  · right
    change x ∈ (p.1.map e.toHom).support at hxq
    rw [SimpleGraph.Walk.support_map] at hxq
    rcases List.mem_map.mp hxq with ⟨z, hz, hzx⟩
    exact ⟨z, hz, hzx⟩
  · right
    subst x
    have hwq : w.1 ∈ (q : G.Walk u.1 w.1).support :=
      (q : G.Walk u.1 w.1).end_mem_support
    change w.1 ∈ (p.1.map e.toHom).support at hwq
    rw [SimpleGraph.Walk.support_map] at hwq
    rcases List.mem_map.mp hwq with ⟨z, hz, hzx⟩
    exact ⟨z, hz, hzx⟩
  · exact Or.inl (by simp [hxt])

end HadwigerLean
