import HadwigerLean.Woven.CommonLemmas

/-!
# Paths through adjacent rooted minor branches

An edge between two connected branch sets gives a path between their
prescribed roots that uses only those two branch sets.
-/

namespace HadwigerLean

universe u v

namespace RootedMinorModel

variable {W : Type u} {V : Type v} {H : SimpleGraph W}
  {G : SimpleGraph V} {root : W → V}

/-- Join roots of adjacent branches inside their union. -/
theorem exists_pairPath (M : RootedMinorModel H G root)
    {i j : W} (hij : H.Adj i j) :
    ∃ p : G.Path (root i) (root j),
      pathVertexSet p ⊆ M.branch i ∪ M.branch j := by
  classical
  obtain ⟨x, hx, y, hy, hxy⟩ := M.adjacent hij
  have hconn : (G.induce (M.branch i ∪ M.branch j)).Connected :=
    G.connected_induce_union (M.connected i).preconnected
      (M.connected j).preconnected hx hy hxy
  let s : Set V := M.branch i ∪ M.branch j
  let a : s := ⟨root i, Or.inl (M.root_mem i)⟩
  let b : s := ⟨root j, Or.inr (M.root_mem j)⟩
  obtain ⟨w, hw⟩ := hconn.exists_isPath a b
  let e : (G.induce s) ↪g G := SimpleGraph.Embedding.induce s
  let p : G.Path (root i) (root j) :=
    SimpleGraph.Path.mapEmbedding e (⟨w, hw⟩ : (G.induce s).Path a b)
  refine ⟨p, ?_⟩
  intro z hz
  change z ∈ (w.map e.toHom).support at hz
  rw [SimpleGraph.Walk.support_map] at hz
  rcases List.mem_map.mp hz with ⟨q, _, hq⟩
  exact hq ▸ q.property

/-- A selected pair path through exactly two branch sets. -/
noncomputable def pairPath (M : RootedMinorModel H G root)
    {i j : W} (hij : H.Adj i j) : G.Path (root i) (root j) :=
  Classical.choose (M.exists_pairPath hij)

/-- Every vertex of the pair path lies in one of its two branches. -/
theorem pairPath_vertices_subset (M : RootedMinorModel H G root)
    {i j : W} (hij : H.Adj i j) :
    pathVertexSet (M.pairPath hij) ⊆ M.branch i ∪ M.branch j :=
  Classical.choose_spec (M.exists_pairPath hij)

end RootedMinorModel

end HadwigerLean
