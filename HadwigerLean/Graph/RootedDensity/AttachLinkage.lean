import HadwigerLean.Woven.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-! Attaching a minor model to prescribed roots by disjoint proxy paths. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- Disjoint root-to-proxy paths, each ending next to its assigned branch,
turn an unrooted `H` model into a rooted one. The path supports must avoid
all original branch sets. -/
theorem rootedMinor_of_minor_and_linkage
    {W : Type u} {V : Type v} {H : SimpleGraph W} {G : SimpleGraph V}
    {root : W → V} (M : MinorModel H G)
    (P : IndexedPairs W V) (L : IndexedLinkage G P)
    (hstart : ∀ i, P.start i = root i)
    (havoid : ∀ i j, Disjoint (M.branch i) (pathVertexSet (L.path j)))
    (hattach : ∀ i, ∃ x ∈ M.branch i, G.Adj x (P.finish i)) :
    Nonempty (RootedMinorModel H G root) := by
  let R (i : W) : Set V := M.branch i ∪ pathVertexSet (L.path i)
  have hpathConn (i : W) :
      (G.induce (pathVertexSet (L.path i))).Connected := by
    simpa only [pathVertexSet] using
      (L.path i : G.Walk (P.start i) (P.finish i)).connected_induce_support
  refine ⟨{
    branch := R
    connected := ?_
    disjoint := ?_
    adjacent := ?_
    root_mem := ?_
  }⟩
  · intro i
    obtain ⟨x, hx, hadj⟩ := hattach i
    exact G.connected_induce_union (M.connected i).preconnected
      (hpathConn i).preconnected hx
      (pathVertexSet.finish_mem (L.path i)) hadj
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    rcases hxi with hxi | hxi <;> rcases hxj with hxj | hxj
    · exact (Set.disjoint_left.mp (M.disjoint hij)) hxi hxj
    · exact (Set.disjoint_left.mp (havoid i j)) hxi hxj
    · exact (Set.disjoint_left.mp (havoid j i)) hxj hxi
    · exact (Set.disjoint_left.mp (L.disjoint hij)) hxi hxj
  · intro i j hij
    obtain ⟨x, hx, y, hy, hxy⟩ := M.adjacent hij
    exact ⟨x, Or.inl hx, y, Or.inl hy, hxy⟩
  · intro i
    exact Or.inr (hstart i ▸ pathVertexSet.start_mem (L.path i))

end HadwigerLean.RootedDensity
