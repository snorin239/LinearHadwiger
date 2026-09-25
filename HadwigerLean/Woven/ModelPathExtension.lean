import HadwigerLean.Graph.RootedMinor
import HadwigerLean.Graph.Linkedness.RegionLinkage

import HadwigerLean.Woven.HubInducedRouting

/-!
# Extending residual clique branches along clean paths

A rooted clique model in the residual graph is carried to external roots
by disjoint paths which meet the residual graph only at their finishes.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} {G : SimpleGraph V} {a : ℕ}
  {R : IndexedPairs (Fin a) V}

/-- Enlarge each residual branch by its disjoint incoming path. The new
model is rooted at the incoming starts. -/
def RootedMinorModel.extendAlongCleanLinkage
    (M : RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G R.finish)
    (L : IndexedLinkage G R) (U : Set V)
    (hMsubset : ∀ i, M.branch i ⊆ U)
    (hLclean : ∀ i v, v ∈ pathVertexSet (L.path i) →
      v ∈ U → v = R.finish i) :
    RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G R.start where
  branch := fun i => M.branch i ∪ pathVertexSet (L.path i)
  connected := by
    intro i
    have hB : (G.induce (M.branch i)).Connected := M.connected i
    have hP : (G.induce (pathVertexSet (L.path i))).Connected :=
      (L.path i : G.Walk (R.start i) (R.finish i)).connected_induce_support
    exact Linkedness.connected_induce_union_of_common hB hP
      (M.root_mem i) (pathVertexSet.finish_mem (L.path i))
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro v hvi hvj
    rcases hvi with hviM | hviL <;> rcases hvj with hvjM | hvjL
    · exact (Set.disjoint_left.mp (M.disjoint hij)) hviM hvjM
    · have hvU : v ∈ U := hMsubset i hviM
      have hlast : v = R.finish j := hLclean j v hvjL hvU
      have hvjM : v ∈ M.branch j := by
        simpa [hlast] using M.root_mem j
      exact (Set.disjoint_left.mp (M.disjoint hij)) hviM hvjM
    · have hvU : v ∈ U := hMsubset j hvjM
      have hlast : v = R.finish i := hLclean i v hviL hvU
      have hviM : v ∈ M.branch i := by
        simpa [hlast] using M.root_mem i
      exact (Set.disjoint_left.mp (M.disjoint hij)) hviM hvjM
    · exact (Set.disjoint_left.mp (L.disjoint hij)) hviL hvjL
  adjacent := by
    intro i j hij
    obtain ⟨x,hxi,y,hyj,hxy⟩ := M.adjacent hij
    exact ⟨x,Or.inl hxi,y,Or.inl hyj,hxy⟩
  root_mem := by
    intro i
    exact Or.inr (pathVertexSet.start_mem (L.path i))

end Woven
end HadwigerLean
