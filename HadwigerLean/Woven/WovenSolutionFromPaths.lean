import HadwigerLean.Woven.ModelPathExtension

import HadwigerLean.Woven.Basic

/-!
# A woven solution from a partitioned clean linkage

Some paths of a disjoint linkage carry external roots to a residual rooted
clique model. Other paths realize terminal pairs and avoid the residual
vertex set. Extending the model along the first paths yields exact zero
model-linkage intersection with the terminal paths.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} {G : SimpleGraph V}
  {a j m : ℕ} {P : IndexedPairs (Fin m) V}

/-- Reindex a disjoint linkage into root paths and terminal paths, then
extend a residual rooted model along the root paths. -/
theorem exists_woven_solution_of_partitioned_linkage
    (L : IndexedLinkage G P)
    (rootSlot : Fin a ↪ Fin m) (terminalSlot : Fin j ↪ Fin m)
    (hslots : ∀ i k, rootSlot i ≠ terminalSlot k)
    (U : Set V)
    (M : RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G
      (P.finish ∘ rootSlot))
    (hMsubset : ∀ i, M.branch i ⊆ U)
    (hrootClean : ∀ i v,
      v ∈ pathVertexSet (L.path (rootSlot i)) →
      v ∈ U → v = P.finish (rootSlot i))
    (hterminalAvoid : ∀ k v,
      v ∈ pathVertexSet (L.path (terminalSlot k)) → v ∉ U) :
    Nonempty (WovenSolution G (P.start ∘ rootSlot)
      (P.reindex terminalSlot)) := by
  let Pr : IndexedPairs (Fin a) V := P.reindex rootSlot
  let Lr : IndexedLinkage G Pr := L.reindex rootSlot
  let Pt : IndexedPairs (Fin j) V := P.reindex terminalSlot
  let Lt : IndexedLinkage G Pt := L.reindex terminalSlot
  let Mr : RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G
      (P.start ∘ rootSlot) :=
    RootedMinorModel.extendAlongCleanLinkage M Lr U hMsubset hrootClean
  have hleft : Mr.toMinorModel.vertices ∩ Lt.vertices = ∅ := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    intro hv
    obtain ⟨hvM,hvL⟩ := hv
    obtain ⟨i,hvi⟩ := Set.mem_iUnion.mp hvM
    obtain ⟨k,hvk⟩ := Set.mem_iUnion.mp hvL
    change v ∈ M.branch i ∪ pathVertexSet (L.path (rootSlot i)) at hvi
    change v ∈ pathVertexSet (L.path (terminalSlot k)) at hvk
    rcases hvi with hviM | hviP
    · exact hterminalAvoid k v hvk (hMsubset i hviM)
    · exact (Set.disjoint_left.mp (L.disjoint (hslots i k))) hviP hvk
  have hright : Set.range (P.start ∘ rootSlot) ∩
      Pt.allTerminals = ∅ := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    intro hv
    obtain ⟨⟨i,hi⟩,hvTerm⟩ := hv
    obtain ⟨k,hvk⟩ := Set.mem_iUnion.mp hvTerm
    have hstart : v ∈ pathVertexSet (L.path (rootSlot i)) := by
      rw [← hi]
      exact pathVertexSet.start_mem (L.path (rootSlot i))
    have hterm : v ∈ pathVertexSet (L.path (terminalSlot k)) := by
      exact Lt.terminal_subset_path k hvk
    exact (Set.disjoint_left.mp (L.disjoint (hslots i k))) hstart hterm
  exact ⟨{
    model := Mr
    linkage := Lt
    exact_intersection := hleft.trans hright.symm
  }⟩

end Woven
end HadwigerLean
