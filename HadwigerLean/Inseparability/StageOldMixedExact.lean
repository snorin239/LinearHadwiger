import HadwigerLean.Inseparability.StageOldIntersection
import HadwigerLean.Inseparability.StageMixedIndexed

/-!
# Exact old-model intersection with the mixed CI linkage

All mixed paths stay in the old chromatic region, where each old branch
has exactly its old root. The old-start slots put every such root on a
path, so the global model-linkage intersection is exact.
-/

namespace HadwigerLean.Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ci_mixed_old_model_intersection
    (p x : ℕ) (G : SimpleGraph V)
    (R W : Finset V)
    (oldRoot : Fin p × Fin x → V)
    (A : RootedMinorModel
      (SimpleGraph.completeGraph (Fin p × Fin x)) G oldRoot)
    {P : IndexedPairs (CIPathIndex p x) V}
    (L : IndexedLinkage G P)
    (Fvertices : Finset V)
    (hFR : Fvertices ⊆ R)
    (hSupport : ∀ k, pathVertexSet (L.path k) ⊆
      (Fvertices : Set V) ∪ ((R \ W : Finset V) : Set V))
    (htangent : ∀ z, A.branch z ∩ (R : Set V) = {oldRoot z})
    (hOldStart : ∀ i r,
      P.start (ciOldStartIndex p x i r) = oldRoot (i,r)) :
    A.toMinorModel.vertices ∩ L.vertices = Set.range oldRoot := by
  have hLR : L.vertices ⊆ (R : Set V) := by
    intro v hv
    obtain ⟨k,hvk⟩ := Set.mem_iUnion.mp hv
    rcases hSupport k hvk with hvF | hvRW
    · exact hFR hvF
    · exact (Finset.mem_sdiff.mp hvRW).1
  have hroots : Set.range oldRoot ⊆ L.vertices := by
    rintro v ⟨⟨i,r⟩,rfl⟩
    rw [← hOldStart i r]
    exact L.start_mem_vertices (ciOldStartIndex p x i r)
  exact rooted_model_exact_inter_linkage_of_region A L
    (R : Set V) htangent hLR hroots

end HadwigerLean.Inseparability
