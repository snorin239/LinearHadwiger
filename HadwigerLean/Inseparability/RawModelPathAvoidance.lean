import HadwigerLean.Inseparability.RawModelAttachment
import HadwigerLean.Woven.ModelLinkageExact
import Mathlib.Tactic

/-!
# Clean paths avoid supplementary pieces of other CI branches

Exact model-linkage intersection after child rerouting gives pathwise
avoidance. The terminal owner equations then show that a path can meet
an old or child model piece only when that piece belongs to its group.
-/

namespace HadwigerLean.Inseparability

theorem ci_path_disjoint_wrong_extra_piece
    {V : Type*} (p x : ℕ) (G : SimpleGraph V)
    (oldRoot : Fin p × Fin x → V)
    (A : RootedMinorModel
      (SimpleGraph.completeGraph (Fin p × Fin x)) G oldRoot)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (M : ∀ i, RootedMinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G (childRoot i))
    {P : IndexedPairs (CIPathIndex p x) V}
    (L : IndexedLinkage G P)
    (hOldExact : A.toMinorModel.vertices ∩ L.vertices =
      Set.range oldRoot)
    (hChildExact : ∀ i,
      (M i).toMinorModel.vertices ∩ L.vertices =
        Set.range (childRoot i))
    (hOldTerm : ∀ i r,
      oldRoot (i,r) ∈ P.terminals (ciOldStartIndex p x i r))
    (hChildOldTerm : ∀ i r,
      childRoot i (0,r) ∈ P.terminals (ciOldMiddleIndex p x i r))
    (hChildNewTerm : ∀ i r,
      childRoot i (1,r) ∈ P.terminals (ciNewMiddleIndex p x i r)) :
    ∀ k z, pathOwner p x k ≠ z →
      ∀ j ∈ ciExtraIndex p x z,
        Disjoint (pathVertexSet (L.path k))
          (ciExtraPiece p x A.toMinorModel
            (fun i => (M i).toMinorModel) z j) := by
  intro k z howner j hj
  cases z with
  | inl z =>
      obtain ⟨i,r⟩ := z
      have hslot : j = none ∨ j = some i := by
        simpa [ciExtraIndex] using hj
      rcases hslot with rfl | rfl
      · have hki : k ≠ ciOldStartIndex p x i r := by
          intro heq
          exact howner (heq ▸ pathOwner_old_start p x i r)
        exact (Woven.rooted_model_path_disjoint_of_other_index_single
          A L hOldExact (i,r) (ciOldStartIndex p x i r)
          k (hOldTerm i r) hki).symm
      · have hki : k ≠ ciOldMiddleIndex p x i r := by
          intro heq
          exact howner (heq ▸ pathOwner_old_middle p x i r)
        have hdis := (Woven.rooted_model_path_disjoint_of_other_index_single
          (M i) L (hChildExact i) (0,r)
          (ciOldMiddleIndex p x i r) k
          (hChildOldTerm i r) hki).symm
        change Disjoint (pathVertexSet (L.path k))
          (if i = i then (M i).branch (0,r) else ∅)
        rw [if_pos rfl]
        exact hdis
  | inr r =>
      cases j with
      | none => simp [ciExtraIndex] at hj
      | some i =>
          have hki : k ≠ ciNewMiddleIndex p x i r := by
            intro heq
            exact howner (heq ▸ pathOwner_new_middle p x i r)
          exact (Woven.rooted_model_path_disjoint_of_other_index_single
            (M i) L (hChildExact i) (1,r)
            (ciNewMiddleIndex p x i r) k
            (hChildNewTerm i r) hki).symm

end HadwigerLean.Inseparability
