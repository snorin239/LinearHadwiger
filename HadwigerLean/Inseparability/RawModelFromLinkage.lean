import HadwigerLean.Inseparability.KnittingInside
import HadwigerLean.Inseparability.RawModelPathAvoidance
import HadwigerLean.Woven.ManyChildRerouting
import Mathlib.Tactic

/-!
# CI raw model from one clean rerouted linkage

This theorem applies knitting to the distinct path ends in D and then
uses the old and child rooted models to assemble the next clique model.
The remaining geometric hypotheses are the clean interactions of the
linkage with D and H3 and the separation of D from the old/child pieces.
-/

namespace HadwigerLean.Inseparability

theorem ci_nonzero_raw_model_from_linkage
    {V : Type*} [Fintype V] [DecidableEq V]
    (p x : ℕ) (hp : 0 < p)
    (G : SimpleGraph V)
    (D : Finset V)
    (hDconn : VertexConnected (G.induce (D : Set V))
      (33 * ((4 * p + 1) * x)))
    (oldRoot : Fin p × Fin x → V)
    (A : RootedMinorModel
      (SimpleGraph.completeGraph (Fin p × Fin x)) G oldRoot)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (M : ∀ i, RootedMinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G (childRoot i))
    {P : IndexedPairs (CIPathIndex p x) V}
    (L : IndexedLinkage G P)
    (root : CIRawIndex p x → V) (H core : Set V)
    (hFinishD : ∀ k, P.finish k ∈ D)
    (hCleanD : ∀ k v,
      v ∈ pathVertexSet (L.path k) → v ∈ D → v = P.finish k)
    (hExtraD : ∀ z j, j ∈ ciExtraIndex p x z →
      Disjoint
        (ciExtraPiece p x A.toMinorModel
          (fun i => (M i).toMinorModel) z j)
        (D : Set V))
    (hExtraH : ∀ z j, j ∈ ciExtraIndex p x z →
      Disjoint
        (ciExtraPiece p x A.toMinorModel
          (fun i => (M i).toMinorModel) z j) H)
    (hDH : Disjoint (D : Set V) H)
    (hAChild : ∀ i,
      Disjoint A.toMinorModel.vertices (M i).toMinorModel.vertices)
    (hChildChild : ∀ i j, i ≠ j →
      Disjoint (M i).toMinorModel.vertices
        (M j).toMinorModel.vertices)
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
      childRoot i (1,r) ∈ P.terminals (ciNewMiddleIndex p x i r))
    (hFinalRoot : ∀ z,
      root z ∈ pathVertexSet (L.path (ciFinalIndex p x z)))
    (hRootH : ∀ z, root z ∈ H)
    (hCleanH : ∀ k v,
      v ∈ pathVertexSet (L.path k) → v ∈ H →
      v = root (pathOwner p x k))
    (hRootCore : ∀ z, root z ∈ core)
    (hOldCore : ∀ z w, z ≠ w →
      ∃ a ∈ A.branch z, ∃ b ∈ A.branch w,
        a ∈ core ∧ b ∈ core ∧ G.Adj a b)
    (hChildCore : ∀ i z, (M i).branch z ⊆ core) :
    ∃ N : RootedMinorModel
        (SimpleGraph.completeGraph (CIRawIndex p x)) G root,
      (∀ z, N.branch z ∩ H = {root z}) ∧
      (∀ z w, z ≠ w →
        ∃ a ∈ N.branch z, ∃ b ∈ N.branch w,
          a ∈ core ∧ b ∈ core ∧ G.Adj a b) ∧
      N.toMinorModel.vertices ∩ H ⊆ core := by
  classical
  obtain ⟨C,hCconn,hCdis,hCover,hCsub⟩ :=
    ci_knitting_inside G p x D P.finish hFinishD
      L.finish_injective hDconn
  have hPmeet : ∀ k,
      ∃ v, v ∈ C (pathOwner p x k) ∧
        v ∈ pathVertexSet (L.path k) := by
    intro k
    exact ⟨P.finish k,hCover k,pathVertexSet.finish_mem (L.path k)⟩
  have hAttach : ∀ z j, j ∈ ciExtraIndex p x z →
      ∃ k : CIPathIndex p x,
        pathOwner p x k = z ∧
        ∃ v, v ∈ pathVertexSet (L.path k) ∧
          v ∈ ciExtraPiece p x A.toMinorModel
            (fun i => (M i).toMinorModel) z j := by
    apply ci_extra_piece_meets_assigned_path p x G oldRoot A childRoot M
      (fun k => pathVertexSet (L.path k))
    · intro i r
      exact L.terminal_subset_path _ (hOldTerm i r)
    · intro i r
      exact L.terminal_subset_path _ (hChildOldTerm i r)
    · intro i r
      exact L.terminal_subset_path _ (hChildNewTerm i r)
  have hCE : ∀ z w, z ≠ w →
      ∀ j ∈ ciExtraIndex p x w,
        Disjoint (C z)
          (ciExtraPiece p x A.toMinorModel
            (fun i => (M i).toMinorModel) w j) := by
    intro z w _ j hj
    apply Set.disjoint_left.mpr
    intro v hvC hvE
    exact (Set.disjoint_left.mp (hExtraD w j hj))
      hvE (hCsub z hvC)
  have hPC : ∀ k z, pathOwner p x k ≠ z →
      Disjoint (pathVertexSet (L.path k)) (C z) := by
    intro k z hkz
    apply Set.disjoint_left.mpr
    intro v hvP hvC
    have hvD : v ∈ D := hCsub z hvC
    have heq := hCleanD k v hvP hvD
    subst v
    exact (Set.disjoint_left.mp (hCdis z (pathOwner p x k) hkz.symm))
      hvC (hCover k)
  have hPE : ∀ k z, pathOwner p x k ≠ z →
      ∀ j ∈ ciExtraIndex p x z,
        Disjoint (pathVertexSet (L.path k))
          (ciExtraPiece p x A.toMinorModel
            (fun i => (M i).toMinorModel) z j) :=
    ci_path_disjoint_wrong_extra_piece p x G oldRoot A childRoot M L
      hOldExact hChildExact hOldTerm hChildOldTerm hChildNewTerm
  have hBaseH : ∀ z,
      Disjoint
        (branchBase C
          (ciExtraPiece p x A.toMinorModel
            (fun i => (M i).toMinorModel))
          (ciExtraIndex p x) z) H := by
    intro z
    apply Set.disjoint_left.mpr
    intro v hvB hvH
    rcases hvB with hvC | hvE
    · exact (Set.disjoint_left.mp hDH) (hCsub z hvC) hvH
    · obtain ⟨j,hj,hvEj⟩ := by
        simpa [extraPieces] using hvE
      exact (Set.disjoint_left.mp (hExtraH z j hj)) hvEj hvH
  have hFinalPath : ∀ z,
      root z ∈ pathVertexSet (L.path (ciFinalIndex p x z)) :=
    hFinalRoot
  have hRootPath :=
    ci_root_mem_assignedPaths p x
      (fun k => pathVertexSet (L.path k)) root hFinalPath
  have hPathH :=
    ci_assignedPaths_tangent p x
      (fun k => pathVertexSet (L.path k)) root H
      hFinalPath hRootH hCleanH
  obtain ⟨N,_,hNTangent,hNWitness,hNCore⟩ :=
    ci_nonzero_raw_model p x hp G
      A.toMinorModel (fun i => (M i).toMinorModel)
      C (fun k => pathVertexSet (L.path k))
      root H core hCconn
      (fun k => (L.path k : G.Walk (P.start k) (P.finish k)).connected_induce_support)
      hPmeet hAttach hCdis hCE hAChild hChildChild hPC hPE
      L.disjoint hRootPath hBaseH hPathH hRootCore
      hOldCore hChildCore
  exact ⟨N,hNTangent,hNWitness,hNCore⟩

end HadwigerLean.Inseparability
