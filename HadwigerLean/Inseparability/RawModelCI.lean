import HadwigerLean.Inseparability.RawModelPieces
import HadwigerLean.Inseparability.RawModelDisjointness
import HadwigerLean.Inseparability.RawModelStage
import Mathlib.Tactic

/-!
# Nonzero CI stage model from old and child models

The terminal owner map chooses one branch for every path. The old
model and the p rooted child models provide all clique edges.
The remaining assumptions express the cleaned geometric placement of
the paths and connected D patches; this theorem verifies the assembled
model, its exact H3 tangency, and its new core.
-/

namespace HadwigerLean.Inseparability

universe u

abbrev CIRawIndex (p x : ℕ) :=
  Sum (Fin p × Fin x) (Fin x)

abbrev CIPathIndex (p x : ℕ) :=
  Fin ((4 * p + 1) * x)

/-- The geometric nonzero CI stage, after disjoint paths and central
knitting patches have been chosen. -/
theorem ci_nonzero_raw_model
    {V : Type u} (p x : ℕ) (hp : 0 < p)
    (G : SimpleGraph V)
    (A : MinorModel (SimpleGraph.completeGraph (Fin p × Fin x)) G)
    (M : Fin p → MinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G)
    (C : CIRawIndex p x → Set V)
    (P : CIPathIndex p x → Set V)
    (root : CIRawIndex p x → V) (H core : Set V)
    (hC : ∀ z, (G.induce (C z)).Connected)
    (hP : ∀ k, (G.induce (P k)).Connected)
    (hPmeet : ∀ k,
      ∃ v, v ∈ C (pathOwner p x k) ∧ v ∈ P k)
    (hAttach : ∀ z j, j ∈ ciExtraIndex p x z →
      ∃ k : CIPathIndex p x,
        pathOwner p x k = z ∧
        ∃ v, v ∈ P k ∧ v ∈ ciExtraPiece p x A M z j)
    (hCC : ∀ z w, z ≠ w → Disjoint (C z) (C w))
    (hCE : ∀ z w, z ≠ w →
      ∀ j ∈ ciExtraIndex p x w,
        Disjoint (C z) (ciExtraPiece p x A M w j))
    (hAChild : ∀ i, Disjoint A.vertices (M i).vertices)
    (hChildChild : ∀ i j, i ≠ j →
      Disjoint (M i).vertices (M j).vertices)
    (hPC : ∀ k z, pathOwner p x k ≠ z →
      Disjoint (P k) (C z))
    (hPE : ∀ k z, pathOwner p x k ≠ z →
      ∀ j ∈ ciExtraIndex p x z,
        Disjoint (P k) (ciExtraPiece p x A M z j))
    (hPP : ∀ k l, k ≠ l → Disjoint (P k) (P l))
    (hRootPath : ∀ z, root z ∈ assignedPaths (pathOwner p x) P z)
    (hBaseH : ∀ z,
      Disjoint (branchBase C (ciExtraPiece p x A M)
        (ciExtraIndex p x) z) H)
    (hPathH : ∀ z,
      assignedPaths (pathOwner p x) P z ∩ H = {root z})
    (hRootCore : ∀ z, root z ∈ core)
    (hOldCore : ∀ z w, z ≠ w →
      ∃ a ∈ A.branch z, ∃ b ∈ A.branch w,
        a ∈ core ∧ b ∈ core ∧ G.Adj a b)
    (hChildCore : ∀ i z, (M i).branch z ⊆ core) :
    ∃ N : RootedMinorModel
        (SimpleGraph.completeGraph (CIRawIndex p x)) G root,
      (∀ z, N.branch z =
        assembledBranch C P (pathOwner p x)
          (ciExtraPiece p x A M) (ciExtraIndex p x) z) ∧
      (∀ z, N.branch z ∩ H = {root z}) ∧
      (∀ z w, z ≠ w →
        ∃ a ∈ N.branch z, ∃ b ∈ N.branch w,
          a ∈ core ∧ b ∈ core ∧ G.Adj a b) ∧
      N.toMinorModel.vertices ∩ H ⊆ core := by
  classical
  apply assemble_raw_rooted_clique_model
    G C P (pathOwner p x) (ciExtraPiece p x A M)
      (ciExtraIndex p x) root H core hC hP hPmeet
  · exact ci_extra_connected p x A M
  · exact extra_meet_of_path_attachment C P
      (pathOwner p x) (ciExtraPiece p x A M)
      (ciExtraIndex p x) hAttach
  · exact branchBase_disjoint_of_pieces C
      (ciExtraPiece p x A M) (ciExtraIndex p x)
      hCC hCE
      (ci_extra_cross_disjoint p x A M hAChild hChildChild)
  · exact path_base_disjoint_of_pieces C P
      (ciExtraPiece p x A M) (ciExtraIndex p x)
      (pathOwner p x) hPC hPE
  · exact hPP
  · exact hRootPath
  · exact hBaseH
  · exact hPathH
  · exact hRootCore
  · exact ci_nonzero_stage_base_witness p x hp A M C core
      hOldCore hChildCore

end HadwigerLean.Inseparability
