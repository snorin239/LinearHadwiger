import HadwigerLean.Graph.RootedDensity.TorsoHangerMatching
import HadwigerLean.Graph.RootedDensity.RigidUnion
import Mathlib.Tactic

/-!
# Real connectedness of selected torso star pieces

Each selected center or hanger piece is connected using original graph
edges. The proof passes from a forest component inside a torso branch
through the near-side subtype and then into the original vertex type.
-/

namespace HadwigerLean.RootedDensity

universe u v

theorem torsoBranchPiece_connected_real
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : VertexSeparation G)
    (B : Set S.left) (F : SimpleGraph B)
    (hF : F ≤ (G.induce S.left).induce B)
    (z : B) :
    (G.induce
      (Subtype.val '' (Subtype.val '' starPiece F z : Set S.left))).Connected := by
  have hInside :
      (((G.induce S.left).induce B).induce
        (starPiece F z)).Connected :=
    starPiece_connected ((G.induce S.left).induce B)
      F hF z
  have hNear :
      ((G.induce S.left).induce
        (Subtype.val '' starPiece F z)).Connected :=
    connected_induce_subtype_image
      (G.induce S.left) B (starPiece F z) hInside
  exact connected_induce_subtype_image G S.left
    (Subtype.val '' starPiece F z) hNear

noncomputable def torsoCenterPiece
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (t : TorsoTouchIndex S M) : Set S.left :=
  Subtype.val '' starPiece
    (chosenTorsoStar G S H root M hmin t).forest
    (chosenTorsoStar G S H root M hmin t).center

theorem torsoCenterPiece_connected_real
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (t : TorsoTouchIndex S M) :
    (G.induce (Subtype.val ''
      torsoCenterPiece G S H root M hmin t)).Connected := by
  exact torsoBranchPiece_connected_real G S (M.branch t.1)
    (chosenTorsoStar G S H root M hmin t).forest
    (chosenTorsoStar G S H root M hmin t).forest_near
    (chosenTorsoStar G S H root M hmin t).center

theorem torsoHangerPiece_connected_real
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (w : TorsoHangerIndex G S H root M hmin) :
    (G.induce (Subtype.val ''
      torsoHangerPiece G S H root M hmin w)).Connected := by
  exact torsoBranchPiece_connected_real G S (M.branch w.1.1)
    (chosenTorsoStar G S H root M hmin w.1).forest
    (chosenTorsoStar G S H root M hmin w.1).forest_near
    w.2.1

end HadwigerLean.RootedDensity
