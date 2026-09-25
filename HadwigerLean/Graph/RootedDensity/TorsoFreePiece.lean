import HadwigerLean.Graph.RootedDensity.TorsoPieceAdjacency
import HadwigerLean.Graph.RootedDensity.RigidUnion
import Mathlib.Tactic

/-!
# Real connectedness of boundary-free torso branches

A branch avoiding the adhesion has no artificial torso edges, so its
original near-side vertex set is connected. Its image in the original
graph is the free branch base for reverse gluing.
-/

namespace HadwigerLean.RootedDensity

universe u v

def torsoFreePiece
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (j : TorsoFreeIndex S M) : Set V :=
  Subtype.val '' M.branch j.1

theorem torsoFreePiece_connected_real
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (j : TorsoFreeIndex S M) :
    (G.induce (torsoFreePiece G S H root M j)).Connected := by
  have hUnique : ∀ x ∈ M.branch j.1, ∀ y ∈ M.branch j.1,
      (x : V) ∈ S.right → (y : V) ∈ S.right → x = y := by
    intro x hx y hy hxS _
    exact (j.2 ⟨x,hx,hxS⟩).elim
  have hNear :
      ((G.induce S.left).induce (M.branch j.1)).Connected :=
    torso_branch_connected_near_of_unique_boundary
      G S (M.branch j.1) hUnique (M.connected j.1)
  exact connected_induce_subtype_image
    G S.left (M.branch j.1) hNear

theorem torsoFreePiece_root_mem
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (j : TorsoFreeIndex S M) :
    (root j.1 : V) ∈ torsoFreePiece G S H root M j :=
  ⟨root j.1,M.root_mem j.1,rfl⟩

theorem torsoFreePiece_avoids_right
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (j : TorsoFreeIndex S M) :
    Disjoint (torsoFreePiece G S H root M j) S.right := by
  apply Set.disjoint_left.mpr
  rintro x ⟨y,hy,rfl⟩ hxS
  exact j.2 ⟨y,hy,hxS⟩

end HadwigerLean.RootedDensity
