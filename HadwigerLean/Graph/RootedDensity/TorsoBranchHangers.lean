import HadwigerLean.Graph.RootedDensity.TorsoStarBranch
import HadwigerLean.Graph.RootedDensity.StarPieceSubtype
import Mathlib.Tactic

/-!
# Rooted hanging pieces of a torso branch

A connected torso branch meeting the adhesion has a real-edge forest
decomposition. The component of the prescribed root determines a center
adhesion vertex. Deleting any other component leaves a connected torso
branch, still containing the root.
-/

namespace HadwigerLean.RootedDensity

universe u

theorem exists_torso_branch_hangers
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : VertexSeparation G)
    (B : Set S.left)
    (hBconn : ((Linkedness.torsoGraph G S).induce B).Connected)
    (boundary : B) (hboundary : (boundary.1 : V) ∈ S.right)
    (root : B) :
    let Z : Set B := {v | (v.1.1 : V) ∈ S.right}
    let K := Linkedness.torsoGraph G S
    let near := G.induce S.left
    ∃ F : SimpleGraph B,
      F ≤ near.induce B ∧
      (∀ v, ∃! z, z ∈ Z ∧ F.Reachable v z) ∧
      ∃ center : B,
        center ∈ Z ∧ root ∈ starPiece F center ∧
        ∀ drop : B, drop ∈ Z → drop ≠ center →
          let D : Set S.left := Subtype.val '' starPiece F drop
          D.Nonempty ∧ D ⊆ B ∧
          (K.induce (B \ D)).Connected ∧
          root.1 ∈ B \ D := by
  classical
  let Z : Set B := {v | (v.1.1 : V) ∈ S.right}
  let K := Linkedness.torsoGraph G S
  let near := G.induce S.left
  obtain ⟨T,hTK,hTree,hFNear,hUnique,_⟩ :=
    exists_torso_branch_star_decomposition G S B hBconn
      boundary.1 boundary.2 hboundary
  let F : SimpleGraph B :=
    T.deleteEdges (boundaryStarEdges Z boundary)
  have hFK : F ≤ K.induce B := by
    intro a b hab
    exact hTK (SimpleGraph.deleteEdges_adj.mp hab).1
  have hclique : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w →
      (K.induce B).Adj z w := by
    intro z hz w hw hzw
    change G.Adj (z.1.1 : V) (w.1.1 : V) ∨
      ((z.1.1 : V) ∈ S.right ∧
        (w.1.1 : V) ∈ S.right ∧ z.1 ≠ w.1)
    right
    refine ⟨hz,hw,?_⟩
    intro h
    exact hzw (Subtype.ext h)
  obtain ⟨center,⟨hc,hreach⟩,_⟩ := hUnique root
  have hroot : root ∈ starPiece F center :=
    (mem_starPiece_iff F root center).2 hreach
  refine ⟨F,hFNear,hUnique,center,hc,hroot,?_⟩
  intro drop hd hdc
  let D : Set S.left := Subtype.val '' starPiece F drop
  have hdropNonempty : D.Nonempty :=
    ⟨drop.1,drop,starPiece_self F drop,rfl⟩
  have hDsub : D ⊆ B := by
    rintro x ⟨v,_,rfl⟩
    exact v.2
  have hconn : (K.induce (B \ D)).Connected :=
    starPiece_delete_connected_ambient K B F Z hFK hUnique
      hclique center drop hc hd (Ne.symm hdc)
  have hrootNot : root.1 ∉ D := by
    rintro ⟨v,hv,heq⟩
    have hvr : v = root := Subtype.ext heq
    have hrootDrop : root ∈ starPiece F drop := hvr ▸ hv
    exact (Set.disjoint_left.mp
      (starPiece_pairwise_disjoint F Z hUnique hc hd
        (Ne.symm hdc))) hroot hrootDrop
  exact ⟨hdropNonempty,hDsub,hconn,⟨root.2,hrootNot⟩⟩

end HadwigerLean.RootedDensity
