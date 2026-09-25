import HadwigerLean.Graph.RootedDensity.RigidFarImage
import HadwigerLean.Graph.RootedDensity.TorsoFreePiece
import HadwigerLean.Graph.RootedDensity.ColoredGlueConnectivity
import HadwigerLean.Graph.RootedDensity.ColoredGlueDisjoint

/-! Branch sets for colored reverse gluing of a rigid torso model. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- A touching branch retains its center and every color-2 hanger it owns,
plus the far branches attached at their adhesion vertices. A free branch
retains its original near piece; if color 1 matched it, the matched hanger
and its far branch are added. -/
noncomputable def torsoColoredBranch
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    [DecidableEq (TorsoHangerIndex G S H root M hmin)]
    [DecidableEq (TorsoFreeIndex S M)]
    (P : TwoColorMatching (TorsoHangerRel G S H root M hmin))
    (Y : Finset I) (q : ↥(Y : Set I) → S.right)
    (N : RootedMinorModel (H.induce (Y : Set I)) (G.induce S.right) q)
    (i : I) : Set V := by
  classical
  by_cases ht : ModelTouchesBoundary S M i
  · let t : TorsoTouchIndex S M := ⟨i,ht⟩
    exact (Subtype.val '' torsoCenterPiece G S H root M hmin t) ∪
      rigidFarBranchImage S Y N i ∪
      ⋃ u : ↥P.color2Left,
        if torsoHangerOwner G S H root M hmin u.1 = i then
          (Subtype.val '' torsoHangerPiece G S H root M hmin u.1) ∪
            rigidFarBranchImage S Y N (P.match2 u).1
        else ∅
  · let j : TorsoFreeIndex S M := ⟨i,ht⟩
    exact torsoFreePiece G S H root M j ∪
      if hj : j ∈ P.color1Right then
        (Subtype.val '' torsoHangerPiece G S H root M hmin
          (P.match1 ⟨j,hj⟩)) ∪ rigidFarBranchImage S Y N i
      else ∅

theorem torsoColoredBranch_root_mem
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    [DecidableEq (TorsoHangerIndex G S H root M hmin)]
    [DecidableEq (TorsoFreeIndex S M)]
    (P : TwoColorMatching (TorsoHangerRel G S H root M hmin))
    (Y : Finset I) (q : ↥(Y : Set I) → S.right)
    (N : RootedMinorModel (H.induce (Y : Set I)) (G.induce S.right) q)
    (i : I) :
    (root i : V) ∈ torsoColoredBranch G S H root M hmin P Y q N i := by
  classical
  by_cases ht : ModelTouchesBoundary S M i
  · have hroot := torsoCenterPiece_root_mem G S H root M hmin
      (⟨i,ht⟩ : TorsoTouchIndex S M)
    unfold torsoColoredBranch
    simp only [dif_pos ht]
    exact Or.inl (Or.inl ⟨root i,hroot,rfl⟩)
  · have hroot := torsoFreePiece_root_mem G S H root M
      (⟨i,ht⟩ : TorsoFreeIndex S M)
    unfold torsoColoredBranch
    simp only [dif_neg ht]
    exact Or.inl hroot

end HadwigerLean.RootedDensity

