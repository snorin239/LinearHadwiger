import HadwigerLean.Graph.RootedDensity.TorsoPieceConnected
import Mathlib.Tactic

/-!
# Center and hanger pieces partition each touching torso branch

Every vertex of a touching branch belongs to exactly one real-edge
forest component: its root center or a uniquely indexed hanger. The
global hanger index records the touching branch that owns it.
-/

namespace HadwigerLean.RootedDensity

universe u v

theorem torsoCenterPiece_subset_branch
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (t : TorsoTouchIndex S M) :
    torsoCenterPiece G S H root M hmin t ⊆ M.branch t.1 := by
  rintro x ⟨z,_,rfl⟩
  exact z.2

theorem torsoHangerPiece_subset_branch
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (w : TorsoHangerIndex G S H root M hmin) :
    torsoHangerPiece G S H root M hmin w ⊆
      M.branch (torsoHangerOwner G S H root M hmin w) := by
  rintro x ⟨z,_,rfl⟩
  exact z.2

theorem torsoCenterPiece_root_mem
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (t : TorsoTouchIndex S M) :
    root t.1 ∈ torsoCenterPiece G S H root M hmin t :=
  ⟨⟨root t.1,M.root_mem t.1⟩,
    (chosenTorsoStar G S H root M hmin t).root_center,rfl⟩

theorem torsoCenterBoundary_mem_piece
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (t : TorsoTouchIndex S M) :
    torsoCenterBoundary G S H root M hmin t ∈
      torsoCenterPiece G S H root M hmin t :=
  ⟨(chosenTorsoStar G S H root M hmin t).center,
    starPiece_self _ _,rfl⟩

theorem torsoHangerBoundary_mem_piece
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (w : TorsoHangerIndex G S H root M hmin) :
    torsoHangerBoundary G S H root M hmin w ∈
      torsoHangerPiece G S H root M hmin w :=
  ⟨w.2.1,starPiece_self _ _,rfl⟩

theorem torsoTouchBranch_piece_cover
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (t : TorsoTouchIndex S M)
    {x : S.left} (hx : x ∈ M.branch t.1) :
    x ∈ torsoCenterPiece G S H root M hmin t ∨
      ∃ w : TorsoHangerIndex G S H root M hmin,
        torsoHangerOwner G S H root M hmin w = t.1 ∧
        x ∈ torsoHangerPiece G S H root M hmin w := by
  let A := chosenTorsoStar G S H root M hmin t
  let v : M.branch t.1 := ⟨x,hx⟩
  obtain ⟨z,hz,hvz⟩ := starPiece_cover A.forest
    {z : M.branch t.1 | ((z.1 : S.left) : V) ∈ S.right}
    A.unique_boundary v
  by_cases hzc : z = A.center
  · left
    refine ⟨v,?_,rfl⟩
    simpa only [hzc] using hvz
  · right
    let w : TorsoHangerIndex G S H root M hmin :=
      ⟨t,⟨z,⟨hz,hzc⟩⟩⟩
    refine ⟨w,rfl,?_⟩
    exact ⟨v,hvz,rfl⟩

end HadwigerLean.RootedDensity
