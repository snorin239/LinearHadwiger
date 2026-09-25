import HadwigerLean.Graph.RootedDensity.TorsoHangerWitness
import Mathlib.Tactic

/-!
# Choosing all torso branch star decompositions

For each branch of a minimal rooted torso model that meets the
adhesion, choose the real-edge forest and root-center supplied by the
hanger-witness theorem. This dependent structure is the input to the
global matching relation.
-/

namespace HadwigerLean.RootedDensity

universe u v

def ModelTouchesBoundary
    {V : Type u} {I : Type v} [Fintype V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    {H : SimpleGraph I} {root : I → S.left}
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (i : I) : Prop :=
  ∃ b ∈ M.branch i, (b : V) ∈ S.right

structure TorsoBranchStarData
    {V : Type u} {I : Type v} [Fintype V]
    (G : SimpleGraph V) (S : VertexSeparation G)
    {H : SimpleGraph I} {root : I → S.left}
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (i : I) where
  forest : SimpleGraph (M.branch i)
  forest_near : forest ≤
    (G.induce S.left).induce (M.branch i)
  unique_boundary : ∀ v : M.branch i,
    ∃! z : M.branch i,
      ((z.1 : S.left) : V) ∈ S.right ∧
        forest.Reachable v z
  center : M.branch i
  center_boundary : ((center.1 : S.left) : V) ∈ S.right
  root_center :
    (⟨root i,M.root_mem i⟩ : M.branch i) ∈
      starPiece forest center
  hanger_witness : ∀ drop : M.branch i,
    ((drop.1 : S.left) : V) ∈ S.right →
    drop ≠ center →
      ∃ j : I, H.Adj i j ∧
        (∀ y ∈ M.branch j, (y : V) ∉ S.right) ∧
        ∃ x ∈
          (Subtype.val '' starPiece forest drop : Set S.left),
          ∃ y ∈ M.branch j, G.Adj (x : V) (y : V)

theorem exists_torso_branch_star_data
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (i : I) (htouch : ModelTouchesBoundary S M i) :
    Nonempty (TorsoBranchStarData G S M i) := by
  obtain ⟨F,hF,hU,c,hc,hr,hw⟩ :=
    exists_torso_model_hanger_witnesses G S H root M hmin
      i htouch
  exact ⟨{
    forest := F
    forest_near := hF
    unique_boundary := hU
    center := c
    center_boundary := hc
    root_center := hr
    hanger_witness := hw
  }⟩

noncomputable def chooseTorsoBranchStar
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (i : I) (htouch : ModelTouchesBoundary S M i) :
    TorsoBranchStarData G S M i :=
  Classical.choice
    (exists_torso_branch_star_data G S H root M hmin i htouch)

end HadwigerLean.RootedDensity
