import HadwigerLean.Graph.RootedDensity.TorsoBranchHangers
import HadwigerLean.Graph.RootedDensity.RootedHangerWitness
import Mathlib.Tactic

/-!
# Hanger witnesses in a minimal rooted torso model

Every hanging piece of a branch-minimal torso model has a real
witnessing edge into a target-adjacent branch that avoids the adhesion.
This is the bipartite relation used by the two-color matching device.
-/

namespace HadwigerLean.RootedDensity

universe u v

theorem exists_torso_model_hanger_witnesses
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (i : I)
    (htouch : ∃ b ∈ M.branch i, (b : V) ∈ S.right) :
    let B := M.branch i
    let Z : Set B := {v | (v.1 : V) ∈ S.right}
    ∃ F : SimpleGraph B,
      F ≤ (G.induce S.left).induce B ∧
      (∀ v, ∃! z, z ∈ Z ∧ F.Reachable v z) ∧
      ∃ center : B,
        center ∈ Z ∧
        (⟨root i,M.root_mem i⟩ : B) ∈ starPiece F center ∧
        ∀ drop : B, drop ∈ Z → drop ≠ center →
          ∃ j : I, H.Adj i j ∧
            (∀ y ∈ M.branch j, (y : V) ∉ S.right) ∧
            ∃ x ∈ (Subtype.val '' starPiece F drop : Set S.left),
              ∃ y ∈ M.branch j, G.Adj (x : V) (y : V) := by
  classical
  let K := Linkedness.torsoGraph G S
  let B := M.branch i
  let Z : Set B := {v | (v.1 : V) ∈ S.right}
  obtain ⟨b,hb,hbS⟩ := htouch
  let boundary : B := ⟨b,hb⟩
  let r : B := ⟨root i,M.root_mem i⟩
  obtain ⟨F,hFNear,hUnique,center,hcenterZ,hrootCenter,hhang⟩ :=
    exists_torso_branch_hangers G S B (M.connected i)
      boundary hbS r
  have hclique : ∀ z : S.left,
      (z : V) ∈ S.right →
      ∀ w : S.left, (w : V) ∈ S.right →
      z ≠ w → K.Adj z w := by
    intro z hz w hw hzw
    change G.Adj (z : V) (w : V) ∨
      ((z : V) ∈ S.right ∧ (w : V) ∈ S.right ∧ z ≠ w)
    exact Or.inr ⟨hz,hw,hzw⟩
  refine ⟨F,hFNear,hUnique,center,hcenterZ,hrootCenter,?_⟩
  intro drop hdropZ hdc
  let D : Set S.left := Subtype.val '' starPiece F drop
  obtain ⟨hDnonempty,hDsub,hCconn,hrootC⟩ :=
    hhang drop hdropZ hdc
  have hcenterNotD : center.1 ∉ D := by
    rintro ⟨v,hv,heq⟩
    have hvc : v = center := Subtype.ext heq
    have hcenterDrop : center ∈ starPiece F drop :=
      hvc ▸ hv
    exact (Set.disjoint_left.mp
      (starPiece_pairwise_disjoint F Z hUnique
        hcenterZ hdropZ (Ne.symm hdc)))
      (starPiece_self F center) hcenterDrop
  have hcenterRetained : center.1 ∈ B \ D :=
    ⟨center.2,hcenterNotD⟩
  obtain ⟨j,hij,hfree,x,hx,y,hy,hxy⟩ :=
    minimal_hanger_has_boundary_free_neighbor M hmin
      {z : S.left | (z : V) ∈ S.right}
      (by
        intro z hz w hw hzw
        exact hclique z hz w hw hzw)
      i D hDsub hDnonempty hCconn hrootC
      ⟨center.1,hcenterRetained,hcenterZ⟩
  refine ⟨j,hij,hfree,x,hx,y,hy,?_⟩
  rcases hxy with hreal | ⟨_,hyS,_⟩
  · exact hreal
  · exact (hfree y hy hyS).elim

end HadwigerLean.RootedDensity
