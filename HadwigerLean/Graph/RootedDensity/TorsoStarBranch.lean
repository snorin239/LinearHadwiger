import HadwigerLean.Graph.RootedDensity.StarForest
import HadwigerLean.Graph.RootedDensity.RigidTruncation
import Mathlib.Tactic

/-!
# Real-edge star pieces of one torso branch

A connected torso branch meeting the adhesion is partitioned by a
spanning tree into real-edge components. Each component contains
exactly one adhesion vertex. This is the branch-level input for
multiboundary rigid truncation.
-/

namespace HadwigerLean.RootedDensity

universe u

theorem exists_torso_branch_star_decomposition
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : VertexSeparation G)
    (B : Set S.left)
    (hBconn : ((Linkedness.torsoGraph G S).induce B).Connected)
    (center : S.left) (hcenterB : center ∈ B)
    (hcenterS : (center : V) ∈ S.right) :
    let Z : Set B := {v | ((v.1 : S.left) : V) ∈ S.right}
    let K := (Linkedness.torsoGraph G S).induce B
    let near := (G.induce S.left).induce B
    ∃ T : SimpleGraph B,
      T ≤ K ∧ T.IsTree ∧
      let F := T.deleteEdges
        (boundaryStarEdges Z (⟨center,hcenterB⟩ : B))
      F ≤ near ∧
      (∀ v, ∃! z, z ∈ Z ∧ F.Reachable v z) ∧
      (∀ v,
        (near.induce
          ((F.connectedComponentMk v).supp : Set B)).Connected) := by
  classical
  let Z : Set B := {v | ((v.1 : S.left) : V) ∈ S.right}
  let K := (Linkedness.torsoGraph G S).induce B
  let near := (G.induce S.left).induce B
  let c : B := ⟨center,hcenterB⟩
  have hcZ : c ∈ Z := hcenterS
  have hstar : ∀ z ∈ Z, z ≠ c → K.Adj c z := by
    intro z hz hzc
    change (G.Adj (center : V) (z.1.1 : V) ∨
      ((center : V) ∈ S.right ∧ (z.1.1 : V) ∈ S.right ∧
        center ≠ z.1))
    right
    refine ⟨hcenterS,hz,?_⟩
    intro heq
    exact hzc (Subtype.ext heq.symm)
  have hfake : ∀ a b, K.Adj a b →
      near.Adj a b ∨ (a ∈ Z ∧ b ∈ Z) := by
    intro a b hab
    change (G.Adj (a.1.1 : V) (b.1.1 : V) ∨
      ((a.1.1 : V) ∈ S.right ∧
        (b.1.1 : V) ∈ S.right ∧ a.1 ≠ b.1)) at hab
    rcases hab with hreal | ⟨ha,hb,_⟩
    · exact Or.inl hreal
    · exact Or.inr ⟨ha,hb⟩
  exact exists_star_forest_real_decomposition
    K near Z c hcZ hBconn hstar hfake

end HadwigerLean.RootedDensity
