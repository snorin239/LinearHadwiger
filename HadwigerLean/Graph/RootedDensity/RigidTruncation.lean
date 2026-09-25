import HadwigerLean.Graph.RootedDensity.MassedStructure
import HadwigerLean.Graph.Linkedness.TorsoPathTrim
import Mathlib.Tactic

/-!
# Rigid truncation: real-edge pieces of a torso model

The torso differs from the induced near side only on pairs of adhesion
vertices. Branch sets with at most one adhesion vertex therefore have
identical internal graphs before and after torso completion.
-/

namespace HadwigerLean.RootedDensity

universe u v

/-- A set with at most one adhesion vertex has exactly the same induced
graph in the near-side torso and in the original near side. -/
theorem torso_induce_eq_near_of_unique_boundary
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : VertexSeparation G)
    (B : Set S.left)
    (hunique : ∀ x ∈ B, ∀ y ∈ B,
      (x : V) ∈ S.right → (y : V) ∈ S.right → x = y) :
    (Linkedness.torsoGraph G S).induce B =
      (G.induce S.left).induce B := by
  ext x y
  change (G.Adj (x.1 : V) (y.1 : V) ∨
    ((x.1 : V) ∈ S.right ∧ (y.1 : V) ∈ S.right ∧ x.1 ≠ y.1)) ↔
      G.Adj (x.1 : V) (y.1 : V)
  constructor
  · rintro (hreal | ⟨hx, hy, hne⟩)
    · exact hreal
    · exact False.elim (hne (hunique x.1 x.2 y.1 y.2 hx hy))
  · exact Or.inl

/-- Internal connectivity of a one-boundary branch survives removal of
all artificial torso edges. -/
theorem torso_branch_connected_near_of_unique_boundary
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : VertexSeparation G)
    (B : Set S.left)
    (hunique : ∀ x ∈ B, ∀ y ∈ B,
      (x : V) ∈ S.right → (y : V) ∈ S.right → x = y)
    (hconn : ((Linkedness.torsoGraph G S).induce B).Connected) :
    ((G.induce S.left).induce B).Connected := by
  rwa [torso_induce_eq_near_of_unique_boundary G S B hunique] at hconn

/-- A torso rooted model whose branches each use at most one adhesion
vertex and whose required inter-branch edges are real lifts unchanged to
the original graph. -/
theorem rooted_model_lift_torso_real_edges
    {V : Type u} {I : Type v} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : VertexSeparation G)
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hunique : ∀ i, ∀ x ∈ M.branch i, ∀ y ∈ M.branch i,
      (x : V) ∈ S.right → (y : V) ∈ S.right → x = y)
    (hadj : ∀ i j, H.Adj i j →
      ∃ x ∈ M.branch i, ∃ y ∈ M.branch j,
        G.Adj (x : V) (y : V)) :
    Nonempty (RootedMinorModel H G (Subtype.val ∘ root)) := by
  let N : RootedMinorModel H (G.induce S.left) root := {
    toMinorModel := {
      branch := M.branch
      connected := by
        intro i
        exact torso_branch_connected_near_of_unique_boundary
          G S (M.branch i) (hunique i) (M.connected i)
      disjoint := M.disjoint
      adjacent := by
        intro i j hij
        exact hadj i j hij
    }
    root_mem := M.root_mem
  }
  let f : (G.induce S.left) →g G := {
    toFun := Subtype.val
    map_rel' := by
      intro x y hxy
      exact hxy
  }
  exact ⟨N.map f Subtype.val_injective⟩


/-- Every target adjacency witnessed in a torso model is either a
real near-side edge or has an adhesion vertex in each branch. -/
theorem torso_model_edge_real_or_boundary
    {V : Type u} {I : Type v} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : VertexSeparation G)
    {H : SimpleGraph I} {root : I → S.left}
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    {i j : I} (hij : H.Adj i j) :
    (∃ x ∈ M.branch i, ∃ y ∈ M.branch j,
      G.Adj (x : V) (y : V)) ∨
    (∃ x ∈ M.branch i, ∃ y ∈ M.branch j,
      (x : V) ∈ S.right ∧ (y : V) ∈ S.right) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := M.adjacent hij
  rcases hxy with hreal | ⟨hxS, hyS, _⟩
  · exact Or.inl ⟨x, hx, y, hy, hreal⟩
  · exact Or.inr ⟨x, hx, y, hy, hxS, hyS⟩
end HadwigerLean.RootedDensity