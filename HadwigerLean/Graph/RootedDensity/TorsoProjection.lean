import HadwigerLean.Graph.RootedDensity.RigidGlue
import HadwigerLean.Graph.RootedCliqueMinor.SeparatorRestriction
import Mathlib.Tactic

/-!
# Forward projection of rooted models to a near-side torso

Restricting a connected branch to the near side preserves connectivity
when the adhesion is completed to a clique.  The rooted model follows by
restricting each branch and using the completed adhesion for edges whose
original witnesses lie in the far shore.
-/

namespace HadwigerLean.RootedDensity

universe u v

/-- Reverse the sides of a vertex separation. -/
def swapSeparation
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (S : VertexSeparation G) : VertexSeparation G where
  left := S.right
  right := S.left
  cover := by simpa only [Set.union_comm] using S.cover
  no_cross := by
    intro x y hxR hxNotL hyL hyNotR hxy
    exact S.no_cross hyL hyNotR hxR hxNotL hxy.symm

/-- The right-side torso of the reversed separation is the near-side
torso of the original separation. -/
theorem swapSeparation_torso_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : VertexSeparation G) :
    (swapSeparation S).torso = Linkedness.torsoGraph G S := by
  ext x y
  rfl

/-- A connected original branch that meets the near side remains connected
when restricted to the near-side torso. -/
theorem connected_restrict_near_torso
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : VertexSeparation G) (B : Set V)
    (hconn : (G.induce B).Connected)
    (hleft : ∃ x ∈ B, x ∈ S.left) :
    ((Linkedness.torsoGraph G S).induce
      {x : S.left | (x : V) ∈ B}).Connected := by
  let Q := swapSeparation S
  have h := Q.connected_restrict_torso B hconn hleft
  change ((swapSeparation S).torso.induce
    {x : S.left | (x : V) ∈ B}).Connected at h
  rw [swapSeparation_torso_eq G S] at h
  exact h

/-- Every rooted model whose prescribed roots lie on the near side projects
to a rooted model in the completed near-side torso. -/
theorem rooted_model_project_to_torso
    {V : Type u} {I : Type v} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : VertexSeparation G)
    (H : SimpleGraph I) (root : I → V)
    (M : RootedMinorModel H G root)
    (hroot : ∀ i, root i ∈ S.left) :
    Nonempty (RootedMinorModel H (Linkedness.torsoGraph G S)
      (fun i => (⟨root i, hroot i⟩ : S.left))) := by
  let Q := swapSeparation S
  let N : MinorModel H Q.torso :=
    Q.restrictMinorModel M.toMinorModel
      (fun i => ⟨root i, M.root_mem i, hroot i⟩)
  have htorso : Q.torso = Linkedness.torsoGraph G S :=
    swapSeparation_torso_eq G S
  refine ⟨{
    toMinorModel := htorso ▸ N
    root_mem := ?_
  }⟩
  intro i
  exact M.root_mem i

end HadwigerLean.RootedDensity