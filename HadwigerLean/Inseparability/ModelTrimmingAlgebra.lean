import HadwigerLean.Inseparability.CoreColor
import HadwigerLean.Inseparability.Stages
import Mathlib.Tactic

/-!
# Restricting rooted clique models to smaller connected branches

This is the algebraic half of the branch-trimming step. The cheap-tree
argument supplies connected `Q i` through the old core; this file verifies
that those sets still form a rooted model and preserve the stage interface.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {s k m coreBound : ℕ}

/-- Restrict each branch of a rooted clique model to a connected subset that
contains its root and every core vertex of the original branch. -/
def rootedModel_restrict_through_core
    (root : Fin s → V)
    (M : RootedMinorModel (SimpleGraph.completeGraph (Fin s)) G root)
    (core : Finset V)
    (hrootcore : ∀ i, root i ∈ core)
    (hwitness : ∀ i j, i ≠ j →
      ∃ x ∈ M.branch i, ∃ y ∈ M.branch j,
        x ∈ core ∧ y ∈ core ∧ G.Adj x y)
    (Q : Fin s → Finset V)
    (hQsub : ∀ i, (Q i : Set V) ⊆ M.branch i)
    (hQconn : ∀ i, (G.induce (Q i : Set V)).Connected)
    (hcoreQ : ∀ i v, v ∈ M.branch i → v ∈ core → v ∈ Q i) :
    RootedMinorModel (SimpleGraph.completeGraph (Fin s)) G root where
  toMinorModel := {
    branch := fun i => (Q i : Set V)
    connected := hQconn
    disjoint := by
      intro i j hij
      exact (M.disjoint hij).mono (hQsub i) (hQsub j)
    adjacent := by
      intro i j hij
      obtain ⟨x, hx, y, hy, hxc, hyc, hxy⟩ :=
        hwitness i j (by simpa using hij)
      exact ⟨x, hcoreQ i x hx hxc,
        y, hcoreQ j y hy hyc, hxy⟩
  }
  root_mem := by
    intro i
    exact hcoreQ i (root i) (M.root_mem i) (hrootcore i)

/-- The restricted model retains the unique tangencies and core witnesses
of a stage, provided each root is its region tangency. -/
def stage_of_restricted_model
    (S : StageState G s k m coreBound)
    (hrootcore : ∀ i, S.root i ∈ S.core)
    (hrootregion : ∀ i, S.root i ∈ S.region)
    (Q : Fin s → Finset V)
    (hQsub : ∀ i, (Q i : Set V) ⊆ S.model.branch i)
    (hQconn : ∀ i, (G.induce (Q i : Set V)).Connected)
    (hcoreQ : ∀ i v, v ∈ S.model.branch i → v ∈ S.core → v ∈ Q i) :
    StageState G s k m coreBound := by
  let M := rootedModel_restrict_through_core S.root S.model S.core
    hrootcore S.core_witness Q hQsub hQconn hcoreQ
  refine {
    root := S.root
    root_injective := S.root_injective
    model := M
    core := S.core
    region := S.region
    region_connected := S.region_connected
    chromatic_reserve := S.chromatic_reserve
    core_card_le := S.core_card_le
    tangent := ?_
    intersection_in_core := ?_
    core_witness := ?_
  }
  · intro i
    refine ⟨S.root i, ⟨M.root_mem i, hrootregion i⟩, ?_⟩
    intro v hv
    obtain ⟨w, _, hunique⟩ := S.tangent i
    have hvM : v ∈ S.model.branch i ∧ v ∈ S.region :=
      ⟨hQsub i hv.1, hv.2⟩
    have hvEq : v = w := hunique v hvM
    have hrEq : S.root i = w :=
      hunique (S.root i) ⟨S.model.root_mem i, hrootregion i⟩
    exact hvEq.trans hrEq.symm
  · intro v hv
    have hvM : v ∈ S.model.toMinorModel.vertices := by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv.1
      exact Set.mem_iUnion.mpr ⟨i, hQsub i hi⟩
    exact S.intersection_in_core ⟨hvM, hv.2⟩
  · intro i j hij
    obtain ⟨x, hx, y, hy, hxc, hyc, hxy⟩ := S.core_witness i j hij
    exact ⟨x, hcoreQ i x hx hxc,
      y, hcoreQ j y hy hyc, hxc, hyc, hxy⟩

end Inseparability
end HadwigerLean


