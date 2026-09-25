import HadwigerLean.Graph.RootedDensity.FBExtremal
import HadwigerLean.Graph.RootedDensity.EdgeDeletionRootShore
import HadwigerLean.Graph.RootedDensity.RootCorrection

/-! The F.b root correction supplies the exact budget for F.3 edge deletion. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- The common-neighbor estimate for an extremal root edge supplies the
outside-common plus root-neighbor budget used by the deletion shore lemma. -/
theorem BadMassedWitness.root_edge_deletion_budget
    {W : Type v} [Fintype W] {H : SimpleGraph W} {α : ℝ}
    (B : BadMassedWitness.{u,v} H α)
    (hmin : ∀ B' : BadMassedWitness.{u,v} H α,
      B.order ≤ B'.order ∧
        (B.order = B'.order →
          B.outsideIncidence ≤ B'.outsideIncidence))
    (hno : letI : Fintype B.Vertex := B.fintype;
      ∀ T : VertexSeparation B.graph,
        (B.roots : Set B.Vertex) ⊆ T.left →
        ¬ RigidSeparation H T)
    (hα : 0 ≤ α) (hXfloor : B.roots.card ≤ Nat.floor α)
    {a b : B.Vertex} (hab : B.graph.Adj a b)
    (ha : a ∈ B.roots) (hb : b ∉ B.roots) :
    letI : Fintype B.Vertex := B.fintype
    letI : DecidableEq B.Vertex := Classical.decEq _
    letI : DecidableRel B.graph.Adj := Classical.decRel _
    B.roots.card ≤
      ((B.graph.neighborFinset a ∩ B.graph.neighborFinset b) \ B.roots).card +
        (B.graph.neighborFinset b ∩ B.roots.erase a).card := by
  classical
  letI : Fintype B.Vertex := B.fintype
  letI : DecidableEq B.Vertex := Classical.decEq _
  letI : DecidableRel B.graph.Adj := Classical.decRel _
  have hfb := B.floor_le_common_root hmin hno hα hab ha hb
  have hfbFinset : Nat.floor α ≤
      (B.graph.neighborFinset a ∩ B.graph.neighborFinset b).card +
        (((B.graph.neighborFinset b ∩ B.roots.erase a) \
          B.graph.neighborFinset a).card) := by
    simpa only [← Set.ncard_coe_finset, Finset.coe_inter, Finset.coe_sdiff,
      Finset.coe_erase, SimpleGraph.coe_neighborFinset] using hfb
  rw [common_add_rootCorrection_eq_outside_common_add_rootNeighbors] at hfbFinset
  omega

/-- F.3 shore stability for deleting an edge from a root to an outside
vertex in an extremal massed counterexample. -/
theorem BadMassedWitness.massed_shore_delete_root_edge_of_floor
    {W : Type v} [Fintype W] {H : SimpleGraph W} {α : ℝ}
    (B : BadMassedWitness.{u,v} H α)
    (hmin : ∀ B' : BadMassedWitness.{u,v} H α,
      B.order ≤ B'.order ∧
        (B.order = B'.order →
          B.outsideIncidence ≤ B'.outsideIncidence))
    (hno : letI : Fintype B.Vertex := B.fintype;
      ∀ T : VertexSeparation B.graph,
        (B.roots : Set B.Vertex) ⊆ T.left →
        ¬ RigidSeparation H T)
    (hα : 0 ≤ α) (hXfloor : B.roots.card ≤ Nat.floor α)
    {a b : B.Vertex} (hab : B.graph.Adj a b)
    (ha : a ∈ B.roots) (hb : b ∉ B.roots) :
    letI : Fintype B.Vertex := B.fintype
    ∀ (S : VertexSeparation (B.graph.deleteEdges {s(a,b)})),
      (B.roots : Set B.Vertex) ⊆ S.left →
      Nat.card S.separator < Nat.card (B.roots : Set B.Vertex) →
      (edgeIncidenceSetCount (B.graph.deleteEdges {s(a,b)}) S.strictRight : ℝ) ≤
        α * (Nat.card S.strictRight : ℝ) := by
  classical
  letI : Fintype B.Vertex := B.fintype
  letI : DecidableEq B.Vertex := Classical.decEq _
  letI : DecidableRel B.graph.Adj := Classical.decRel _
  intro S hroot hsmall
  exact massed_shore_delete_root_edge B.graph B.roots α B.massed a b hab ha hb
    (B.root_edge_deletion_budget hmin hno hα hXfloor hab ha hb)
    S hroot hsmall

end HadwigerLean.RootedDensity
