import HadwigerLean.Graph.RootedDensity.EdgeDeletionFB
import HadwigerLean.Graph.RootedDensity.EdgeTight

/-! F.3 edge-tightness for an extremal bad massed pair. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- Every edge meeting the outside of the roots has a shore-stable deletion
under the F.b common-neighbor estimates. -/
theorem BadMassedWitness.massed_shore_delete_exterior_edge
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
    (hout : a ∉ B.roots ∨ b ∉ B.roots) :
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
  by_cases ha : a ∈ B.roots
  · have hb : b ∉ B.roots := by
      rcases hout with haout | hbout
      · exact False.elim (haout ha)
      · exact hbout
    exact B.massed_shore_delete_root_edge_of_floor hmin hno hα hXfloor
      hab ha hb
  · by_cases hb : b ∈ B.roots
    · have hreverse := B.massed_shore_delete_root_edge_of_floor hmin hno
        hα hXfloor hab.symm hb ha
      have hedge : ({s(b,a)} : Set (Sym2 B.Vertex)) = {s(a,b)} := by
        congr 1
        exact Sym2.eq_swap
      rw [hedge] at hreverse
      exact hreverse
    · intro S hroot hsmall
      have hfb := B.floor_le_common_exterior hmin hno hα hab ha hb
      have hfbFinset : Nat.floor α ≤
          (B.graph.neighborFinset a ∩ B.graph.neighborFinset b).card := by
        simpa only [← Set.ncard_coe_finset, Finset.coe_inter,
          SimpleGraph.coe_neighborFinset] using hfb
      have hcommon : B.roots.card ≤
          (B.graph.neighborFinset a ∩ B.graph.neighborFinset b).card := by
        omega
      exact Linkedness.massed_shore_delete_edge B.graph B.roots α
        B.massed a b hab hcommon S hroot hsmall

/-- Deleting any edge meeting the outside of the roots forces the exact
outside-incidence count at an extremal bad massed pair. -/
theorem BadMassedWitness.floor_edge_tight
    {W : Type v} [Fintype W] (H : SimpleGraph W) {α : ℝ}
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
    (hout : a ∉ B.roots ∨ b ∉ B.roots) :
    letI : Fintype B.Vertex := B.fintype
    letI : DecidableEq B.Vertex := Classical.decEq _
    edgeIncidenceSetCount B.graph (B.roots : Set B.Vertex)ᶜ =
      Nat.floor (α * ((B.rootsᶜ).card : ℝ)) + 1 := by
  classical
  letI : Fintype B.Vertex := B.fintype
  letI : DecidableEq B.Vertex := Classical.decEq _
  letI : DecidableRel B.graph.Adj := Classical.decRel _
  apply floor_edge_tight_of_minimal_bad H B.graph B.roots α hα B.massed
    B.not_universal ?_ a b hab hout
    (B.massed_shore_delete_exterior_edge hmin hno hα hXfloor hab hout)
  intro D hinc hmD
  exact B.universal_of_lower_incidence hmin D B.roots B.root_card hmD
    (by simpa only [BadMassedWitness.outsideIncidence] using hinc)

end HadwigerLean.RootedDensity





