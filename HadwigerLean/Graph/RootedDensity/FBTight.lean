import HadwigerLean.Graph.RootedDensity.FBNonisolated
import HadwigerLean.Graph.RootedDensity.EdgeDeletionFB
import HadwigerLean.Graph.RootedDensity.EdgeTight
import Mathlib.Tactic

/-!
# The F.3 exact incidence identity for an extremal massed pair
-/

namespace HadwigerLean.RootedDensity

universe u v

/-- The strict global mass inequality makes the outside of the root set
nonempty. -/
theorem BadMassedWitness.outside_nonempty
    {W : Type v} [Fintype W] {H : SimpleGraph W} {α : ℝ}
    (B : BadMassedWitness.{u,v} H α) :
    letI : Fintype B.Vertex := B.fintype
    ∃ z : B.Vertex, z ∉ B.roots := by
  classical
  letI : Fintype B.Vertex := B.fintype
  by_contra hn
  push Not at hn
  have hfull : (B.roots : Set B.Vertex) = Set.univ := by
    ext z
    simp [hn z]
  have hg := B.massed.global
  rw [hfull] at hg
  simp [edgeIncidenceSetCount, edgeIncidenceSet] at hg

/-- An extremal bad massed pair has the exact F.3 outside-incidence
count whenever the root count does not exceed the mass floor. -/
theorem BadMassedWitness.floor_edge_tight
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
    (hα : 0 ≤ α) (hXfloor : B.roots.card ≤ Nat.floor α) :
    letI : Fintype B.Vertex := B.fintype
    edgeIncidenceSetCount B.graph (B.roots : Set B.Vertex)ᶜ =
      Nat.floor (α * ((((B.roots : Set B.Vertex)ᶜ).ncard) : ℝ)) + 1 := by
  classical
  letI : Fintype B.Vertex := B.fintype
  letI : DecidableEq B.Vertex := Classical.decEq _
  letI : DecidableRel B.graph.Adj := Classical.decRel _
  obtain ⟨z, hz⟩ := B.outside_nonempty
  obtain ⟨w, hzw⟩ := B.outside_has_neighbor hmin hα z hz
  have hsame : ∀ D : SimpleGraph B.Vertex,
      edgeIncidenceSetCount D (B.roots : Set B.Vertex)ᶜ <
        edgeIncidenceSetCount B.graph (B.roots : Set B.Vertex)ᶜ →
      MassedPair D (B.roots : Set B.Vertex) α →
      UniversalAt D H B.roots := by
    intro D hinc hmD
    exact B.universal_of_lower_incidence hmin D B.roots
      B.root_card hmD hinc
  have hshore : ∀ S : VertexSeparation
      (B.graph.deleteEdges {s(w,z)}),
      (B.roots : Set B.Vertex) ⊆ S.left →
      Nat.card S.separator < Nat.card (B.roots : Set B.Vertex) →
      (edgeIncidenceSetCount (B.graph.deleteEdges {s(w,z)})
        S.strictRight : ℝ) ≤
        α * (Nat.card S.strictRight : ℝ) := by
    by_cases hw : w ∈ B.roots
    · exact B.massed_shore_delete_root_edge_of_floor
        hmin hno hα hXfloor hzw.symm hw hz
    · have hcommonSet : Nat.floor α ≤
          (B.graph.neighborSet w ∩ B.graph.neighborSet z).ncard :=
        B.floor_le_common_exterior hmin hno hα hzw.symm hw hz
      have hcommonFinset : B.roots.card ≤
          (B.graph.neighborFinset w ∩ B.graph.neighborFinset z).card := by
        have hc : (B.graph.neighborFinset w ∩
            B.graph.neighborFinset z).card =
            (B.graph.neighborSet w ∩ B.graph.neighborSet z).ncard := by
          simp only [← Set.ncard_coe_finset, Finset.coe_inter,
            SimpleGraph.coe_neighborFinset]
        omega
      exact Linkedness.massed_shore_delete_edge
        B.graph B.roots α B.massed w z hzw.symm hcommonFinset
  simpa only [← Set.ncard_coe_finset, Finset.coe_compl] using
    floor_edge_tight_of_minimal_bad H B.graph B.roots α hα
    B.massed B.not_universal hsame w z hzw.symm (Or.inr hz) hshore

end HadwigerLean.RootedDensity
