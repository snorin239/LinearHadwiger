import HadwigerLean.Graph.RootedDensity.FBExtremal
import HadwigerLean.Graph.RootedDensity.FBConclusion
import Mathlib.Tactic

/-!
# The F.b local universal core in an extremal massed counterexample
-/

namespace HadwigerLean.RootedDensity

universe u v

/-- A nonisolated low-degree exterior vertex in an extremal bad massed
pair has an induced H-universal neighborhood core. This combines the
F.b contraction estimates with the F.2 numerical closure. -/
theorem BadMassedWitness.exists_ambient_universal_induced_of_low_degree
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (c : ℝ) (hc : 1 < c) (hforces : DensityForcesMinor.{u,v} H c)
    (hh : 3 ≤ Fintype.card W)
    (B : BadMassedWitness.{u,v} H
      (12 * c + 5000 * (Fintype.card W : ℝ)))
    (hmin : ∀ B' : BadMassedWitness.{u,v} H
        (12 * c + 5000 * (Fintype.card W : ℝ)),
      B.order ≤ B'.order ∧
        (B.order = B'.order →
          B.outsideIncidence ≤ B'.outsideIncidence))
    (hno : letI : Fintype B.Vertex := B.fintype;
      ∀ T : VertexSeparation B.graph,
        (B.roots : Set B.Vertex) ⊆ T.left →
        ¬ RigidSeparation H T)
    (z : B.Vertex) (hz : z ∉ B.roots)
    (hdeg : ((B.graph.neighborSet z).ncard : ℝ) ≤
      2 * (12 * c + 5000 * (Fintype.card W : ℝ)))
    (hnonisolated : ∃ w : B.Vertex, B.graph.Adj z w) :
    letI : Fintype B.Vertex := B.fintype
    ∃ S : Finset B.Vertex,
      Universal (B.graph.induce (S : Set B.Vertex)) H := by
  classical
  letI : Fintype B.Vertex := B.fintype
  letI : DecidableEq B.Vertex := Classical.decEq _
  letI : DecidableRel B.graph.Adj := Classical.decRel _
  let α : ℝ := 12 * c + 5000 * (Fintype.card W : ℝ)
  have hα : 0 ≤ α := by
    dsimp [α]
    positivity
  have hdeg' : (B.graph.degree z : ℝ) ≤
      2 * (12 * c + 5000 * (Fintype.card W : ℝ)) := by
    simpa only [SimpleGraph.degree, ← Set.ncard_coe_finset,
      SimpleGraph.coe_neighborFinset] using hdeg
  apply exists_ambient_universal_induced_of_FB H c hc hforces hh
    B.graph B.roots B.root_card z hdeg' hnonisolated
  · intro w hzw hw
    have hbound := floor_le_common_of_exterior_contraction_failure
      B.graph B.roots α hα B.massed hzw hz hw
      (B.contraction_global_failure hmin hno hzw hw)
    have hcard : Fintype.card (B.graph.commonNeighbors z w) =
        (B.graph.neighborSet z ∩ B.graph.neighborSet w).ncard := by
      calc
        Fintype.card (B.graph.commonNeighbors z w) =
            (B.graph.commonNeighbors z w).ncard :=
          Set.fintypeCard_eq_ncard _
        _ = _ := by rw [SimpleGraph.commonNeighbors_eq]
    rw [hcard]
    simpa [α, ← Set.ncard_coe_finset, Finset.coe_inter,
      SimpleGraph.coe_neighborFinset] using hbound
  · intro w hzw hw
    have hbound := floor_le_common_add_otherRoots_of_contraction_failure
      B.graph B.roots α hα B.massed hzw.symm hw hz
      (B.contraction_global_failure hmin hno hzw.symm hz)
    have hcard : Fintype.card (B.graph.commonNeighbors z w) =
        (B.graph.neighborSet w ∩ B.graph.neighborSet z).ncard := by
      calc
        Fintype.card (B.graph.commonNeighbors z w) =
            (B.graph.commonNeighbors z w).ncard :=
          Set.fintypeCard_eq_ncard _
        _ = _ := by rw [SimpleGraph.commonNeighbors_eq, Set.inter_comm]
    rw [hcard]
    simpa [α, ← Set.ncard_coe_finset, Finset.coe_inter,
      SimpleGraph.coe_neighborFinset] using hbound

end HadwigerLean.RootedDensity
