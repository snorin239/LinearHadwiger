import HadwigerLean.Graph.RootedDensity.SmallRoots
import HadwigerLean.Graph.RootedDensity.F3Contradiction

/-! Final Appendix F.1 reduction: only the rigid-separation exclusion remains. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- The F.a no-rigid theorem, at extremal bad witnesses, implies the
full massed-universality principle by the checked small-root base and
the F.b–F.c contradiction. -/
theorem massedUniversal_of_no_rigid_extremal
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (c : ℝ) (hc : 1 < c) (hforces : DensityForcesMinor.{u,v} H c)
    (hh : 3 ≤ Fintype.card W)
    (hno : ∀ B : BadMassedWitness.{u,v} H
        (12 * c + 5000 * (Fintype.card W : ℝ)),
      (∀ B' : BadMassedWitness.{u,v} H
        (12 * c + 5000 * (Fintype.card W : ℝ)),
          B.order ≤ B'.order ∧
            (B.order = B'.order →
              B.outsideIncidence ≤ B'.outsideIncidence)) →
      (letI : Fintype B.Vertex := B.fintype;
       ∀ T : VertexSeparation B.graph,
         (B.roots : Set B.Vertex) ⊆ T.left →
         ¬ RigidSeparation H T)) :
    MassedUniversalPrinciple.{u,v} H
      (12 * c + 5000 * (Fintype.card W : ℝ)) := by
  classical
  by_contra hfail
  obtain ⟨B, hmin⟩ :=
    exists_extremal_bad_massed_witness H
      (12 * c + 5000 * (Fintype.card W : ℝ)) hfail
  letI : Fintype B.Vertex := B.fintype
  letI : DecidableEq B.Vertex := Classical.decEq _
  letI : DecidableRel B.graph.Adj := Classical.decRel _
  have hX3 : 3 ≤ B.roots.card := by
    by_contra hnot
    have hsmall : B.roots.card ≤ 2 := by omega
    exact B.not_universal
      (universalAt_of_massed_card_le_two
        B.graph H B.roots
        (12 * c + 5000 * (Fintype.card W : ℝ))
        B.massed hsmall)
  exact no_extremal_bad_massed_of_three_roots
    H c hc hforces hh B hmin (hno B hmin) hX3

end HadwigerLean.RootedDensity
