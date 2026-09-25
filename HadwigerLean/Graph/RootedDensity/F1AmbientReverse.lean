import HadwigerLean.Graph.RootedDensity.F1TorsoTransportReduction
import HadwigerLean.Graph.RootedDensity.NestedRigidGlue

/-! One ambient-target reverse model transport implies both F.a torso
transports and hence the full rooted-density conclusion. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- The reverse rigid-truncation principle with the ambient target `H`
fixed but the torso model allowed to use any induced subset of its labels.
The adhesion budget depends on `|H|`, independently of the root count. -/
def AmbientRigidReversePrinciple
    {W : Type v} [Fintype W] (H : SimpleGraph W) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : VertexSeparation G) [Fintype S.left]
    (X : Finset V),
    (X : Set V) ⊆ S.left →
    (Linkedness.separationBoundaryFinset S).card ≤ Fintype.card W →
    UniversalAtRightShore H S →
    UniversalAt (Linkedness.torsoGraph G S) H
      (Linkedness.torsoRootFinset S X) →
    UniversalAt G H X

/-- A uniform ambient reverse transport supplies both torso model
transports required by the extremal F.a argument. -/
theorem badMassedTorsoTransports_of_ambientReverse
    {W : Type v} [Fintype W] {H : SimpleGraph W} {α : ℝ}
    (hreverse : AmbientRigidReversePrinciple.{u,v} H)
    (B : BadMassedWitness.{u,v} H α) :
    BadMassedTorsoTransports B := by
  classical
  letI : Fintype B.Vertex := B.fintype
  letI : DecidableEq B.Vertex := Classical.decEq _
  constructor
  · intro S _ T hBoundary hroot hfar hsep huniS huniT
    have hsize : (Linkedness.separationBoundaryFinset S).card ≤
        Fintype.card W := by
      rw [Linkedness.separationBoundaryFinset_card_eq]
      exact (le_of_lt hsep).trans B.root_card
    letI : Fintype (Linkedness.glueTorsoFar S T hBoundary).right :=
      Fintype.ofFinite _
    letI : DecidableEq (Linkedness.glueTorsoFar S T hBoundary).right :=
      Classical.decEq _
    letI : Fintype (Linkedness.glueTorsoFarRestricted S T hBoundary).left :=
      Fintype.ofFinite _
    apply universalAtRightShore_glueTorsoFar_of_reverse
      S T hBoundary H huniS hsize huniT
    dsimp
    intro hrootR hsizeR huniR htorsoR
    exact hreverse _ (B.graph.induce
        (Linkedness.glueTorsoFar S T hBoundary).right)
      (Linkedness.glueTorsoFarRestricted S T hBoundary)
      (Linkedness.separationBoundaryFinset
        (Linkedness.glueTorsoFar S T hBoundary))
      hrootR hsizeR huniR htorsoR
  · intro S _ hroot hsep huni htorso
    have hsize : (Linkedness.separationBoundaryFinset S).card ≤
        Fintype.card W := by
      rw [Linkedness.separationBoundaryFinset_card_eq]
      exact (le_of_lt hsep).trans B.root_card
    exact hreverse _ B.graph S B.roots hroot hsize huni htorso

/-- Ambient reverse rigid truncation closes the entire massed-pair
universal minor theorem. -/
theorem massedUniversal_of_ambientReverse
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (c : ℝ) (hc : 1 < c) (hforces : DensityForcesMinor.{u,v} H c)
    (hh : 3 ≤ Fintype.card W)
    (hreverse : AmbientRigidReversePrinciple.{u,v} H) :
    MassedUniversalPrinciple.{u,v} H
      (12 * c + 5000 * (Fintype.card W : ℝ)) := by
  apply massedUniversal_of_torso_transports H c hc hforces hh
  intro B
  exact badMassedTorsoTransports_of_ambientReverse hreverse B

/-- Ambient reverse rigid truncation closes the sharp rooted-density
bound of Appendix F. -/
theorem rootedDensity_of_ambientReverse
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (c : ℝ) (hc : 1 < c) (hforces : DensityForcesMinor.{u,v} H c)
    (hh : 3 ≤ Fintype.card W)
    (hreverse : AmbientRigidReversePrinciple.{u,v} H) :
    RootedDensityConclusion.{u,v} H
      (12 * c + 5000 * (Fintype.card W : ℝ)) := by
  exact rootedDensity_of_torso_transports H c hc hforces hh
    (fun B => badMassedTorsoTransports_of_ambientReverse hreverse B)

end HadwigerLean.RootedDensity
