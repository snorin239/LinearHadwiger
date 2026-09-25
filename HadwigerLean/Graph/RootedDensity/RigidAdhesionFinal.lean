import HadwigerLean.Graph.RootedDensity.RigidAdhesionClosed
import HadwigerLean.Graph.RootedDensity.RigidTorsoExtremal

/-! The F.a rigid-shore exclusion at an extremal massed witness. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- The extremal witness has no H-rigid shore once the two torso model
transports are supplied. The fan and separator arguments are closed. -/
theorem BadMassedWitness.no_rigid_of_torso_transports
    {W : Type v} [Fintype W] {H : SimpleGraph W} {α : ℝ}
    (B : BadMassedWitness.{u,v} H α)
    (hmin : ∀ B' : BadMassedWitness.{u,v} H α,
      B.order ≤ B'.order ∧
        (B.order = B'.order →
          B.outsideIncidence ≤ B'.outsideIncidence))
    (hglue : letI : Fintype B.Vertex := B.fintype;
      letI : DecidableEq B.Vertex := Classical.decEq _;
      ∀ (S : VertexSeparation B.graph) [Fintype S.left]
        (T : VertexSeparation (Linkedness.torsoGraph B.graph S))
        (hBoundary : ∀ u : S.left,
          (u : B.Vertex) ∈ S.right → u ∈ T.right),
        (B.roots : Set B.Vertex) ⊆ S.left →
        S.strictRight.Nonempty →
        Nat.card S.separator < B.roots.card →
        UniversalAtRightShore H S →
        UniversalAtRightShore H T →
        UniversalAtRightShore H
          (Linkedness.glueTorsoFar S T hBoundary))
    (hreverse : letI : Fintype B.Vertex := B.fintype;
      letI : DecidableEq B.Vertex := Classical.decEq _;
      ∀ (S : VertexSeparation B.graph) [Fintype S.left],
        (B.roots : Set B.Vertex) ⊆ S.left →
        Nat.card S.separator < B.roots.card →
        UniversalAtRightShore H S →
        UniversalAt (Linkedness.torsoGraph B.graph S) H
          (Linkedness.torsoRootFinset S B.roots) →
        UniversalAt B.graph H B.roots) :
    (letI : Fintype B.Vertex := B.fintype;
     ∀ S : VertexSeparation B.graph,
       (B.roots : Set B.Vertex) ⊆ S.left →
       RigidSeparation H S → False) := by
  classical
  letI : Fintype B.Vertex := B.fintype
  letI : DecidableEq B.Vertex := Classical.decEq _
  letI : DecidableRel B.graph.Adj := Classical.decRel _
  apply no_rigid_of_lower_rigid_exclusion B.graph H B.roots B.not_universal
  intro S hroot hfar hsep huni
  exact B.no_lower_rigid_of_transports hmin hglue hreverse
    ⟨S,hroot,hfar,hsep,huni⟩

end HadwigerLean.RootedDensity
