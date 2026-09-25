import HadwigerLean.Graph.RootedDensity.RigidAdhesionFinal
import HadwigerLean.Graph.RootedDensity.F1Reduction

/-! Final Appendix F reduction with only two torso model transports as
inputs. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- The two model transports needed by F.a at one massed counterexample. -/
structure BadMassedTorsoTransports
    {W : Type v} [Fintype W] {H : SimpleGraph W} {α : ℝ}
    (B : BadMassedWitness.{u,v} H α) : Prop where
  glue : letI : Fintype B.Vertex := B.fintype;
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
        (Linkedness.glueTorsoFar S T hBoundary)
  reverse : letI : Fintype B.Vertex := B.fintype;
    letI : DecidableEq B.Vertex := Classical.decEq _;
    ∀ (S : VertexSeparation B.graph) [Fintype S.left],
      (B.roots : Set B.Vertex) ⊆ S.left →
      Nat.card S.separator < B.roots.card →
      UniversalAtRightShore H S →
      UniversalAt (Linkedness.torsoGraph B.graph S) H
        (Linkedness.torsoRootFinset S B.roots) →
      UniversalAt B.graph H B.roots

/-- The full massed universality principle follows once the two rigid
torso model transports are available at every extremal witness. -/
theorem massedUniversal_of_torso_transports
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (c : ℝ) (hc : 1 < c) (hforces : DensityForcesMinor.{u,v} H c)
    (hh : 3 ≤ Fintype.card W)
    (htransport : ∀ B : BadMassedWitness.{u,v} H
      (12 * c + 5000 * (Fintype.card W : ℝ)),
      BadMassedTorsoTransports B) :
    MassedUniversalPrinciple.{u,v} H
      (12 * c + 5000 * (Fintype.card W : ℝ)) := by
  apply massedUniversal_of_no_rigid_extremal H c hc hforces hh
  intro B hmin
  let T := htransport B
  intro S hroot hrigid
  exact B.no_rigid_of_torso_transports hmin T.glue T.reverse S hroot hrigid

/-- The density-to-rooted-minor conclusion of Appendix F follows from
the two rigid torso model transports. -/
theorem rootedDensity_of_torso_transports
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (c : ℝ) (hc : 1 < c) (hforces : DensityForcesMinor.{u,v} H c)
    (hh : 3 ≤ Fintype.card W)
    (htransport : ∀ B : BadMassedWitness.{u,v} H
      (12 * c + 5000 * (Fintype.card W : ℝ)),
      BadMassedTorsoTransports B) :
    RootedDensityConclusion.{u,v} H
      (12 * c + 5000 * (Fintype.card W : ℝ)) := by
  exact rootedDensity_of_massedUniversal H c hh (by linarith)
    (massedUniversal_of_torso_transports H c hc hforces hh htransport)

end HadwigerLean.RootedDensity
