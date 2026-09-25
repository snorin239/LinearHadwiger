import HadwigerLean.Graph.RootedDensity.RigidAdhesionReduction
import HadwigerLean.Graph.RootedDensity.RigidTorsoExtremal

/-! The F.a no-rigid conclusion for an extremal massed witness. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- Once the torso and fan model transports are supplied, an extremal bad
massed witness has no H-rigid separation containing its roots on the near
side. The Menger step applies even when adhesion exceeds root order. -/
theorem BadMassedWitness.no_rigid_of_transports
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
        UniversalAt B.graph H B.roots)
    (hfull : letI : Fintype B.Vertex := B.fintype;
      letI : DecidableEq B.Vertex := Classical.decEq _;
      ∀ (S : VertexSeparation B.graph) [Fintype S.left],
        (B.roots : Set B.Vertex) ⊆ S.left →
        ∀ {n : ℕ} (P : IndexedPairs (Fin n) S.left)
          (_ : IndexedLinkage (B.graph.induce S.left) P),
          Finset.univ.image P.start = Linkedness.torsoRootFinset S B.roots →
          (∀ i, P.finish i ∈ Linkedness.torsoBoundaryFinset B.graph S) →
          (Linkedness.separationBoundaryFinset S).card ≤ Fintype.card W →
          UniversalAtRightShore H S → UniversalAt B.graph H B.roots)
    (hsaturated : letI : Fintype B.Vertex := B.fintype;
      letI : DecidableEq B.Vertex := Classical.decEq _;
      ∀ (S : VertexSeparation B.graph) [Fintype S.left]
        (T : VertexSeparation (B.graph.induce S.left))
        (hBoundary : ∀ u : S.left, (u : B.Vertex) ∈ S.right → u ∈ T.right)
        {q : ℕ} (C : IndexedPairs (Fin q) S.left)
        (F : IndexedLinkage (B.graph.induce S.left) C),
        Finset.univ.image C.start = T.separatorFinset →
        (∀ i, (C.finish i : B.Vertex) ∈ S.separator) →
        (∀ i x, x ∈ pathVertexSet (F.path i) → x ∈ T.right) →
        (∀ i x, x ∈ pathVertexSet (F.path i) →
          (x : B.Vertex) ∈ S.right → x = C.finish i) →
        (Linkedness.separationBoundaryFinset S).card ≤ Fintype.card W →
        UniversalAtRightShore H S →
        UniversalAtRightShore H (S.glueLeft T hBoundary)) :
    (letI : Fintype B.Vertex := B.fintype;
     ∀ S : VertexSeparation B.graph,
       (B.roots : Set B.Vertex) ⊆ S.left →
       RigidSeparation H S → False) := by
  classical
  letI : Fintype B.Vertex := B.fintype
  letI : DecidableEq B.Vertex := Classical.decEq _
  letI : DecidableRel B.graph.Adj := Classical.decRel _
  apply no_rigid_of_lower_rigid_exclusion_and_fans
    B.graph H B.roots B.not_universal
  · intro S hroot hfar hsep huni
    exact B.no_lower_rigid_of_transports hmin hglue hreverse
      ⟨S,hroot,hfar,hsep,huni⟩
  · exact hfull
  · exact hsaturated

end HadwigerLean.RootedDensity
