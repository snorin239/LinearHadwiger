import HadwigerLean.Graph.RootedDensity.RigidTorsoMass
import Mathlib.Tactic

/-! The target-independent F.a torso argument at an extremal witness. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- Any lower-order rigid separation contradicts an extremal bad massed
witness once the rigid-side model transports are available. -/
theorem BadMassedWitness.no_lower_rigid_of_transports
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
    (hex : letI : Fintype B.Vertex := B.fintype;
      ∃ S : VertexSeparation B.graph,
        (B.roots : Set B.Vertex) ⊆ S.left ∧
        S.strictRight.Nonempty ∧
        Nat.card S.separator < B.roots.card ∧
        UniversalAtRightShore H S) :
    False := by
  classical
  letI : Fintype B.Vertex := B.fintype
  letI : DecidableEq B.Vertex := Classical.decEq _
  letI : DecidableRel B.graph.Adj := Classical.decRel _
  have hsmallTorso :
      ∀ (S : VertexSeparation B.graph) [Fintype S.left],
        Nat.card S.left < Fintype.card B.Vertex →
        MassedPair (Linkedness.torsoGraph B.graph S)
          (Linkedness.torsoRootFinset S B.roots : Set S.left) α →
        UniversalAt (Linkedness.torsoGraph B.graph S) H
          (Linkedness.torsoRootFinset S B.roots) := by
    intro S _ horder hmS
    let Y : Finset S.left := Linkedness.torsoRootFinset S B.roots
    have hYsub : Y.image Subtype.val ⊆ B.roots := by
      intro x hx
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
      simpa [Y] using hq
    have hYcard : Y.card ≤ Fintype.card W := by
      have hc : Y.card ≤ B.roots.card := by
        rw [← Finset.card_image_of_injective Y Subtype.val_injective]
        exact Finset.card_le_card hYsub
      exact hc.trans B.root_card
    have hord : Fintype.card S.left < B.order := by
      have hc : Fintype.card S.left = Nat.card S.left :=
        Nat.card_eq_fintype_card.symm
      simpa only [BadMassedWitness.order, hc] using horder
    exact B.universal_of_smaller_order hmin
      (Linkedness.torsoGraph B.graph S) Y hord hYcard hmS
  have hsmallShore :
      ∀ (S : VertexSeparation B.graph) [Fintype S.left],
        Nat.card S.left < Fintype.card B.Vertex →
        ∀ T : VertexSeparation (Linkedness.torsoGraph B.graph S),
          Nat.card T.right < Fintype.card S.left →
          Nat.card T.separator <
            (Linkedness.torsoRootFinset S B.roots).card →
          MassedPair ((Linkedness.torsoGraph B.graph S).induce T.right)
            {q : T.right | (q : S.left) ∈ T.left} α →
          UniversalAtRightShore H T := by
    intro S _ horder T hTorder hTsep hmT
    letI : Fintype T.right := Fintype.ofFinite T.right
    let Y : Finset T.right := Linkedness.separationBoundaryFinset T
    have hYcard : Y.card ≤ Fintype.card W := by
      have hc : Y.card = Nat.card T.separator :=
        Linkedness.separationBoundaryFinset_card_eq T
      have htorsoY : (Linkedness.torsoRootFinset S B.roots).card ≤
          B.roots.card := by
        have hYsub :
            (Linkedness.torsoRootFinset S B.roots).image
              Subtype.val ⊆ B.roots := by
          intro x hx
          obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
          simpa using hq
        rw [← Finset.card_image_of_injective _ Subtype.val_injective]
        exact Finset.card_le_card hYsub
      have hrootcard := B.root_card
      omega
    have hmY : MassedPair
        ((Linkedness.torsoGraph B.graph S).induce T.right)
        (Y : Set T.right) α := by
      simpa [Y, Linkedness.separationBoundaryFinset] using hmT
    have hord : Fintype.card T.right < B.order := by
      have hleft : Fintype.card S.left < B.order := by
        have hc : Fintype.card S.left = Nat.card S.left :=
          Nat.card_eq_fintype_card.symm
        simpa only [BadMassedWitness.order, hc] using horder
      have hc : Fintype.card T.right = Nat.card T.right :=
        Nat.card_eq_fintype_card.symm
      omega
    change UniversalAt
      ((Linkedness.torsoGraph B.graph S).induce T.right) H Y
    exact B.universal_of_smaller_order hmin
      ((Linkedness.torsoGraph B.graph S).induce T.right)
      Y hord hYcard hmY
  exact B.not_universal
    (universalAt_of_lower_rigid_and_smaller_massed
      B.graph H B.roots α B.massed
      hsmallTorso hsmallShore hglue hreverse hex)

end HadwigerLean.RootedDensity
