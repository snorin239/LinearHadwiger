import HadwigerLean.Graph.RootedDensity.FBGlobalFailure
import HadwigerLean.Graph.RootedDensity.FBMassDrop
import HadwigerLean.Graph.Linkedness.MinimalCounterexample
import Mathlib.Tactic

/-!
# The F.b common-neighbor bounds in an extremal massed counterexample
-/

namespace HadwigerLean.RootedDensity

universe u v

/-- The contracted graph of an extremal bad massed pair fails the global
strict mass inequality, provided no H-rigid shore remains. -/
theorem BadMassedWitness.contraction_global_failure
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
    {a b : B.Vertex} (hab : B.graph.Adj a b) (hb : b ∉ B.roots) :
    letI : Fintype B.Vertex := B.fintype
    let C := edgeContractionPartition B.graph hab
    let Y : Set (EdgeContractionVertex a b) :=
      Linkedness.partitionIndex C '' (B.roots : Set B.Vertex)
    (edgeIncidenceSetCount (edgeContraction B.graph hab) Yᶜ : ℝ) ≤
      α * ((Yᶜ).ncard : ℝ) := by
  classical
  letI : Fintype B.Vertex := B.fintype
  letI : DecidableEq B.Vertex := Classical.decEq _
  letI : DecidableRel B.graph.Adj := Classical.decRel _
  let C := edgeContractionPartition B.graph hab
  let Q := edgeContraction B.graph hab
  let f := Linkedness.partitionIndex C
  let Y : Set (EdgeContractionVertex a b) := f '' (B.roots : Set B.Vertex)
  have hquot : Fintype.card (EdgeContractionVertex a b) < B.order := by
    simpa [BadMassedWitness.order] using
      Linkedness.edgeContraction_order_lt_linkedness B.graph hab
  have hYle : Nat.card Y ≤ B.roots.card := by
    simpa only [Nat.card_coe_set_eq, Set.ncard_coe_finset] using
      Set.ncard_image_le (Set.toFinite (B.roots : Set B.Vertex))
  have hsmallQ : ∀ S : VertexSeparation Q,
      Nat.card S.right < Fintype.card (EdgeContractionVertex a b) →
      Nat.card S.separator < Nat.card Y →
      MassedPair (Q.induce S.right)
        {q : S.right | (q : EdgeContractionVertex a b) ∈ S.left} α →
      UniversalAtRightShore H S := by
    intro S horder hsep hmS
    letI : Fintype S.right := Fintype.ofFinite S.right
    let Z : Finset S.right := Linkedness.separationBoundaryFinset S
    have hZcard : Z.card ≤ Fintype.card W := by
      have hc : Z.card = Nat.card S.separator :=
        Linkedness.separationBoundaryFinset_card_eq S
      have hrootcard := B.root_card
      omega
    have hmZ : MassedPair (Q.induce S.right) (Z : Set S.right) α := by
      simpa [Z, Linkedness.separationBoundaryFinset] using hmS
    have hord : Fintype.card S.right < B.order := by
      have hc : Fintype.card S.right = Nat.card S.right :=
        Nat.card_eq_fintype_card.symm
      omega
    change UniversalAt (Q.induce S.right) H Z
    exact B.universal_of_smaller_order hmin
      (Q.induce S.right) Z hord hZcard hmZ
  have hsmallG : ∀ T : VertexSeparation B.graph,
      Nat.card T.right < Fintype.card B.Vertex →
      Nat.card T.separator ≤ Fintype.card W →
      MassedPair (B.graph.induce T.right)
        {x : T.right | (x : B.Vertex) ∈ T.left} α →
      UniversalAtRightShore H T := by
    intro T horder hsep hmT
    letI : Fintype T.right := Fintype.ofFinite T.right
    let Z : Finset T.right := Linkedness.separationBoundaryFinset T
    have hZcard : Z.card ≤ Fintype.card W := by
      have hc : Z.card = Nat.card T.separator :=
        Linkedness.separationBoundaryFinset_card_eq T
      omega
    have hmZ : MassedPair (B.graph.induce T.right) (Z : Set T.right) α := by
      simpa [Z, Linkedness.separationBoundaryFinset] using hmT
    have hord : Fintype.card T.right < B.order := by
      have hc : Fintype.card T.right = Nat.card T.right :=
        Nat.card_eq_fintype_card.symm
      simpa [BadMassedWitness.order] using horder
    change UniversalAt (B.graph.induce T.right) H Z
    exact B.universal_of_smaller_order hmin
      (B.graph.induce T.right) Z hord hZcard hmZ
  have hminQ : MassedPair Q Y α →
      UniversalAt Q H (B.roots.image f) := by
    intro hmQ
    have hcard : (B.roots.image f).card ≤ Fintype.card W :=
      (Finset.card_image_le).trans B.root_card
    have hset : (B.roots.image f : Set (EdgeContractionVertex a b)) = Y := by
      ext q
      simp [Y, f]
    exact B.universal_of_smaller_order hmin Q (B.roots.image f)
      hquot hcard (by simpa only [hset] using hmQ)
  exact contraction_global_failure_of_no_rigid_and_minimality
    B.graph H B.roots α B.root_card B.massed B.not_universal
    hno hab hb hsmallQ hsmallG hminQ

/-- F.b's exterior-edge common-neighbor estimate for an extremal bad
massed pair. -/
theorem BadMassedWitness.floor_le_common_exterior
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
    (hα : 0 ≤ α)
    {a b : B.Vertex} (hab : B.graph.Adj a b)
    (ha : a ∉ B.roots) (hb : b ∉ B.roots) :
    letI : Fintype B.Vertex := B.fintype
    Nat.floor α ≤
      (B.graph.neighborSet a ∩ B.graph.neighborSet b).ncard := by
  classical
  letI : Fintype B.Vertex := B.fintype
  letI : DecidableEq B.Vertex := Classical.decEq _
  letI : DecidableRel B.graph.Adj := Classical.decRel _
  simpa only [← Set.ncard_coe_finset, Finset.coe_inter,
    SimpleGraph.coe_neighborFinset] using
    floor_le_common_of_exterior_contraction_failure
    B.graph B.roots α hα B.massed hab ha hb
    (B.contraction_global_failure hmin hno hab hb)

/-- F.b's root-exterior common-neighbor estimate, including the exact
root-incidence correction. -/
theorem BadMassedWitness.floor_le_common_root
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
    (hα : 0 ≤ α)
    {a b : B.Vertex} (hab : B.graph.Adj a b)
    (ha : a ∈ B.roots) (hb : b ∉ B.roots) :
    letI : Fintype B.Vertex := B.fintype
    Nat.floor α ≤
      (B.graph.neighborSet a ∩ B.graph.neighborSet b).ncard +
      ((B.graph.neighborSet b ∩ ((B.roots : Set B.Vertex) \ {a})) \
        B.graph.neighborSet a).ncard := by
  classical
  letI : Fintype B.Vertex := B.fintype
  letI : DecidableEq B.Vertex := Classical.decEq _
  letI : DecidableRel B.graph.Adj := Classical.decRel _
  simpa only [← Set.ncard_coe_finset, Finset.coe_inter, Finset.coe_sdiff, Finset.coe_erase,
    SimpleGraph.coe_neighborFinset] using
    floor_le_common_add_rootCorrection_of_contraction_failure
    B.graph B.roots α hα B.massed hab ha hb
    (B.contraction_global_failure hmin hno hab hb)

end HadwigerLean.RootedDensity
