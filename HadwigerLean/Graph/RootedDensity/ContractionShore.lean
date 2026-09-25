import HadwigerLean.Graph.RootedDensity.ContractionStrictFar
import HadwigerLean.Graph.Linkedness.ContractionLift
import Mathlib.Tactic

/-!
# Contracted-shore stability for arbitrary rooted targets

Every quotient shore satisfies the massed bound under the F.a no-rigid
hypothesis and smaller-order universality. This is the geometric part of
Appendix F.b.
-/

namespace HadwigerLean.RootedDensity

universe u v

/-- Under the no-rigid-separation hypothesis, the F.2 shore inequality
survives contraction of an edge with at most one rooted endpoint. -/
theorem contraction_shore_of_no_rigid_and_minimality
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) (X : Finset V) (α : ℝ)
    (hX : X.card ≤ Fintype.card W)
    (hm : MassedPair G (X : Set V) α)
    (hno : ∀ T : VertexSeparation G,
      (X : Set V) ⊆ T.left → ¬ RigidSeparation H T)
    {a b : V} (hab : G.Adj a b)
    (hsmallQ : ∀ S : VertexSeparation
        (edgeContraction G hab),
      Nat.card S.right < Fintype.card (EdgeContractionVertex a b) →
      Nat.card S.separator <
        Nat.card (Linkedness.partitionIndex
          (edgeContractionPartition G hab) '' (X : Set V)) →
      MassedPair ((edgeContraction G hab).induce S.right)
        {u : S.right | (u : EdgeContractionVertex a b) ∈ S.left} α →
      UniversalAtRightShore H S)
    (hsmallG : ∀ T : VertexSeparation G,
      Nat.card T.right < Fintype.card V →
      Nat.card T.separator ≤ Fintype.card W →
      MassedPair (G.induce T.right)
        {u : T.right | (u : V) ∈ T.left} α →
      UniversalAtRightShore H T) :
    ∀ S : VertexSeparation (edgeContraction G hab),
      (Linkedness.partitionIndex
        (edgeContractionPartition G hab) '' (X : Set V)) ⊆ S.left →
      Nat.card S.separator <
        Nat.card (Linkedness.partitionIndex
          (edgeContractionPartition G hab) '' (X : Set V)) →
      (edgeIncidenceSetCount (edgeContraction G hab)
        S.strictRight : ℝ) ≤
        α * (Nat.card S.strictRight : ℝ) := by
  classical
  let C := edgeContractionPartition G hab
  let Q := edgeContraction G hab
  let Y : Set (EdgeContractionVertex a b) :=
    Linkedness.partitionIndex C '' (X : Set V)
  intro S hroot hsep
  by_contra hnot
  have hdense : α * (Nat.card S.strictRight : ℝ) <
      (edgeIncidenceSetCount Q S.strictRight : ℝ) :=
    lt_of_not_ge hnot
  have hex : ∃ T : VertexSeparation Q,
      Y ⊆ T.left ∧ Nat.card T.separator < Nat.card Y ∧
      α * (Nat.card T.strictRight : ℝ) <
        (edgeIncidenceSetCount Q T.strictRight : ℝ) :=
    ⟨S, hroot, hsep, hdense⟩
  obtain ⟨T, hrootT, hsepT, hdenseT, hmT, horderT⟩ :=
    exists_massed_dense_shore_of_violation Q Y α hex
  have huniT : UniversalAtRightShore H T :=
    hsmallQ T horderT hsepT hmT
  by_cases hright : none ∈ T.right
  · by_cases hleft : none ∈ T.left
    · exact no_dense_contraction_separator_of_no_rigid
        G H X α hX hm hno hsmallG hab T
        hrootT hsepT ⟨hleft, hright⟩ hdenseT
    · exact no_universal_contraction_strictFar_of_no_rigid
        G H X hX hno hab T hrootT hsepT
        ⟨hright, hleft⟩ huniT
  · have hbound := Linkedness.edgeContraction_shore_away
      hab X α hm T hrootT hsepT hright
    exact (not_lt_of_ge hbound) hdenseT

end HadwigerLean.RootedDensity
