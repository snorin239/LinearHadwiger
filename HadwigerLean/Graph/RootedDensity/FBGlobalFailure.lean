import HadwigerLean.Graph.RootedDensity.ContractionShore
import Mathlib.Tactic

/-!
# The F.b global obstruction after contraction

Once every contracted shore satisfies F.2, the quotient must fail strict
F.1: otherwise minimality makes it H-universal and its model lifts.
-/

namespace HadwigerLean.RootedDensity

universe u v

/-- A contraction of an edge with at most one rooted endpoint cannot
satisfy strict F.1 in a non-universal massed counterexample. -/
theorem contraction_global_failure_of_no_rigid_and_minimality
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) (X : Finset V) (α : ℝ)
    (hX : X.card ≤ Fintype.card W)
    (hm : MassedPair G (X : Set V) α)
    (hbad : ¬ UniversalAt G H X)
    (hno : ∀ T : VertexSeparation G,
      (X : Set V) ⊆ T.left → ¬ RigidSeparation H T)
    {a b : V} (hab : G.Adj a b) (hb : b ∉ X)
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
      UniversalAtRightShore H T)
    (hminQ : MassedPair (edgeContraction G hab)
      (Linkedness.partitionIndex
        (edgeContractionPartition G hab) '' (X : Set V)) α →
      UniversalAt (edgeContraction G hab) H
        (X.image (Linkedness.partitionIndex
          (edgeContractionPartition G hab)))) :
    let C := edgeContractionPartition G hab
    let Y : Set (EdgeContractionVertex a b) :=
      Linkedness.partitionIndex C '' (X : Set V)
    (edgeIncidenceSetCount (edgeContraction G hab) Yᶜ : ℝ) ≤
      α * ((Yᶜ).ncard : ℝ) := by
  classical
  let C := edgeContractionPartition G hab
  let Q := edgeContraction G hab
  let Y : Set (EdgeContractionVertex a b) :=
    Linkedness.partitionIndex C '' (X : Set V)
  have hshore :=
    contraction_shore_of_no_rigid_and_minimality
      G H X α hX hm hno hab hsmallQ hsmallG
  have hbadQ : ¬ UniversalAt Q H
      (X.image (Linkedness.partitionIndex C)) :=
    not_universalAt_edgeContraction G H X hab hb hbad
  by_contra hnot
  have hstrict : α * ((Yᶜ).ncard : ℝ) <
      (edgeIncidenceSetCount Q Yᶜ : ℝ) := lt_of_not_ge hnot
  have hmQ : MassedPair Q Y α := by
    refine ⟨?_, ?_⟩
    · have hcard : Nat.card {q : EdgeContractionVertex a b // q ∉ Y} =
          (Yᶜ).ncard := by
        change Nat.card (Yᶜ : Set (EdgeContractionVertex a b)) =
          (Yᶜ).ncard
        exact Nat.card_coe_set_eq (Yᶜ)
      rw [hcard]
      exact hstrict
    · exact hshore
  exact hbadQ (hminQ hmQ)

end HadwigerLean.RootedDensity
