import HadwigerLean.Graph.RootedDensity.FBMassDrop
import HadwigerLean.Graph.Linkedness.ContractionLift
import Mathlib.Tactic

/-!
# The separator case of contracted-shore stability

If the contracted vertex lies in the separator of a dense violating shore,
its pullback has an adhesion of size at most the root order.  The induced
pullback shore is massed and hence universal by smaller-order minimality,
contradicting the absence of H-rigid separations.
-/

namespace HadwigerLean.RootedDensity

universe u v

/-- The separator case in the F.b proof of contraction shore stability. -/
theorem no_dense_contraction_separator_of_no_rigid
    {V : Type u} {W : Type v} [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) (X : Finset V) (α : ℝ)
    (hX : X.card ≤ Fintype.card W)
    (hm : MassedPair G (X : Set V) α)
    (hno : ∀ T : VertexSeparation G,
      (X : Set V) ⊆ T.left → ¬ RigidSeparation H T)
    (hsmall : ∀ T : VertexSeparation G,
      Nat.card T.right < Fintype.card V →
      Nat.card T.separator ≤ Fintype.card W →
      MassedPair (G.induce T.right)
        {u : T.right | (u : V) ∈ T.left} α →
      UniversalAtRightShore H T)
    {a b : V} (hab : G.Adj a b)
    (S : VertexSeparation (edgeContraction G hab))
    (hroot :
      (Linkedness.partitionIndex (edgeContractionPartition G hab) ''
        (X : Set V)) ⊆ S.left)
    (hsep : Nat.card S.separator <
      Nat.card (Linkedness.partitionIndex
        (edgeContractionPartition G hab) '' (X : Set V)))
    (hnone : none ∈ S.separator)
    (hdense : α * (Nat.card S.strictRight : ℝ) <
      (edgeIncidenceSetCount (edgeContraction G hab) S.strictRight : ℝ)) :
    False := by
  classical
  let C := edgeContractionPartition G hab
  let T := Linkedness.partitionPullbackSeparation C S
  have hmT : MassedPair (G.induce T.right)
      {u : T.right | (u : V) ∈ T.left} α :=
    Linkedness.massed_contraction_separator_shore hab X α hm S
      hroot hsep hnone hdense
  have horder : Nat.card T.right < Fintype.card V :=
    Linkedness.contraction_pullback_right_card_lt_of_root_sep
      hab X S hroot hsep
  have hrootT : (X : Set V) ⊆ T.left := by
    intro x hx
    exact hroot ⟨x, hx, rfl⟩
  have hsizeImage : Nat.card
      (Linkedness.partitionIndex C '' (X : Set V)) ≤
      Nat.card (X : Set V) := by
    change (Linkedness.partitionIndex C '' (X : Set V)).ncard ≤
      (X : Set V).ncard
    exact Set.ncard_image_le (Set.toFinite (X : Set V))
  have hsepT : Nat.card T.separator ≤ Fintype.card W := by
    have hcard : Nat.card T.separator = Nat.card S.separator + 1 :=
      Linkedness.edgeContraction_preimage_card_of_mem_contract
        hab S.separator hnone
    have hXnat : Nat.card (X : Set V) = X.card := by simp
    change Nat.card S.separator <
      Nat.card (Linkedness.partitionIndex C '' (X : Set V)) at hsep
    omega
  have huni : UniversalAtRightShore H T :=
    hsmall T horder hsepT hmT
  have hSfar : S.strictRight.Nonempty := by
    by_contra hn
    have he : S.strictRight = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    rw [he] at hdense
    simp [edgeIncidenceSetCount, edgeIncidenceSet] at hdense
  obtain ⟨q,hq⟩ := hSfar
  have hTfar : T.strictRight.Nonempty := by
    cases hqv : q with
    | none =>
        exact False.elim (hq.2 (hqv ▸ hnone.1))
    | some z =>
        have hzidx : Linkedness.partitionIndex C z.1 = some z := by
          have hz := z.property
          simpa [C] using
            Linkedness.edgeContraction_index_some hab z.1 hz.1 hz.2
        refine ⟨z.1, ?_⟩
        change Linkedness.partitionIndex C z.1 ∈ S.strictRight
        rw [hzidx]
        exact hqv ▸ hq
  exact hno T hrootT ⟨hTfar, hsepT, huni⟩

end HadwigerLean.RootedDensity