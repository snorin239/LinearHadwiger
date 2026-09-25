import HadwigerLean.Graph.RootedDensity.ContractionSeparator
import HadwigerLean.Graph.RootedDensity.PartitionInduceLift
import Mathlib.Tactic

/-!
# Universality across a strict-far contracted shore

When the contracted vertex lies strictly on the far side, the adhesion
avoids it.  Its vertices therefore lift one-to-one through the contraction,
so universality at the quotient adhesion transfers to the pulled-back
original shore.
-/

namespace HadwigerLean.RootedDensity

universe u v

/-- An H-universal strict-far shore in an edge contraction lifts to an
H-universal original shore at the pulled-back adhesion. -/
theorem universalAtRightShore_of_contraction_strictFar
    {V : Type u} {W : Type v} [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    {a b : V} (hab : G.Adj a b)
    (S : VertexSeparation (edgeContraction G hab))
    (hnone : none ∈ S.strictRight)
    (huni : UniversalAtRightShore H S) :
    UniversalAtRightShore H
      (Linkedness.partitionPullbackSeparation
        (edgeContractionPartition G hab) S) := by
  classical
  let C := edgeContractionPartition G hab
  let T := Linkedness.partitionPullbackSeparation C S
  have hnoneSep : none ∉ S.separator := by
    intro h
    exact hnone.2 h.1
  change UniversalAt ((edgeContraction G hab).induce S.right) H
    (Linkedness.separationBoundaryFinset S) at huni
  change UniversalAt (G.induce T.right) H
    (Linkedness.separationBoundaryFinset T)
  intro Y root hrootinj hrange
  let qroot : ↥(Y : Set W) → S.right := fun i =>
    ⟨Linkedness.partitionIndex C (root i : V), root i |>.property⟩
  have hrootBoundary (i : ↥(Y : Set W)) :
      root i ∈ Linkedness.separationBoundaryFinset T := by
    change root i ∈ (Linkedness.separationBoundaryFinset T : Set T.right)
    rw [← hrange]
    exact ⟨i, rfl⟩
  have hindexSep (i : ↥(Y : Set W)) :
      Linkedness.partitionIndex C (root i : V) ∈ S.separator := by
    constructor
    · exact (Linkedness.mem_separationBoundaryFinset T (root i)).mp
        (hrootBoundary i)
    · exact (root i).property
  have hqinj : Function.Injective qroot := by
    intro i j heq
    apply hrootinj
    apply Subtype.ext
    apply Linkedness.edgeContraction_index_inj_away hab
    · intro hidx
      exact hnoneSep (hidx ▸ hindexSep i)
    · exact congrArg Subtype.val heq
  have hqrange : Set.range qroot =
      (Linkedness.separationBoundaryFinset S : Set S.right) := by
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      exact (Linkedness.mem_separationBoundaryFinset S (qroot i)).mpr
        (hindexSep i).1
    · intro hq
      have hqSep : (q : EdgeContractionVertex a b) ∈ S.separator :=
        ⟨(Linkedness.mem_separationBoundaryFinset S q).mp hq, q.property⟩
      cases hqv : (q : EdgeContractionVertex a b) with
      | none =>
          exact False.elim (hnoneSep (hqv ▸ hqSep))
      | some z =>
          have hzidx : Linkedness.partitionIndex C z.1 = some z := by
            exact Linkedness.edgeContraction_index_some hab z.1 z.2.1 z.2.2
          have hzR : z.1 ∈ T.right := by
            change Linkedness.partitionIndex C z.1 ∈ S.right
            rw [hzidx]
            exact hqv ▸ q.property
          let x : T.right := ⟨z.1, hzR⟩
          have hxB : x ∈ Linkedness.separationBoundaryFinset T := by
            apply (Linkedness.mem_separationBoundaryFinset T x).mpr
            change Linkedness.partitionIndex C z.1 ∈ S.left
            rw [hzidx]
            exact hqv ▸ hqSep.1
          have hxB' : x ∈ (Linkedness.separationBoundaryFinset T : Set T.right) := hxB
          rw [← hrange] at hxB'
          obtain ⟨i, hi⟩ := hxB'
          refine ⟨i, ?_⟩
          apply Subtype.ext
          change Linkedness.partitionIndex C (root i : V) = (q : EdgeContractionVertex a b)
          rw [hi, hzidx]
          exact hqv.symm
  obtain ⟨M⟩ := huni Y qroot hqinj hqrange
  exact ⟨rootedMinor_liftPartitionInduce C S.right qroot M root
    (fun i => Linkedness.partitionIndex_mem C (root i : V))⟩


/-- A universal strict-far quotient shore contradicts the absence of
H-rigid separations in the original graph. -/
theorem no_universal_contraction_strictFar_of_no_rigid
    {V : Type u} {W : Type v} [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (X : Finset V)
    (hX : X.card ≤ Fintype.card W)
    (hno : ∀ T : VertexSeparation G,
      (X : Set V) ⊆ T.left → ¬ RigidSeparation H T)
    {a b : V} (hab : G.Adj a b)
    (S : VertexSeparation (edgeContraction G hab))
    (hroot : (Linkedness.partitionIndex
      (edgeContractionPartition G hab) '' (X : Set V)) ⊆ S.left)
    (hsep : Nat.card S.separator <
      Nat.card (Linkedness.partitionIndex
        (edgeContractionPartition G hab) '' (X : Set V)))
    (hnone : none ∈ S.strictRight)
    (huni : UniversalAtRightShore H S) : False := by
  classical
  let C := edgeContractionPartition G hab
  let T := Linkedness.partitionPullbackSeparation C S
  have hrootT : (X : Set V) ⊆ T.left := by
    intro x hx
    exact hroot ⟨x, hx, rfl⟩
  have hnoneSep : none ∉ S.separator := by
    intro hs
    exact hnone.2 hs.1
  have hcard : Nat.card T.separator = Nat.card S.separator :=
    Linkedness.edgeContraction_pullback_separator_card_away hab S hnoneSep
  have hsizeImage : Nat.card
      (Linkedness.partitionIndex C '' (X : Set V)) ≤ X.card := by
    simpa only [Nat.card_coe_set_eq, Set.ncard_coe_finset] using
      Set.ncard_image_le (Set.toFinite (X : Set V))
  have hsepH : Nat.card T.separator ≤ Fintype.card W := by
    change Nat.card S.separator <
      Nat.card (Linkedness.partitionIndex C '' (X : Set V)) at hsep
    omega
  have hTfar : T.strictRight.Nonempty := by
    refine ⟨a, ?_⟩
    constructor
    · change Linkedness.partitionIndex C a ∈ S.right
      rw [Linkedness.edgeContraction_index_left hab]
      exact hnone.1
    · change Linkedness.partitionIndex C a ∉ S.left
      rw [Linkedness.edgeContraction_index_left hab]
      exact hnone.2
  have hTuni : UniversalAtRightShore H T :=
    universalAtRightShore_of_contraction_strictFar G H hab S hnone huni
  exact hno T hrootT ⟨hTfar, hsepH, hTuni⟩
end HadwigerLean.RootedDensity