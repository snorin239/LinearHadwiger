import HadwigerLean.Graph.SmallConnected.LocalIncidence
import Mathlib.Tactic

/-!
# Mader endpoint for a maximal small contraction
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
/-- Positive minimum degree and low contraction loss force a touched
vertex outside the contracted set. -/
theorem localR_nonempty
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H X S : Finset V) (p : ℕ) (hp : 0 < p)
    (hH : H.Nonempty) (hHS : H ⊆ S) (hSX : Disjoint S X)
    (hmin : ∀ v ∈ S, 4 * p ≤ (G.neighborFinset v ∩ S).card)
    (hloss : connectedSetContractionLoss G H ≤ p * (H.card - 1)) :
    (localR G H X).Nonempty := by
  classical
  let R := localR G H X
  by_contra hnone
  have hRempty : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
  have hRpzero : (localRPrime G H X S).card = 0 := by
    change (R ∩ S).card = 0
    simp [hRempty]
  have hinc := local_incidence_le_twice_loss_add_RPrime
    G H X S hHS hSX
  rw [hRpzero, add_zero] at hinc
  have hsummin : 4 * (p * H.card) ≤
      ∑ v ∈ H, (G.neighborFinset v ∩ S).card := by
    calc
      4 * (p * H.card) = ∑ v ∈ H, 4 * p := by
        simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ ≤ ∑ v ∈ H, (G.neighborFinset v ∩ S).card := by
        apply Finset.sum_le_sum
        intro v hv
        exact hmin v (hHS hv)
  have hpdiff : p * (H.card - 1) ≤ p * H.card :=
    Nat.mul_le_mul_left p (Nat.sub_le _ _)
  have hcard : 0 < H.card := Finset.card_pos.mpr hH
  have hprod : 0 < p * H.card := Nat.mul_pos hp hcard
  omega

/-- The local Section 8 inequalities give a `k`-connected induced subgraph
inside the neighborhood of the contracted set, with order no larger than
that neighborhood. -/
theorem local_connected_witness
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H X S : Finset V) (p k : ℕ)
    (hk : 1 ≤ k) (hp : 48 * k ≤ p)
    (hH : H.Nonempty) (hHS : H ⊆ S) (hSX : Disjoint S X)
    (hmin : ∀ v ∈ S, 4 * p ≤ (G.neighborFinset v ∩ S).card)
    (hratio : ∀ v ∈ S, G.degree v ≤
      3 * (G.neighborFinset v ∩ S).card)
    (hloss : connectedSetContractionLoss G H ≤ p * (H.card - 1))
    (hmax : ∀ v ∈ localRPrime G H X S,
      p * H.card < connectedSetContractionLoss G (insert v H))
    (hX : ∀ v ∈ S, 2 * (G.neighborFinset v ∩ X).card < p) :
    ∃ (W : Type u) (_ : Fintype W) (f : W ↪ V),
      Fintype.card W ≤ (localR G H X).card ∧
      (∀ w, f w ∈ localR G H X) ∧
      VertexConnected (G.comap f) k := by
  classical
  let R := localR G H X
  have hRne : R.Nonempty :=
    localR_nonempty G H X S p (by omega) hH hHS hSX hmin hloss
  have hinc := local_incidence_le_twice_loss_add_RPrime
    G H X S hHS hSX
  have hden := local_dense_neighborhood G H X S p hH hHS hSX
    hinc hmin hratio hloss hmax hX
  change p * R.card ≤ 24 * edgeCount (G.induce (R : Set V)) at hden
  have hmul : (48 * k) * R.card ≤ p * R.card :=
    Nat.mul_le_mul_right R.card hp
  have hdense : 2 * k * R.card ≤
      edgeCount (G.induce (R : Set V)) := by
    have hring : (48 * k) * R.card = 24 * (2 * k * R.card) := by ring
    rw [hring] at hmul
    omega
  have hcardEq : Fintype.card ↥(R : Set V) = R.card := by
    simpa using Fintype.card_coe R
  have hcardR : 0 < Fintype.card ↥(R : Set V) := by
    rw [hcardEq]
    exact Finset.card_pos.mpr hRne
  have hdense' : 2 * k * Fintype.card ↥(R : Set V) ≤
      edgeCount (G.induce (R : Set V)) := by
    simpa only [hcardEq] using hdense
  obtain ⟨W, instW, f, hf⟩ :=
    hasVertexConnectedInducedSubgraph_of_edges_ge
      (G.induce (R : Set V)) k hk hcardR hdense'
  letI : Fintype W := instW
  refine ⟨W, instW,
    f.trans (Function.Embedding.subtype (· ∈ (R : Set V))), ?_, ?_, ?_⟩
  · change Fintype.card W ≤ R.card
    exact (Fintype.card_le_of_embedding f).trans_eq hcardEq
  · intro w
    exact (f w).property
  · exact hf

end HadwigerLean
