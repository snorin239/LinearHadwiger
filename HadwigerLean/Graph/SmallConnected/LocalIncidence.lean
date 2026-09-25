import HadwigerLean.Graph.SmallConnected.LocalCore
import Mathlib.Tactic

/-!
# Incidence accounting around one contracted connected set
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

private theorem neighbor_inter_card_as_sum
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (v : V) :
    (G.neighborFinset v ∩ A).card =
      ∑ w ∈ A, if G.Adj v w then 1 else 0 := by
  have heq : G.neighborFinset v ∩ A = A.filter (G.Adj v) := by
    ext w
    simp [G.mem_neighborFinset, and_comm]
  rw [heq]
  simp

theorem cross_incidence_symm
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    (∑ v ∈ A, (G.neighborFinset v ∩ B).card) =
      ∑ w ∈ B, (G.neighborFinset w ∩ A).card := by
  simp_rw [neighbor_inter_card_as_sum G]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro v hv
  simp [G.adj_comm]

theorem inside_incidence_twice_edges
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : Finset V) :
    (∑ v ∈ H, (G.neighborFinset v ∩ H).card) =
      2 * edgeCount (G.induce (H : Set V)) := by
  have h := inducedEdgeWeight_eq_edgeCount G H
  simp only [inducedEdgeWeight, internalNeighborWeight_eq_card] at h
  have hr : ((∑ v ∈ H, (G.neighborFinset v ∩ H).card : ℕ) : ℝ) =
      2 * (edgeCount (G.induce (H : Set V)) : ℝ) := by
    simp only [Nat.cast_sum]
    linarith
  exact_mod_cast hr

private theorem inside_external_incidence
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H S : Finset V) (hHS : H ⊆ S) :
    (∑ v ∈ H, (G.neighborFinset v ∩ S).card) =
      2 * edgeCount (G.induce (H : Set V)) +
        ∑ w ∈ S \ H, (G.neighborFinset w ∩ H).card := by
  let T := S \ H
  have hS : S = H ∪ T := by
    ext v
    simp only [Finset.mem_union, T, Finset.mem_sdiff]
    constructor
    · intro hv
      by_cases hh : v ∈ H
      · exact Or.inl hh
      · exact Or.inr ⟨hv, hh⟩
    · rintro (hv | hv)
      · exact hHS hv
      · exact hv.1
  have hdisj : Disjoint H T := by
    apply Finset.disjoint_left.mpr
    intro v hvH hvT
    exact (Finset.mem_sdiff.mp hvT).2 hvH
  have hpoint (v : V) :
      (G.neighborFinset v ∩ S).card =
        (G.neighborFinset v ∩ H).card +
          (G.neighborFinset v ∩ T).card := by
    simp_rw [neighbor_inter_card_as_sum G]
    rw [hS, Finset.sum_union hdisj]
  calc
    (∑ v ∈ H, (G.neighborFinset v ∩ S).card) =
        ∑ v ∈ H, ((G.neighborFinset v ∩ H).card +
          (G.neighborFinset v ∩ T).card) := by
            apply Finset.sum_congr rfl
            intro v hv
            exact hpoint v
    _ = (∑ v ∈ H, (G.neighborFinset v ∩ H).card) +
          (∑ v ∈ H, (G.neighborFinset v ∩ T).card) := Finset.sum_add_distrib
    _ = 2 * edgeCount (G.induce (H : Set V)) +
          ∑ w ∈ S \ H, (G.neighborFinset w ∩ H).card := by
            rw [inside_incidence_twice_edges,
              cross_incidence_symm]

/-- Incidences into the trimmed set are paid for by twice the contraction
loss and by the number of touched vertices that remain in that set. -/
theorem local_incidence_le_twice_loss_add_RPrime
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H X S : Finset V) (hHS : H ⊆ S) (hSX : Disjoint S X) :
    (∑ v ∈ H, (G.neighborFinset v ∩ S).card) ≤
      2 * connectedSetContractionLoss G H +
        (localRPrime G H X S).card := by
  classical
  let T := S \ H
  let m : V → ℕ := fun w => (G.neighborFinset w ∩ H).card
  let touched := T.filter (fun w => 0 < m w)
  have htouched : touched = localRPrime G H X S := by
    ext w
    simp only [touched, T, m, localRPrime, localR,
      contractedNeighborFinset, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_inter, Finset.mem_compl]
    constructor
    · rintro ⟨⟨hwS, hwH⟩, hwpos⟩
      exact ⟨⟨⟨hwH, hwpos⟩,
        Finset.disjoint_left.mp hSX hwS⟩, hwS⟩
    · rintro ⟨⟨⟨hwH, hwpos⟩, _⟩, hwS⟩
      exact ⟨⟨hwS, hwH⟩, hwpos⟩
  have hTsub : T ⊆ Hᶜ := by
    intro w hw
    exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hw).2
  have hterm (w : V) :
      m w = (m w - 1) + (if 0 < m w then 1 else 0) := by
    by_cases hm : m w = 0
    · simp [hm]
    · have hp : 0 < m w := Nat.pos_of_ne_zero hm
      simp [hp]
      omega
  have hsum : (∑ w ∈ T, m w) =
      (∑ w ∈ T, (m w - 1)) + touched.card := by
    calc
      (∑ w ∈ T, m w) =
          ∑ w ∈ T, ((m w - 1) + (if 0 < m w then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro w hw
            exact hterm w
      _ = (∑ w ∈ T, (m w - 1)) + touched.card := by
            rw [Finset.sum_add_distrib]
            simp [touched]
  have hdup : (∑ w ∈ T, (m w - 1)) ≤
      contractionDuplicateCost G H := by
    unfold contractionDuplicateCost
    exact Finset.sum_le_sum_of_subset_of_nonneg hTsub (by intros; omega)
  have hinside := inside_external_incidence G H S hHS
  change (∑ v ∈ H, (G.neighborFinset v ∩ S).card) ≤
    2 * (edgeCount (G.induce (H : Set V)) + contractionDuplicateCost G H) +
      (localRPrime G H X S).card
  rw [hinside, ← htouched]
  change 2 * edgeCount (G.induce (H : Set V)) + (∑ w ∈ T, m w) ≤
    2 * (edgeCount (G.induce (H : Set V)) + contractionDuplicateCost G H) +
      touched.card
  omega

end HadwigerLean
