import HadwigerLean.Graph.SmallConnected.ContractionCount
import HadwigerLean.Graph.DensityConnectivity
import Mathlib.Tactic

/-!
# Dense neighborhood produced by a maximal small contraction

This is the local counting step of Section 8.  The global packing argument
supplies the incidence estimate and the maximality hypothesis.
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

theorem contractedNeighborFinset_card_le_sum_degrees
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : Finset V) :
    (contractedNeighborFinset G H).card ≤ ∑ v ∈ H, G.degree v := by
  classical
  have hsub : contractedNeighborFinset G H ⊆
      H.biUnion (fun v => G.neighborFinset v) := by
    intro w hw
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (Finset.mem_filter.mp hw).2
    exact Finset.mem_biUnion.mpr ⟨v, (Finset.mem_inter.mp hv).2,
      (G.mem_neighborFinset v w).mpr (((G.mem_neighborFinset w v).mp (Finset.mem_inter.mp hv).1).symm)⟩
  calc
    (contractedNeighborFinset G H).card ≤
        (H.biUnion (fun v => G.neighborFinset v)).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ H, (G.neighborFinset v).card := Finset.card_biUnion_le
    _ = ∑ v ∈ H, G.degree v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact G.card_neighborFinset_eq_degree v

/-- The vertices in `R` are exactly the touched vertices outside the old
exceptional set `X`; `R'` additionally lies in the trimmed set `S`. -/
noncomputable def localR (G : SimpleGraph V) [DecidableRel G.Adj]
    (H X : Finset V) : Finset V := contractedNeighborFinset G H \ X

noncomputable def localRPrime (G : SimpleGraph V) [DecidableRel G.Adj]
    (H X S : Finset V) : Finset V := localR G H X ∩ S

/-- Incidence and maximality estimates force the contracted neighborhood
to have density at least `p/24`. -/
theorem local_dense_neighborhood
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H X S : Finset V) (p : ℕ)
    (hH : H.Nonempty) (hHS : H ⊆ S) (hSX : Disjoint S X)
    (hinc : ∑ v ∈ H, (G.neighborFinset v ∩ S).card ≤
      2 * connectedSetContractionLoss G H +
        (localRPrime G H X S).card)
    (hmin : ∀ v ∈ S, 4 * p ≤ (G.neighborFinset v ∩ S).card)
    (hratio : ∀ v ∈ S, G.degree v ≤
      3 * (G.neighborFinset v ∩ S).card)
    (hloss : connectedSetContractionLoss G H ≤ p * (H.card - 1))
    (hmax : ∀ v ∈ localRPrime G H X S,
      p * H.card < connectedSetContractionLoss G (insert v H))
    (hX : ∀ v ∈ S, 2 * (G.neighborFinset v ∩ X).card < p) :
    p * (localR G H X).card ≤
      24 * edgeCount (G.induce (localR G H X : Set V)) := by
  classical
  let R := localR G H X
  let Rp := localRPrime G H X S
  let a := ∑ v ∈ H, (G.neighborFinset v ∩ S).card
  have hRpS : Rp ⊆ S := Finset.inter_subset_right
  have hRpR : Rp ⊆ R := Finset.inter_subset_left
  have hsummin : 4 * p * H.card ≤ a := by
    dsimp [a]
    calc
      4 * p * H.card = ∑ v ∈ H, 4 * p := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ H, (G.neighborFinset v ∩ S).card := by
        apply Finset.sum_le_sum
        intro v hv
        exact hmin v (hHS hv)
  have hsumratio : (∑ v ∈ H, G.degree v) ≤ 3 * a := by
    dsimp [a]
    calc
      (∑ v ∈ H, G.degree v) ≤
          ∑ v ∈ H, 3 * (G.neighborFinset v ∩ S).card := by
        apply Finset.sum_le_sum
        intro v hv
        exact hratio v (hHS hv)
      _ = 3 * ∑ v ∈ H, (G.neighborFinset v ∩ S).card := by
        rw [Finset.mul_sum]
  have hRsum : R.card ≤ ∑ v ∈ H, G.degree v := by
    exact (Finset.card_le_card (Finset.sdiff_subset)).trans
      (contractedNeighborFinset_card_le_sum_degrees G H)
  have hHcard : 0 < H.card := Finset.card_pos.mpr hH
  have hRpLarge : a ≤ 2 * Rp.card := by
    have hpdiff : p * (H.card - 1) ≤ p * H.card :=
      Nat.mul_le_mul_left p (Nat.sub_le _ _)
    have hscale : 4 * p * H.card = 4 * (p * H.card) := by ring
    rw [hscale] at hsummin
    dsimp [a, Rp] at *
    omega
  have hRvsRp : R.card ≤ 6 * Rp.card := by omega
  have hcommon (v : V) (hv : v ∈ Rp) :
      p ≤ (contractedCommonNeighbors G H v).card := by
    have hvR : v ∈ R := hRpR hv
    have hvTouch : v ∈ contractedNeighborFinset G H :=
      Finset.mem_sdiff.mp hvR |>.1
    have hvH : v ∉ H := Finset.mem_compl.mp (Finset.mem_filter.mp hvTouch).1
    have hadj : 0 < (G.neighborFinset v ∩ H).card :=
      (Finset.mem_filter.mp hvTouch).2
    have hstep := connectedSetContractionLoss_insert G H v hvH hadj
    have hmaxv := hmax v hv
    have hcard : (H.card - 1) + 1 = H.card := Nat.sub_add_cancel hHcard
    have hmul : p * H.card = p * (H.card - 1) + p := by
      conv_lhs => rw [← hcard]
      ring
    omega
  have hcommonSub (v : V) (hv : v ∈ Rp) :
      contractedCommonNeighbors G H v ⊆
        (G.neighborFinset v ∩ R) ∪ (G.neighborFinset v ∩ X) := by
    intro w hw
    have hdata := Finset.mem_filter.mp hw
    have hwOutside : w ∉ H := by
      have hh := Finset.mem_erase.mp hdata.1
      exact Finset.mem_compl.mp hh.2
    have hwAdj : G.Adj v w := hdata.2.1
    by_cases hwX : w ∈ X
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset v w).mpr hwAdj, hwX⟩))
    · apply Finset.mem_union.mpr
      apply Or.inl
      apply Finset.mem_inter.mpr
      refine ⟨(G.mem_neighborFinset v w).mpr hwAdj, ?_⟩
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, hwX⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_compl.mpr hwOutside, hdata.2.2⟩
  have hdegreeR (v : V) (hv : v ∈ Rp) :
      p ≤ 2 * (G.neighborFinset v ∩ R).card := by
    have hcard := Finset.card_le_card (hcommonSub v hv)
    have hunion := Finset.card_union_le
      (G.neighborFinset v ∩ R) (G.neighborFinset v ∩ X)
    have hXv := hX v (hRpS hv)
    have hc := hcommon v hv
    omega
  have hsumRp : p * Rp.card ≤
      2 * ∑ v ∈ R, (G.neighborFinset v ∩ R).card := by
    calc
      p * Rp.card = ∑ v ∈ Rp, p := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ Rp, 2 * (G.neighborFinset v ∩ R).card := by
        apply Finset.sum_le_sum
        intro v hv
        exact hdegreeR v hv
      _ = 2 * ∑ v ∈ Rp, (G.neighborFinset v ∩ R).card := by
        rw [Finset.mul_sum]
      _ ≤ 2 * ∑ v ∈ R, (G.neighborFinset v ∩ R).card := by
        apply Nat.mul_le_mul_left
        exact Finset.sum_le_sum_of_subset_of_nonneg hRpR (by intros; omega)
  have hhand : ∑ v ∈ R, (G.neighborFinset v ∩ R).card =
      2 * edgeCount (G.induce (R : Set V)) := by
    have h := inducedEdgeWeight_eq_edgeCount G R
    simp only [inducedEdgeWeight, internalNeighborWeight_eq_card] at h
    have hr : ((∑ v ∈ R, (G.neighborFinset v ∩ R).card : ℕ) : ℝ) =
        2 * (edgeCount (G.induce (R : Set V)) : ℝ) := by
      simp only [Nat.cast_sum]
      linarith
    exact_mod_cast hr
  change p * R.card ≤ 24 * edgeCount (G.induce (R : Set V))
  have hmul := Nat.mul_le_mul_left p hRvsRp
  have hring : p * (6 * Rp.card) = 6 * (p * Rp.card) := by ring
  rw [hring] at hmul
  rw [hhand] at hsumRp
  omega

end HadwigerLean
