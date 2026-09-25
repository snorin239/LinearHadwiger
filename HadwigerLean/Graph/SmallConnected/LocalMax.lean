import HadwigerLean.Graph.SmallConnected.LocalEndpoint
import Mathlib.Tactic

/-!
# A largest small connected set with low contraction loss
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

theorem connectedSetContractionLoss_singleton
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    connectedSetContractionLoss G {v} = 0 := by
  classical
  have hinner : edgeCount (G.induce (({v} : Finset V) : Set V)) = 0 := by
    have hbound : edgeCount (G.induce (({v} : Finset V) : Set V)) ≤
        (Fintype.card ↥((({v} : Finset V) : Set V))).choose 2 := by
      rw [edgeCount_eq_card_edgeFinset]
      exact (G.induce (({v} : Finset V) : Set V)).card_edgeFinset_le_card_choose_two
    have hcard : Fintype.card ↥((({v} : Finset V) : Set V)) = 1 := by
      simpa using Fintype.card_coe ({v} : Finset V)
    have hchoose : (Fintype.card ↥((({v} : Finset V) : Set V))).choose 2 = 0 := by
      rw [hcard]
      norm_num
    rw [hchoose] at hbound
    exact Nat.eq_zero_of_le_zero hbound
  have hdup : contractionDuplicateCost G {v} = 0 := by
    unfold contractionDuplicateCost
    apply Finset.sum_eq_zero
    intro w hw
    have hle : (G.neighborFinset w ∩ ({v} : Finset V)).card ≤ 1 := by
      exact (Finset.card_le_card Finset.inter_subset_right).trans_eq
        (Finset.card_singleton v)
    omega
  simp [connectedSetContractionLoss, hinner, hdup]

noncomputable def LowLossConnectedSet
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (h p : ℕ) (H : Finset V) : Prop :=
  H.Nonempty ∧ H ⊆ S ∧ H.card ≤ h ∧
    (G.induce (H : Set V)).Connected ∧
      connectedSetContractionLoss G H ≤ p * (H.card - 1)

theorem exists_maximal_lowLossConnectedSet
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (h p : ℕ)
    (hS : S.Nonempty) (hh : 1 ≤ h) :
    ∃ H : Finset V, LowLossConnectedSet G S h p H ∧
      ∀ H' : Finset V, LowLossConnectedSet G S h p H' →
        H'.card ≤ H.card := by
  classical
  let P : Set (Finset V) := {H | LowLossConnectedSet G S h p H}
  have hfinite : P.Finite := Set.toFinite P
  have hnonempty : P.Nonempty := by
    obtain ⟨v, hv⟩ := hS
    refine ⟨{v}, ?_⟩
    dsimp [P, LowLossConnectedSet]
    have hconn : (G.induce (({v} : Finset V) : Set V)).Connected := by
      haveI : Subsingleton ↥((({v} : Finset V) : Set V)) := by
        constructor
        intro a b
        apply Subtype.ext
        have ha : a.1 = v := by simpa using a.2
        have hb : b.1 = v := by simpa using b.2
        exact ha.trans hb.symm
      haveI : Nonempty ↥((({v} : Finset V) : Set V)) :=
        ⟨⟨v, by simp⟩⟩
      exact ⟨SimpleGraph.Preconnected.of_subsingleton⟩
    refine ⟨by simp, by simpa using hv, by simpa using hh, hconn, ?_⟩
    simp [connectedSetContractionLoss_singleton]
  obtain ⟨H, hHP, hmax⟩ :=
    hfinite.exists_maximalFor Finset.card P hnonempty
  refine ⟨H, hHP, ?_⟩
  intro H' hH'
  by_contra hnot
  have hlt : H.card < H'.card := Nat.lt_of_not_ge hnot
  have hback := hmax hH' hlt.le
  omega

/-- Adding a vertex adjacent to a connected induced set preserves
connectedness. -/
theorem connected_induce_insert_of_adjacent
    (G : SimpleGraph V) (H : Finset V) (v u : V)
    (hconn : (G.induce (H : Set V)).Connected)
    (hu : u ∈ H) (huv : G.Adj u v) :
    (G.induce ((insert v H : Finset V) : Set V)).Connected := by
  haveI : Subsingleton ↥({v} : Set V) := by
    constructor
    intro a b
    apply Subtype.ext
    have ha : a.1 = v := a.2
    have hb : b.1 = v := b.2
    exact ha.trans hb.symm
  have hsingle : (G.induce ({v} : Set V)).Preconnected :=
    SimpleGraph.Preconnected.of_subsingleton
  have h := G.connected_induce_union hconn.preconnected hsingle
    hu (by simp : v ∈ ({v} : Set V)) huv
  have hset : (((insert v H : Finset V) : Set V)) = (H : Set V) ∪ {v} := by
    ext x
    simp [or_comm]
  rw [hset]
  exact h

/-- Maximality makes every neighboring extension cost more than p per new vertex. -/
theorem maximal_lowLoss_extension_cost
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S X H : Finset V) (h p : ℕ)
    (hH : LowLossConnectedSet G S h p H)
    (hmax : ∀ H' : Finset V, LowLossConnectedSet G S h p H' →
      H'.card ≤ H.card)
    (hshort : H.card < h) :
    ∀ v ∈ localRPrime G H X S,
      p * H.card < connectedSetContractionLoss G (insert v H) := by
  classical
  intro v hv
  obtain ⟨hvR, hvS⟩ := Finset.mem_inter.mp hv
  obtain ⟨hvN, _⟩ := Finset.mem_sdiff.mp hvR
  obtain ⟨hvout, htouched⟩ := Finset.mem_filter.mp hvN
  have hvnotH : v ∉ H := by
    intro hvH
    exact (Finset.mem_compl.mp hvout) hvH
  obtain ⟨u, hu⟩ := Finset.card_pos.mp htouched
  have huH : u ∈ H := (Finset.mem_inter.mp hu).2
  have hVu : G.Adj v u := (G.mem_neighborFinset v u).mp
    (Finset.mem_inter.mp hu).1
  have hconn := connected_induce_insert_of_adjacent G H v u
    hH.2.2.2.1 huH hVu.symm
  have hcard : (insert v H).card = H.card + 1 :=
    by simp [hvnotH]
  by_contra hnot
  have hloss : connectedSetContractionLoss G (insert v H) ≤
      p * H.card := Nat.le_of_not_gt hnot
  have hgood : LowLossConnectedSet G S h p (insert v H) := by
    refine ⟨by simp, Finset.insert_subset hvS hH.2.1,
      ?_, hconn, ?_⟩
    · rw [hcard]
      omega
    · rw [hcard]
      simpa using hloss
  have hbound := hmax (insert v H) hgood
  rw [hcard] at hbound
  omega
end HadwigerLean
