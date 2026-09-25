import HadwigerLean.Graph.SmallConnected.InducedAdj
import HadwigerLean.Graph.SmallConnected.ConnectedSetContraction
import Mathlib.Tactic

/-!
# Edge loss under contraction of a connected set

The loss is expressed from incidences in the original graph. This makes
one-vertex extension arithmetic independent of the quotient's vertex type.
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

private theorem card_neighbor_inter_insert
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v w : V) (hv : v ∉ S) :
    (G.neighborFinset w ∩ insert v S).card =
      (G.neighborFinset w ∩ S).card +
        (if G.Adj w v then 1 else 0) := by
  by_cases hwv : G.Adj w v
  · have hset : G.neighborFinset w ∩ insert v S =
        insert v (G.neighborFinset w ∩ S) := by
      ext x
      simp [Finset.mem_inter, Finset.mem_insert, hwv]
    rw [hset, Finset.card_insert_of_notMem]
    · simp [hwv]
    · simp [hv]
  · have hset : G.neighborFinset w ∩ insert v S =
        G.neighborFinset w ∩ S := by
      ext x
      simp [Finset.mem_inter, Finset.mem_insert, hwv]
    simp [hset, hwv]

private theorem pred_add_indicator (m : ℕ) (b : Prop) [Decidable b] :
    (m + if b then 1 else 0) - 1 =
      (m - 1) + if b ∧ 0 < m then 1 else 0 := by
  by_cases hb : b
  · by_cases hm : m = 0
    · simp [hb, hm]
    · have hm' : 0 < m := Nat.pos_of_ne_zero hm
      simp [hb, hm']
      omega
  · simp [hb]

/-- The surplus edges incident to a set that disappear when it is
contracted, counted one outside vertex at a time. -/
noncomputable def contractionDuplicateCost
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  ∑ w ∈ Sᶜ, ((G.neighborFinset w ∩ S).card - 1)

/-- Internal edges and duplicated external incidences are the contraction
loss. -/
noncomputable def connectedSetContractionLoss
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  edgeCount (G.induce (S : Set V)) + contractionDuplicateCost G S

/-- Outside common neighbors of `v` and the contracted set `S`. -/
noncomputable def contractedCommonNeighbors
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) : Finset V := by
  classical
  exact (Sᶜ).erase v |>.filter
    (fun w => G.Adj v w ∧ 0 < (G.neighborFinset w ∩ S).card)

private theorem compl_insert_eq_erase (S : Finset V) (v : V) :
    (insert v S)ᶜ = (Sᶜ).erase v := by
  ext w
  simp [Finset.mem_compl, Finset.mem_erase, Finset.mem_insert,
    and_comm, not_or]


private theorem duplicate_term_insert
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v w : V) (hv : v ∉ S) :
    (G.neighborFinset w ∩ insert v S).card - 1 =
      ((G.neighborFinset w ∩ S).card - 1) +
        (if G.Adj v w ∧ 0 < (G.neighborFinset w ∩ S).card
          then 1 else 0) := by
  rw [card_neighbor_inter_insert G S v w hv]
  rw [pred_add_indicator]
  simp only [G.adj_comm]

/-- The duplicated-incidence part of contraction loss changes by the
number of outside common neighbors, after removing the new vertex's old
contribution. -/
theorem contractionDuplicateCost_insert_add
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) (hv : v ∉ S) :
    contractionDuplicateCost G (insert v S) +
        ((G.neighborFinset v ∩ S).card - 1) =
      contractionDuplicateCost G S +
        (contractedCommonNeighbors G S v).card := by
  classical
  let C := (Sᶜ).erase v
  have hvC : v ∈ Sᶜ := by simp [hv]
  have hnew : contractionDuplicateCost G (insert v S) =
      ∑ w ∈ C, ((G.neighborFinset w ∩ insert v S).card - 1) := by
    simp only [contractionDuplicateCost, compl_insert_eq_erase, C]
  have hold : contractionDuplicateCost G S =
      (∑ w ∈ C, ((G.neighborFinset w ∩ S).card - 1)) +
        ((G.neighborFinset v ∩ S).card - 1) := by
    simpa only [contractionDuplicateCost, C] using
      (Finset.sum_erase_add (Sᶜ)
        (fun w => (G.neighborFinset w ∩ S).card - 1) hvC).symm
  have hcommon : (contractedCommonNeighbors G S v).card =
      ∑ w ∈ C,
        (if G.Adj v w ∧ 0 < (G.neighborFinset w ∩ S).card
          then 1 else 0) := by
    simp [contractedCommonNeighbors, C, Finset.sum_ite]
  have hsum : (∑ w ∈ C, ((G.neighborFinset w ∩ insert v S).card - 1)) =
      (∑ w ∈ C, ((G.neighborFinset w ∩ S).card - 1)) +
      (∑ w ∈ C,
        (if G.Adj v w ∧ 0 < (G.neighborFinset w ∩ S).card
          then 1 else 0)) := by
    simp_rw [duplicate_term_insert G S v _ hv]
    rw [Finset.sum_add_distrib]
  omega

/-- Adding a vertex adjacent to the contracted set costs one edge plus the
number of its outside common neighbors with that set. -/
theorem connectedSetContractionLoss_insert
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) (hv : v ∉ S)
    (hadj : 0 < (G.neighborFinset v ∩ S).card) :
    connectedSetContractionLoss G (insert v S) =
      connectedSetContractionLoss G S + 1 +
        (contractedCommonNeighbors G S v).card := by
  have hedges := edgeCount_induce_insert_add_neighbors G S v hv
  have hdup := contractionDuplicateCost_insert_add G S v hv
  have hm : (G.neighborFinset v ∩ S).card - 1 + 1 =
      (G.neighborFinset v ∩ S).card := Nat.sub_add_cancel hadj
  dsimp only [connectedSetContractionLoss]
  omega

/-- Outside vertices touched by the set to be contracted. -/
noncomputable def contractedNeighborFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  (Sᶜ).filter (fun w => 0 < (G.neighborFinset w ∩ S).card)

theorem contractionDuplicateCost_add_neighborCount
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    contractionDuplicateCost G S + (contractedNeighborFinset G S).card =
      ∑ w ∈ Sᶜ, (G.neighborFinset w ∩ S).card := by
  classical
  have hpoint (m : ℕ) : (m - 1) + (if 0 < m then 1 else 0) = m := by
    by_cases hm : m = 0
    · simp [hm]
    · have hpos : 0 < m := Nat.pos_of_ne_zero hm
      simp [hpos]
      omega
  have hcount : (contractedNeighborFinset G S).card =
      ∑ w ∈ Sᶜ,
        (if 0 < (G.neighborFinset w ∩ S).card then 1 else 0) := by
    simp [contractedNeighborFinset]
  rw [hcount]
  unfold contractionDuplicateCost
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  exact hpoint _
end HadwigerLean