import HadwigerLean.Graph.SmallConnected.Trimming
import HadwigerLean.Graph.DensityBasic
import Mathlib.Tactic

namespace HadwigerLean

universe u

private theorem double_sum_erase_add_two_row
    {V : Type u} [DecidableEq V] (S : Finset V) (v : V) (hv : v ∈ S)
    (f : V → V → ℝ) (hsym : ∀ x y, f x y = f y x)
    (hdiag : f v v = 0) :
    (∑ x ∈ S.erase v, ∑ y ∈ S.erase v, f x y) +
      2 * (∑ y ∈ S, f v y) =
        ∑ x ∈ S, ∑ y ∈ S, f x y := by
  classical
  let T := S.erase v
  have hvT : v ∉ T := Finset.notMem_erase v S
  have hS : S = insert v T := (Finset.insert_erase hv).symm
  rw [hS]
  rw [Finset.erase_insert hvT]
  simp only [Finset.sum_insert hvT]
  simp only [hdiag, zero_add, Finset.sum_add_distrib]
  have hcross : (∑ x ∈ T, f x v) = ∑ x ∈ T, f v x := by
    apply Finset.sum_congr rfl
    intro x hx
    exact hsym x v
  rw [hcross]
  ring


/-- Number of oriented edges from a vertex into a finite set, as a real. -/
noncomputable def internalNeighborWeight {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) : ℝ :=
  ∑ y ∈ S, if G.Adj v y then 1 else 0

/-- Half the total number of oriented edges inside a finite set. -/
noncomputable def inducedEdgeWeight {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : ℝ :=
  (∑ x ∈ S, internalNeighborWeight G S x) / 2

theorem internalNeighborWeight_eq_card
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) :
    internalNeighborWeight G S v =
      ((G.neighborFinset v ∩ S).card : ℝ) := by
  classical
  have hfilter : S.filter (G.Adj v) = G.neighborFinset v ∩ S := by
    ext y
    simp [G.mem_neighborFinset, and_comm]
  simp [internalNeighborWeight, hfilter]

theorem internalNeighborWeight_le_degree
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) :
    internalNeighborWeight G S v ≤ (G.degree v : ℝ) := by
  rw [internalNeighborWeight_eq_card]
  exact_mod_cast (Finset.card_le_card (Finset.inter_subset_left)).trans_eq
    (G.card_neighborFinset_eq_degree v)

theorem inducedEdgeWeight_erase_add_internal
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) (hv : v ∈ S) :
    inducedEdgeWeight G (S.erase v) + internalNeighborWeight G S v =
      inducedEdgeWeight G S := by
  classical
  let f : V → V → ℝ := fun x y => if G.Adj x y then 1 else 0
  have hsym : ∀ x y, f x y = f y x := by
    intro x y
    simp only [f]
    simp [G.adj_comm]
  have hdiag : f v v = 0 := by simp [f]
  have h := double_sum_erase_add_two_row S v hv f hsym hdiag
  dsimp [inducedEdgeWeight, internalNeighborWeight, f] at h ⊢
  linarith

/-- The Section 8 trimming lemma in the degree-sum formulation of its
surplus hypothesis. -/
theorem exists_trimmed_induced_finset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (r δ : ℝ) (hr : 2 < r) (hδ : 0 < δ)
    (hscore : (r - 1) * δ * (S.card : ℝ) +
      (∑ v ∈ S, (G.degree v : ℝ)) < r * inducedEdgeWeight G S) :
    ∃ T : Finset V, T.Nonempty ∧ T ⊆ S ∧
      (∀ v ∈ T, δ ≤ ((G.neighborFinset v ∩ T).card : ℝ)) ∧
      (∀ v ∈ T, (G.degree v : ℝ) ≤
        r * ((G.neighborFinset v ∩ T).card : ℝ)) := by
  classical
  obtain ⟨T, hTne, hTS, hmin, hratio⟩ :=
    exists_minimal_positive_surplus_set S (inducedEdgeWeight G)
      (fun v => (G.degree v : ℝ)) (internalNeighborWeight G)
      r δ hr hδ (by simp [inducedEdgeWeight])
      (by intro U hUS v hv; exact inducedEdgeWeight_erase_add_internal G U v hv)
      (by intro U hUS v hv; exact internalNeighborWeight_le_degree G U v)
      hscore
  refine ⟨T, hTne, hTS, ?_, ?_⟩
  · intro v hv
    simpa only [internalNeighborWeight_eq_card] using hmin v hv
  · intro v hv
    simpa only [internalNeighborWeight_eq_card] using hratio v hv

/-- The oriented-edge normalization agrees with the ordinary induced edge
count. -/
theorem inducedEdgeWeight_eq_edgeCount
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    inducedEdgeWeight G S = (edgeCount (G.induce (S : Set V)) : ℝ) := by
  classical
  letI : Fintype ↥(S : Set V) := Subtype.fintype _
  have hdegree (x : ↥(S : Set V)) :
      (G.induce (S : Set V)).degree x =
        (G.neighborFinset x.1 ∩ S).card := by
    have hmap := G.map_neighborFinset_induce (s := (S : Set V)) x
    have hcard := congrArg Finset.card hmap
    simpa using hcard
  have hsum :
      (∑ x ∈ S, (G.neighborFinset x ∩ S).card) =
        ∑ x : ↥(S : Set V), (G.induce (S : Set V)).degree x := by
    rw [Finset.sum_subtype S (by intro x; rfl)
      (fun x => (G.neighborFinset x ∩ S).card)]
    apply Finset.sum_congr rfl
    intro x hx
    exact (hdegree x).symm
  have hhand :
      (∑ x : ↥(S : Set V), (G.induce (S : Set V)).degree x) =
        2 * edgeCount (G.induce (S : Set V)) := by
    simpa only [edgeCount_eq_card_edgeFinset] using
      (G.induce (S : Set V)).sum_degrees_eq_twice_card_edges
  have hsumR :
      (∑ x ∈ S, ((G.neighborFinset x ∩ S).card : ℝ)) =
        2 * (edgeCount (G.induce (S : Set V)) : ℝ) := by
    exact_mod_cast hsum.trans hhand
  simp only [inducedEdgeWeight, internalNeighborWeight_eq_card]
  linarith

/-- Graph-specific trimming with the ordinary induced edge count. The
hypothesis is Equation (8.2) after replacing the boundary count by the
ambient degree sum minus twice the induced edge count. -/
theorem exists_trimmed_induced_finset_of_edge_score
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (r δ : ℝ) (hr : 2 < r) (hδ : 0 < δ)
    (hscore : (r - 1) * δ * (S.card : ℝ) +
      (∑ v ∈ S, (G.degree v : ℝ)) <
        r * (edgeCount (G.induce (S : Set V)) : ℝ)) :
    ∃ T : Finset V, T.Nonempty ∧ T ⊆ S ∧
      (∀ v ∈ T, δ ≤ ((G.neighborFinset v ∩ T).card : ℝ)) ∧
      (∀ v ∈ T, (G.degree v : ℝ) ≤
        r * ((G.neighborFinset v ∩ T).card : ℝ)) := by
  apply exists_trimmed_induced_finset G S r δ hr hδ
  simpa only [inducedEdgeWeight_eq_edgeCount] using hscore

/-- Adding one vertex to an induced graph adds exactly its neighbors already
in the set. -/
theorem edgeCount_induce_insert_add_neighbors
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) (hv : v ∉ S) :
    edgeCount (G.induce ((insert v S : Finset V) : Set V)) =
      edgeCount (G.induce (S : Set V)) +
        (G.neighborFinset v ∩ S).card := by
  have h := inducedEdgeWeight_erase_add_internal G (insert v S) v
    (Finset.mem_insert_self v S)
  rw [Finset.erase_insert hv,
    inducedEdgeWeight_eq_edgeCount, inducedEdgeWeight_eq_edgeCount,
    internalNeighborWeight_eq_card] at h
  have hnei : G.neighborFinset v ∩ insert v S =
      G.neighborFinset v ∩ S := by
    ext x
    by_cases hx : x = v
    · subst x
      simp
    · simp
  rw [hnei] at h
  exact_mod_cast h.symm
end HadwigerLean
