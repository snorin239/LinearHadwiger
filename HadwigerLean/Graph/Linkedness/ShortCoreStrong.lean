import HadwigerLean.Graph.Linkedness.ShortCoreFinal
import Mathlib.Tactic

/-!
# Retaining the degree guarantee of the linked residual core
-/

namespace HadwigerLean
namespace Linkedness

set_option maxHeartbeats 1000000

/-- The small side of an anticomplete dense partition retains minimum
degree five times k, in addition to being k-linked. -/
theorem dense_linked_side_of_anticomplete_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ)
    (horder : Fintype.card V ≤ 14 * k)
    (hdegree : ∀ v, 5 * k ≤ G.degree v)
    (A B : Finset V)
    (hcover : A ∪ B = Finset.univ)
    (hdisjoint : Disjoint A B)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hnoedge : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y) :
    ∃ S : Finset V, S.Nonempty ∧ S.card ≤ 7 * k ∧
      (∀ v : (S : Set V), 5 * k ≤ (G.induce (S : Set V)).degree v) ∧
      KLinked (G.induce (S : Set V)) k := by
  classical
  have hsum : A.card + B.card = Fintype.card V := by
    have hcard := Finset.card_union_of_disjoint hdisjoint
    rw [hcover] at hcard
    simpa only [Finset.card_univ] using hcard.symm
  have hcoverSet : (A : Set V) ∪ (B : Set V) = Set.univ := by
    simpa using congrArg (fun s : Finset V => (s : Set V)) hcover
  have hsmall : A.card ≤ 7 * k ∨ B.card ≤ 7 * k := by omega
  rcases hsmall with hA_small | hB_small
  · have hdegA : ∀ v : (A : Set V), 5 * k ≤
        (G.induce (A : Set V)).degree v := by
      intro v
      rw [degree_induce_of_anticomplete_partition G (A : Set V) (B : Set V)
        hcoverSet hnoedge v]
      exact hdegree v.1
    refine ⟨A, hA, hA_small, hdegA, ?_⟩
    exact kLinked_of_five_k_degree_seven_k_order
      (G.induce (A : Set V)) k hdegA (by simpa using hA_small)
  · have hnoedge' : ∀ x ∈ B, ∀ y ∈ A, ¬ G.Adj x y := by
      intro x hx y hy hxy
      exact hnoedge y hy x hx hxy.symm
    have hcover' : (B : Set V) ∪ (A : Set V) = Set.univ := by
      simpa only [Set.union_comm] using hcoverSet
    have hdegB : ∀ v : (B : Set V), 5 * k ≤
        (G.induce (B : Set V)).degree v := by
      intro v
      rw [degree_induce_of_anticomplete_partition G (B : Set V) (A : Set V)
        hcover' hnoedge' v]
      exact hdegree v.1
    refine ⟨B, hB, hB_small, hdegB, ?_⟩
    exact kLinked_of_five_k_degree_seven_k_order
      (G.induce (B : Set V)) k hdegB (by simpa using hB_small)

/-- The dense linked side has at least twice k vertices. -/
theorem dense_linked_side_card_ge_two_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (S : Finset V) (hS : S.Nonempty)
    (hdegree : ∀ v : (S : Set V),
      5 * k ≤ (G.induce (S : Set V)).degree v) :
    2 * k ≤ S.card := by
  classical
  obtain ⟨v,hv⟩ := hS
  let w : (S : Set V) := ⟨v,hv⟩
  have hlt := (G.induce (S : Set V)).degree_lt_card_verts w
  have hcard : Fintype.card (S : Set V) = S.card := by simp
  have hdeg := hdegree w
  omega


/-- A disconnected residual graph meeting the 14k/5k bounds contains a
linked side retaining the five-k degree guarantee. -/
theorem dense_linked_side_of_nonreachable
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ)
    (horder : Fintype.card V ≤ 14 * k)
    (hdegree : ∀ x, 5 * k ≤ H.degree x)
    (u v : V) (huv : ¬ H.Reachable u v) :
    ∃ S : Finset V, S.Nonempty ∧ 2 * k ≤ S.card ∧ S.card ≤ 7 * k ∧
      (∀ x : (S : Set V), 5 * k ≤ (H.induce (S : Set V)).degree x) ∧
      KLinked (H.induce (S : Set V)) k := by
  classical
  let A : Finset V := Finset.univ.filter (fun x => H.Reachable u x)
  let B : Finset V := Aᶜ
  have hcover : A ∪ B = Finset.univ := Finset.union_compl A
  have hdisjoint : Disjoint A B := by
    change Disjoint A Aᶜ
    exact disjoint_compl_right
  have hnoedge : ∀ x ∈ A, ∀ y ∈ B, ¬ H.Adj x y := by
    intro x hx y hy hxy
    have hux : H.Reachable u x := (Finset.mem_filter.mp hx).2
    have huy : H.Reachable u y := hux.trans hxy.reachable
    have hyA : y ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huy⟩
    exact (Finset.mem_compl.mp hy) hyA
  have hA : A.Nonempty := by
    refine ⟨u, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl u⟩
  have hB : B.Nonempty := by
    refine ⟨v, ?_⟩
    apply Finset.mem_compl.mpr
    intro hvA
    exact huv (Finset.mem_filter.mp hvA).2
  obtain ⟨S,hSnon,hScard,hSdeg,hSlinked⟩ :=
    dense_linked_side_of_anticomplete_partition H k horder hdegree
      A B hcover hdisjoint hA hB hnoedge
  exact ⟨S,hSnon,dense_linked_side_card_ge_two_mul H k S hSnon hSdeg,
    hScard,hSdeg,hSlinked⟩


namespace ShortPartial

/-- An unused pair of an optimal short partial linkage leaves a dense
linked residual component, retaining all useful degree information. -/
theorem dense_linked_residual_side
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} {P : IndexedPairs (Fin k) V}
    (C : ShortPartial G P (terminalFinset P))
    (hP : P.DisjointTerminals)
    (hne : ∀ i, P.start i ≠ P.finish i)
    (hmax : ∀ D : ShortPartial G P (terminalFinset P),
      D.used.card ≤ C.used.card)
    (hminimal : ∀ D : ShortPartial G P (terminalFinset P),
      D.used.card = C.used.card → C.totalLength ≤ D.totalLength)
    (hocc : C.occupied.card < 8 * k)
    (hdegree : ∀ x, 8 * k ≤ G.degree x)
    (horder : Fintype.card V ≤ 16 * k)
    (i : Fin k) (hi : i ∉ C.used) :
    ∃ S : Finset {x : V | x ∉ C.occupied},
      S.Nonempty ∧ 2 * k ≤ S.card ∧ S.card ≤ 7 * k ∧
      (∀ x : (S : Set {x : V | x ∉ C.occupied}),
        5 * k ≤ ((G.induce {x : V | x ∉ C.occupied}).induce
          (S : Set {x : V | x ∉ C.occupied})).degree x) ∧
      KLinked ((G.induce {x : V | x ∉ C.occupied}).induce
        (S : Set {x : V | x ∉ C.occupied})) k := by
  classical
  let R : Set V := {x | x ∉ C.occupied}
  have horderR : Fintype.card R ≤ 14 * k :=
    C.residual_order_le_fourteen_mul hP hne horder
  have hdegreeR : ∀ x : R, 5 * k ≤ (G.induce R).degree x := by
    intro x
    exact C.residual_min_degree_ge_five_mul hP hne hminimal hdegree x
  have hstart : C.occupied.card < G.degree (P.start i) := by
    have hd := hdegree (P.start i)
    omega
  have hfinish : C.occupied.card < G.degree (P.finish i) := by
    have hd := hdegree (P.finish i)
    omega
  obtain ⟨u, hs⟩ := C.exterior_neighbor_of_degree_gt_occupied
    (P.start i) hstart
  obtain ⟨v, hvt⟩ := C.exterior_neighbor_of_degree_gt_occupied
    (P.finish i) hfinish
  have ht : G.Adj v.1 (P.finish i) := hvt.symm
  have hnotReach : ¬ (G.induce R).Reachable u v :=
    C.no_residual_reachable_between_pair_neighbors
      hP hmax hdegreeR horderR i hi u v hs ht
  exact dense_linked_side_of_nonreachable (G.induce R) k
    horderR hdegreeR u v hnotReach

end ShortPartial


/-- A failed full linkage yields a dense linked component in the twice
induced residual graph. -/
theorem exists_dense_nested_induced_core_of_not_kLinked
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ)
    (hdegree : ∀ x, 8 * k ≤ G.degree x)
    (horder : Fintype.card V ≤ 16 * k)
    (hnot : ¬ KLinked G k) :
    ∃ P : IndexedPairs (Fin k) V,
      ∃ C : ShortPartial G P (terminalFinset P),
        ∃ S : Finset {x : V | x ∉ C.occupied},
          S.Nonempty ∧ 2 * k ≤ S.card ∧ S.card ≤ 7 * k ∧
          (∀ x : (S : Set {x : V | x ∉ C.occupied}),
            5 * k ≤ ((G.induce {x : V | x ∉ C.occupied}).induce
              (S : Set {x : V | x ∉ C.occupied})).degree x) ∧
          KLinked ((G.induce {x : V | x ∉ C.occupied}).induce
            (S : Set {x : V | x ∉ C.occupied})) k := by
  classical
  unfold KLinked at hnot
  push Not at hnot
  obtain ⟨P,hP,hne,hfailed⟩ := hnot
  have hnotL : ¬ Nonempty (IndexedLinkage G P) := by
    rintro ⟨L⟩
    exact hfailed.false L
  obtain ⟨C,hmax,hminimal⟩ :=
    exists_optimal_short_partial (G := G) P (terminalFinset P)
  obtain ⟨i,hi⟩ := C.exists_unused_index hnotL
  have hX : (terminalFinset P).card = 2 * k :=
    terminalFinset_card_eq_two_mul k P hP hne
  have hterm : ∀ j, P.terminals j ⊆
      (terminalFinset P : Set V) :=
    terminals_subset_terminalFinset P
  have hoccBound := C.occupied_card_le hX hterm hne
  have hused := C.card_used_le_sub_one hnotL
  have hk : 0 < k := by
    have := i.isLt
    omega
  have hocc : C.occupied.card < 8 * k := by omega
  obtain ⟨S,hS⟩ := C.dense_linked_residual_side hP hne hmax hminimal
    hocc hdegree horder i hi
  exact ⟨P,C,S,hS⟩

end Linkedness
end HadwigerLean
