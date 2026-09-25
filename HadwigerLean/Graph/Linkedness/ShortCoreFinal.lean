import HadwigerLean.Graph.Linkedness.ShortCoreResidual
import HadwigerLean.Graph.Linkedness.ShortCoreResidualDegree
import HadwigerLean.Graph.Linkedness.InducedTransport

/-!
# The short-path small-core argument
-/

namespace HadwigerLean
namespace Linkedness

set_option maxHeartbeats 1000000

/-- A disconnected graph meeting the 14k/5k bounds contains a
k-linked induced subgraph of order at most 7k. -/
theorem linked_side_of_nonreachable
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ)
    (horder : Fintype.card V ≤ 14 * k)
    (hdegree : ∀ x, 5 * k ≤ H.degree x)
    (u v : V) (huv : ¬ H.Reachable u v) :
    ∃ S : Finset V, S.Nonempty ∧ S.card ≤ 7 * k ∧
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
  exact linked_side_of_dense_anticomplete_partition H k
    horder hdegree A B hcover hdisjoint hA hB hnoedge

namespace ShortPartial

/-- The two exterior neighborhoods of an unused pair lie in
different components of the residual graph when the partial
linkage is maximal. -/
theorem no_residual_reachable_between_pair_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} {P : IndexedPairs (Fin k) V}
    (C : ShortPartial G P (terminalFinset P))
    (hP : P.DisjointTerminals)
    (hmax : ∀ D : ShortPartial G P (terminalFinset P),
      D.used.card ≤ C.used.card)
    (hdegreeR : ∀ x : {y : V | y ∉ C.occupied},
      5 * k ≤ (G.induce {y : V | y ∉ C.occupied}).degree x)
    (horderR : Fintype.card {y : V | y ∉ C.occupied} ≤ 14 * k)
    (i : Fin k) (hi : i ∉ C.used)
    (u v : {y : V | y ∉ C.occupied})
    (hs : G.Adj (P.start i) u.1)
    (ht : G.Adj v.1 (P.finish i)) :
    ¬ (G.induce {y : V | y ∉ C.occupied}).Reachable u v := by
  intro hr
  obtain ⟨p, hlen⟩ := dense_reachable_path_length_le_five
    (G.induce {y : V | y ∉ C.occupied}) k hdegreeR horderR hr
  obtain ⟨D, hlarger⟩ :=
    C.extend_of_residual_path hP i hi u v hs ht p hlen
  have hsmall := hmax D
  omega


/-- A vertex whose degree exceeds the occupied set has an exterior
neighbor. -/
theorem exterior_neighbor_of_degree_gt_occupied
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} {P : IndexedPairs (Fin k) V}
    (C : ShortPartial G P (terminalFinset P))
    (s : V) (hdegree : C.occupied.card < G.degree s) :
    ∃ u : {x : V | x ∉ C.occupied}, G.Adj s u.1 := by
  classical
  by_contra h
  have hsub : G.neighborFinset s ⊆ C.occupied := by
    intro u hu
    by_contra hnot
    have hadj : G.Adj s u := (G.mem_neighborFinset s u).mp hu
    exact h ⟨⟨u,hnot⟩,hadj⟩
  have hcard := Finset.card_le_card hsub
  rw [G.card_neighborFinset_eq_degree] at hcard
  omega

/-- An optimal short partial linkage with an unused pair yields a
nonempty linked component in its residual graph. -/
theorem linked_residual_side
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} {P : IndexedPairs (Fin k) V}
    (C : ShortPartial G P (terminalFinset P))
    (hP : P.DisjointTerminals)
    (hne : ∀ i, P.start i ≠ P.finish i)
    (hmax : ∀ D : ShortPartial G P (terminalFinset P),
      D.used.card ≤ C.used.card)
    (hminimal : ∀ D : ShortPartial G P (terminalFinset P),
      D.used.card = C.used.card →
      C.totalLength ≤ D.totalLength)
    (hocc : C.occupied.card < 8 * k)
    (hdegree : ∀ x, 8 * k ≤ G.degree x)
    (horder : Fintype.card V ≤ 16 * k)
    (i : Fin k) (hi : i ∉ C.used) :
    ∃ S : Finset {x : V | x ∉ C.occupied},
      S.Nonempty ∧ S.card ≤ 7 * k ∧
      KLinked ((G.induce {x : V | x ∉ C.occupied}).induce
        (S : Set {x : V | x ∉ C.occupied})) k := by
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
  exact linked_side_of_nonreachable (G.induce R) k
    horderR hdegreeR u v hnotReach

/-- A partial linkage with no full extension leaves one index unused. -/
theorem exists_unused_index
    {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ}
    {P : IndexedPairs (Fin k) V} {X : Finset V}
    (C : ShortPartial G P X)
    (hnot : ¬ Nonempty (IndexedLinkage G P)) :
    ∃ i : Fin k, i ∉ C.used := by
  classical
  by_contra h
  have hfull : C.used = Finset.univ := by
    ext i
    simp only [Finset.mem_univ, iff_true]
    by_contra hi
    exact h ⟨i,hi⟩
  have hcardfull : C.used.card = k := by
    rw [hfull]
    simp
  exact hnot ⟨C.toLinkageOfFull hcardfull⟩

/-- A failed k-linkage in a 16k-vertex, minimum-degree-8k
graph produces a nonempty k-linked side after deleting the
short partial linkage. -/
theorem linked_residual_side_of_failed_linkage
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (k : ℕ) (P : IndexedPairs (Fin k) V)
    (hP : P.DisjointTerminals)
    (hne : ∀ i, P.start i ≠ P.finish i)
    (hnot : ¬ Nonempty (IndexedLinkage G P))
    (hdegree : ∀ x, 8 * k ≤ G.degree x)
    (horder : Fintype.card V ≤ 16 * k) :
    ∃ C : ShortPartial G P (terminalFinset P),
      ∃ S : Finset {x : V | x ∉ C.occupied},
        S.Nonempty ∧ S.card ≤ 7 * k ∧
        KLinked ((G.induce {x : V | x ∉ C.occupied}).induce
          (S : Set {x : V | x ∉ C.occupied})) k := by
  classical
  obtain ⟨C,hmax,hminimal⟩ :=
    exists_optimal_short_partial (G := G) P (terminalFinset P)
  obtain ⟨i,hi⟩ := C.exists_unused_index hnot
  have hX : (terminalFinset P).card = 2 * k :=
    terminalFinset_card_eq_two_mul k P hP hne
  have hterm : ∀ j, P.terminals j ⊆
      (terminalFinset P : Set V) :=
    terminals_subset_terminalFinset P
  have hoccBound := C.occupied_card_le hX hterm hne
  have hused := C.card_used_le_sub_one hnot
  have hk : 0 < k := by
    have := i.isLt
    omega
  have hocc : C.occupied.card < 8 * k := by omega
  obtain ⟨S,hS⟩ :=
    C.linked_residual_side hP hne hmax hminimal
      hocc hdegree horder i hi
  exact ⟨C,S,hS⟩
end ShortPartial

/-- Failure of whole-graph linkedness exposes a nonempty linked
side of a twice-induced residual graph. -/
theorem exists_nested_induced_core_of_not_kLinked
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ)
    (hdegree : ∀ x, 8 * k ≤ G.degree x)
    (horder : Fintype.card V ≤ 16 * k)
    (hnot : ¬ KLinked G k) :
    ∃ P : IndexedPairs (Fin k) V,
      ∃ C : ShortPartial G P (terminalFinset P),
        ∃ S : Finset {x : V | x ∉ C.occupied},
          S.Nonempty ∧ S.card ≤ 7 * k ∧
          KLinked ((G.induce {x : V | x ∉ C.occupied}).induce
            (S : Set {x : V | x ∉ C.occupied})) k := by
  unfold KLinked at hnot
  push Not at hnot
  obtain ⟨P,hP,hne,hfailed⟩ := hnot
  have hnotL : ¬ Nonempty (IndexedLinkage G P) := by
    rintro ⟨L⟩
    exact hfailed.false L
  obtain ⟨C,S,hS⟩ :=
    ShortPartial.linked_residual_side_of_failed_linkage
      k P hP hne hnotL hdegree horder
  exact ⟨P,C,S,hS⟩

/-- In a 16k-vertex graph of minimum degree at least 8k,
either the whole graph is k-linked or it contains a nonempty
k-linked induced subgraph on at most 7k vertices. -/
theorem kLinked_or_contains_small_kLinked_induced
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ)
    (hdegree : ∀ x, 8 * k ≤ G.degree x)
    (horder : Fintype.card V ≤ 16 * k) :
    KLinked G k ∨
      ∃ T : Finset V, T.Nonempty ∧ T.card ≤ 7 * k ∧
        KLinked (G.induce (T : Set V)) k := by
  classical
  by_cases hG : KLinked G k
  · exact Or.inl hG
  · right
    obtain ⟨P,C,S,hSnon,hScard,hSlinked⟩ :=
      exists_nested_induced_core_of_not_kLinked G k
        hdegree horder hG
    let R : Set V := {x | x ∉ C.occupied}
    let T : Finset V := S.image (fun x : R => x.1)
    have hTnon : T.Nonempty := by
      obtain ⟨u,hu⟩ := hSnon
      exact ⟨u.1, Finset.mem_image.mpr ⟨u,hu,rfl⟩⟩
    have hTcard : T.card ≤ 7 * k := by
      exact (Finset.card_image_le).trans hScard
    have hTset : (T : Set V) = Subtype.val '' (S : Set R) := by
      ext v
      simp [T]
    have hTlinked : KLinked (G.induce (T : Set V)) k := by
      rw [hTset]
      exact kLinked_induce_image_of_nested G R (S : Set R) k hSlinked
    exact ⟨T,hTnon,hTcard,hTlinked⟩

/-- Every nonempty graph of order at most 16k and minimum
degree at least 8k contains a nonempty induced k-linked core. -/
theorem exists_kLinked_induced_of_order_le_sixteen_mul
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ)
    (hdegree : ∀ x, 8 * k ≤ G.degree x)
    (horder : Fintype.card V ≤ 16 * k) :
    ∃ T : Finset V, T.Nonempty ∧ T.card ≤ 16 * k ∧
      KLinked (G.induce (T : Set V)) k := by
  classical
  rcases kLinked_or_contains_small_kLinked_induced G k hdegree horder with
    hG | ⟨T,hTnon,hTcard,hTlinked⟩
  · refine ⟨Finset.univ, Finset.univ_nonempty, ?_, ?_⟩
    · simpa using horder
    · have hset : ((Finset.univ : Finset V) : Set V) = Set.univ := by
        ext x
        simp
      rw [hset]
      exact kLinked_of_iso (G.induceUnivIso).symm k hG
  · refine ⟨T,hTnon,?_,hTlinked⟩
    omega
end Linkedness
end HadwigerLean
