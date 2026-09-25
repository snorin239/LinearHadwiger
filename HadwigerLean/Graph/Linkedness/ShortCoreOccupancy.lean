import HadwigerLean.Graph.Linkedness.ShortCoreMain
import Mathlib.Tactic

/-!
# Occupied-neighbor bound for an optimal short partial linkage
-/

namespace HadwigerLean
namespace Linkedness
namespace ShortPartial

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {k : ℕ} {P : IndexedPairs (Fin k) V}

/-- In an optimal short partial linkage, an outside vertex has at most
`3k` neighbors among all terminals and completed path vertices. -/
theorem outside_occupied_neighbor_card_le_three_mul
    (C : ShortPartial G P (terminalFinset P))
    (hP : P.DisjointTerminals)
    (hne : ∀ i, P.start i ≠ P.finish i)
    (hminimal : ∀ D : ShortPartial G P (terminalFinset P),
      D.used.card = C.used.card → C.totalLength ≤ D.totalLength)
    (x : V) (hx : x ∉ C.occupied) :
    (G.neighborFinset x ∩ C.occupied).card ≤ 3 * k := by
  classical
  let T : Finset V := (C.used.image P.start) ∪ (C.used.image P.finish)
  have hdis : Disjoint (C.used.image P.start) (C.used.image P.finish) := by
    apply Finset.disjoint_left.mpr
    intro v hvstart hvfinish
    obtain ⟨i, hi, hiv⟩ := Finset.mem_image.mp hvstart
    obtain ⟨j, hj, hjv⟩ := Finset.mem_image.mp hvfinish
    have heq : P.start i = P.finish j := hiv.trans hjv.symm
    by_cases hij : i = j
    · subst j
      exact hne i heq
    · have ha : P.start i ∈ P.terminals i := by
        simp [IndexedPairs.terminals]
      have hb : P.start i ∈ P.terminals j := by
        simp [IndexedPairs.terminals, heq]
      exact (Set.disjoint_left.mp (hP hij)) ha hb
  have hTcard : T.card = 2 * C.used.card := by
    simp only [T, Finset.card_union_of_disjoint hdis]
    rw [Finset.card_image_of_injective _ (IndexedPairs.start_injective hP),
      Finset.card_image_of_injective _ (IndexedPairs.finish_injective hP)]
    omega
  have hTsub : T ⊆ terminalFinset P := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      exact (mem_terminalFinset P _).mpr (Or.inl ⟨i, rfl⟩)
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      exact (mem_terminalFinset P _).mpr (Or.inr ⟨i, rfl⟩)
  let U : Finset V := terminalFinset P \ T
  have hXcard : (terminalFinset P).card = 2 * k :=
    terminalFinset_card_eq_two_mul k P hP hne
  have hused : C.used.card ≤ k := by
    simpa using (Finset.card_le_card (Finset.subset_univ C.used))
  have hUcard : U.card = 2 * (k - C.used.card) := by
    have hused : C.used.card ≤ k := by
      simpa using (Finset.card_le_card (Finset.subset_univ C.used))
    have hsdiff : U.card + T.card = (terminalFinset P).card := by
      exact Finset.card_sdiff_add_card_eq_card hTsub
    omega
  let paths : Finset V := (Finset.univ : Finset C.used).biUnion (fun i =>
    (C.path i : G.Walk (P.start i.1) (P.finish i.1)).support.toFinset)
  have hoccup : C.occupied ⊆ U ∪ paths := by
    intro v hv
    rw [Finset.mem_union]
    rcases Finset.mem_union.mp hv with hvX | hvrest
    · by_cases hvT : v ∈ T
      · rcases Finset.mem_union.mp hvT with hvstart | hvfinish
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hvstart
          right
          apply Finset.mem_biUnion.mpr
          refine ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
          exact List.mem_toFinset.mpr (C.path ⟨i, hi⟩).1.start_mem_support
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hvfinish
          right
          apply Finset.mem_biUnion.mpr
          refine ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
          exact List.mem_toFinset.mpr (C.path ⟨i, hi⟩).1.end_mem_support
      · left
        exact Finset.mem_sdiff.mpr ⟨hvX, hvT⟩
    · right
      obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hvrest
      apply Finset.mem_biUnion.mpr
      exact ⟨i, hi, (Finset.mem_sdiff.mp hvi).1⟩
  have hbound : (G.neighborFinset x ∩ C.occupied).card ≤
      U.card + ∑ i : C.used,
        (G.neighborFinset x ∩
          (C.path i : G.Walk (P.start i.1) (P.finish i.1)).support.toFinset).card := by
    have hsub : G.neighborFinset x ∩ C.occupied ⊆
        (G.neighborFinset x ∩ U) ∪
          ((Finset.univ : Finset C.used).biUnion (fun i =>
            G.neighborFinset x ∩
              (C.path i : G.Walk (P.start i.1) (P.finish i.1)).support.toFinset)) := by
      intro v hv
      have hocc := hoccup (Finset.mem_inter.mp hv).2
      rw [Finset.mem_union]
      rcases Finset.mem_union.mp hocc with hU | hpaths
      · exact Or.inl (Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hv).1, hU⟩)
      · right
        obtain ⟨i, hi, hip⟩ := Finset.mem_biUnion.mp hpaths
        exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hv).1, hip⟩⟩
    have hle := Finset.card_le_card hsub
    have hcardunion := Finset.card_union_le
      (G.neighborFinset x ∩ U)
      ((Finset.univ : Finset C.used).biUnion (fun i =>
        G.neighborFinset x ∩
          (C.path i : G.Walk (P.start i.1) (P.finish i.1)).support.toFinset))
    have hbi := Finset.card_biUnion_le (s := (Finset.univ : Finset C.used))
      (t := fun i => G.neighborFinset x ∩
        (C.path i : G.Walk (P.start i.1) (P.finish i.1)).support.toFinset)
    have hUle : (G.neighborFinset x ∩ U).card ≤ U.card :=
      Finset.card_le_card Finset.inter_subset_right
    omega
  have hpaths : (∑ i : C.used,
      (G.neighborFinset x ∩
        (C.path i : G.Walk (P.start i.1) (P.finish i.1)).support.toFinset).card)
      ≤ 3 * C.used.card := by
    calc
      _ ≤ ∑ _i : C.used, 3 := by
        apply Finset.sum_le_sum
        intro i _
        exact C.outside_path_neighbor_card_le_three hminimal i x hx
      _ = 3 * C.used.card := by simp [mul_comm]
  omega

end ShortPartial
end Linkedness
end HadwigerLean
