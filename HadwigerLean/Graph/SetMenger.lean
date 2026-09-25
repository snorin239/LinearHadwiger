import HadwigerLean.Graph.IndexedLinkage
import Mathlib.Data.Finset.Card
import HadwigerLean.Graph.FiniteFlow

/-!
# Finite set separators and indexed linkages

A vertex separator may contain either endpoint of a path. This file proves
the weak Menger inequality and the saturation consequence, and relates
small cuts of the vertex-split network to separators in the graph. The final
min-max theorem is in `SetMengerTheorem`.
-/

namespace HadwigerLean
namespace SetMenger

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]

/-- Every path from A to B meets Q, including paths of length zero and
paths whose endpoints lie in Q. -/
def IsABSeparator (G : SimpleGraph V) (A B Q : Finset V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ p : G.Path a b,
    ∃ q ∈ Q, q ∈ pathVertexSet p

/-- Every indexed path starts in A and ends in B. -/
def IsABLinkage {G : SimpleGraph V} {P : IndexedPairs ι V}
    (L : IndexedLinkage G P) (A B : Finset V) : Prop :=
  (∀ i, P.start i ∈ A) ∧ (∀ i, P.finish i ∈ B)

/-- The vertices at which the paths of an indexed linkage meet a separator
are all distinct. Hence every separator has order at least the linkage size. -/
theorem card_le_separator {G : SimpleGraph V} {P : IndexedPairs ι V}
    (L : IndexedLinkage G P) (A B Q : Finset V)
    (hAB : IsABLinkage L A B) (hQ : IsABSeparator G A B Q) :
    Fintype.card ι ≤ Q.card := by
  classical
  let hit : ι → V := fun i =>
    Classical.choose (hQ (P.start i) (hAB.1 i)
      (P.finish i) (hAB.2 i) (L.path i))
  have hit_spec (i : ι) :
      hit i ∈ Q ∧ hit i ∈ pathVertexSet (L.path i) :=
    Classical.choose_spec (hQ (P.start i) (hAB.1 i)
      (P.finish i) (hAB.2 i) (L.path i))
  have hinj : Function.Injective hit := by
    intro i j heq
    by_contra hne
    exact (Set.disjoint_left.mp (L.disjoint hne))
      (hit_spec i).2 (heq.symm ▸ (hit_spec j).2)
  have hsubset : (Finset.univ.image hit) ⊆ Q := by
    intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
    exact (hit_spec i).1
  calc
    Fintype.card ι = (Finset.univ.image hit).card := by
      simp [Finset.card_image_of_injective _ hinj]
    _ ≤ Q.card := Finset.card_le_card hsubset

/-- If the separator and linkage have the same order, every separator
vertex is occupied by exactly one of the disjoint paths. -/
theorem separator_saturated {G : SimpleGraph V} {P : IndexedPairs ι V}
    (L : IndexedLinkage G P) (A B Q : Finset V)
    (hAB : IsABLinkage L A B) (hQ : IsABSeparator G A B Q)
    (hcard : Q.card = Fintype.card ι) :
    ∀ q ∈ Q, ∃ i : ι, q ∈ pathVertexSet (L.path i) := by
  classical
  let hit : ι → V := fun i =>
    Classical.choose (hQ (P.start i) (hAB.1 i)
      (P.finish i) (hAB.2 i) (L.path i))
  have hit_spec (i : ι) :
      hit i ∈ Q ∧ hit i ∈ pathVertexSet (L.path i) :=
    Classical.choose_spec (hQ (P.start i) (hAB.1 i)
      (P.finish i) (hAB.2 i) (L.path i))
  have hinj : Function.Injective hit := by
    intro i j heq
    by_contra hne
    exact (Set.disjoint_left.mp (L.disjoint hne))
      (hit_spec i).2 (heq.symm ▸ (hit_spec j).2)
  have hsubset : (Finset.univ.image hit) ⊆ Q := by
    intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
    exact (hit_spec i).1
  have himage_card : (Finset.univ.image hit).card = Fintype.card ι := by
    simp [Finset.card_image_of_injective _ hinj]
  have heq : Finset.univ.image hit = Q :=
    Finset.eq_of_subset_of_card_le hsubset (by rw [hcard, ← himage_card])
  intro q hq
  have hq' : q ∈ Finset.univ.image hit := heq.symm ▸ hq
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hq'
  exact ⟨i, hi ▸ (hit_spec i).2⟩

/-! ## Vertex-split network -/

/-- Two copies of every graph vertex, together with source and sink. -/
abbrev SplitVertex (V : Type*) := Option V ⊕ Option V

def splitSource : SplitVertex V := .inl none
def splitSink : SplitVertex V := .inr none
def splitIn (v : V) : SplitVertex V := .inl (some v)
def splitOut (v : V) : SplitVertex V := .inr (some v)

/-- The capacity of an arc in the standard vertex-split network. The
capacity `|V|+1` makes original-edge and terminal arcs unavailable to a
minimum cut of size at most `|V|`. -/
noncomputable def splitCapacity (G : SimpleGraph V) (A B : Finset V) :
    SplitVertex V → SplitVertex V → ℕ := by
  classical
  let M := Fintype.card V + 1
  exact fun x y =>
    match x, y with
    | .inl none, .inl (some a) => if a ∈ A then M else 0
    | .inl (some v), .inr (some w) => if v = w then 1 else 0
    | .inr (some u), .inl (some v) => if G.Adj u v then M else 0
    | .inr (some b), .inr none => if b ∈ B then M else 0
    | _, _ => 0

/-- The network whose unit arcs represent vertex use. -/
noncomputable def splitNetwork (G : SimpleGraph V) (A B : Finset V) :
    FiniteFlow.Network (SplitVertex V) where
  source := splitSource
  sink := splitSink
  capacity := splitCapacity G A B
  source_ne_sink := by simp [splitSource, splitSink]
  no_into_source := by
    intro z
    cases z with
    | inl o => cases o <;> simp [splitSource, splitCapacity]
    | inr o => cases o <;> simp [splitSource, splitCapacity]
  no_out_of_sink := by
    intro z
    cases z with
    | inl o => cases o <;> simp [splitSink, splitCapacity]
    | inr o => cases o <;> simp [splitSink, splitCapacity]
/-- The cut through every unit vertex arc. -/
noncomputable def allInCut : Finset (SplitVertex V) := by
  classical
  exact Finset.univ.image (fun o : Option V => (Sum.inl o : SplitVertex V))

@[simp] theorem splitSource_mem_allInCut : splitSource ∈ (allInCut (V := V)) := by
  classical
  simp [allInCut, splitSource]

@[simp] theorem splitIn_mem_allInCut (v : V) :
    splitIn v ∈ (allInCut (V := V)) := by
  classical
  simp [allInCut, splitIn]

@[simp] theorem splitSink_not_mem_allInCut :
    splitSink ∉ (allInCut (V := V)) := by
  classical
  simp [allInCut, splitSink]

@[simp] theorem splitOut_not_mem_allInCut (v : V) :
    splitOut v ∉ (allInCut (V := V)) := by
  classical
  simp [allInCut, splitOut]
/-- The two copies partition the vertex-split network. -/
noncomputable def allOutCut : Finset (SplitVertex V) := by
  classical
  exact Finset.univ.image (fun o : Option V => (Sum.inr o : SplitVertex V))

theorem allInCut_compl :
    Finset.univ \ (allInCut (V := V)) = allOutCut (V := V) := by
  classical
  ext x
  cases x with
  | inl o => simp [allInCut, allOutCut]
  | inr o => simp [allInCut, allOutCut]
theorem allInCut_capacity (G : SimpleGraph V) (A B : Finset V) :
    (splitNetwork G A B).cutCapacity (allInCut (V := V)) =
      Fintype.card V := by
  classical
  unfold FiniteFlow.Network.cutCapacity
  rw [allInCut_compl]
  have hinl : Set.InjOn
      (fun o : Option V => (Sum.inl o : SplitVertex V))
      (Finset.univ : Finset (Option V)) := by
    intro a ha b hb hab
    exact Sum.inl_injective hab
  have hinr : Set.InjOn
      (fun o : Option V => (Sum.inr o : SplitVertex V))
      (Finset.univ : Finset (Option V)) := by
    intro a ha b hb hab
    exact Sum.inr_injective hab
  simp only [allInCut, allOutCut]
  rw [Finset.sum_image hinl]
  simp_rw [Finset.sum_image hinr]
  simp [splitNetwork, splitCapacity, Fintype.sum_option]
/-- No arc of capacity `|V|+1` crosses a cut of capacity at most `|V|`. -/
theorem no_large_arc_crosses (G : SimpleGraph V) (A B : Finset V)
    (S : Finset (SplitVertex V))
    (hsmall : (splitNetwork G A B).cutCapacity S ≤ Fintype.card V)
    {x y : SplitVertex V}
    (hlarge : splitCapacity G A B x y = Fintype.card V + 1) :
    ¬ (x ∈ S ∧ y ∉ S) := by
  intro hcross
  have hle := (splitNetwork G A B).arcCapacity_le_cutCapacity
    S hcross.1 hcross.2
  change (splitCapacity G A B x y : ℤ) ≤
    (splitNetwork G A B).cutCapacity S at hle
  rw [hlarge] at hle
  omega

/-- Max-flow/min-cut yields a minimum split-network cut with capacity at
most the number of graph vertices. -/
theorem exists_small_split_cut (G : SimpleGraph V) (A B : Finset V) :
    ∃ (f : FiniteFlow.Flow (splitNetwork G A B))
      (S : Finset (SplitVertex V)),
      splitSource ∈ S ∧ splitSink ∉ S ∧
      f.value = (splitNetwork G A B).cutCapacity S ∧
      (splitNetwork G A B).cutCapacity S ≤ Fintype.card V ∧
      (∀ T : Finset (SplitVertex V),
        splitSource ∈ T → splitSink ∉ T →
        (splitNetwork G A B).cutCapacity S ≤
          (splitNetwork G A B).cutCapacity T) := by
  obtain ⟨f, S, hsource, hsink, hval, hmax, hmin⟩ :=
    (splitNetwork G A B).exists_max_flow_min_cut
  refine ⟨f, S, hsource, hsink, hval, ?_, hmin⟩
  calc
    (splitNetwork G A B).cutCapacity S ≤
      (splitNetwork G A B).cutCapacity (allInCut (V := V)) :=
        hmin _ splitSource_mem_allInCut splitSink_not_mem_allInCut
    _ = Fintype.card V := allInCut_capacity G A B
/-- Original vertices whose unit split arc crosses a network cut. -/
noncomputable def splitSeparator (S : Finset (SplitVertex V)) : Finset V := by
  classical
  exact Finset.univ.filter
    (fun v => splitIn v ∈ S ∧ splitOut v ∉ S)

@[simp] theorem mem_splitSeparator {S : Finset (SplitVertex V)} {v : V} :
    v ∈ splitSeparator S ↔ splitIn v ∈ S ∧ splitOut v ∉ S := by
  classical
  simp [splitSeparator]

theorem split_start_in_cut (G : SimpleGraph V) (A B : Finset V)
    (S : Finset (SplitVertex V))
    (hsource : splitSource ∈ S)
    (hsmall : (splitNetwork G A B).cutCapacity S ≤ Fintype.card V)
    {a : V} (ha : a ∈ A) : splitIn a ∈ S := by
  by_contra hnot
  have hlarge :
      splitCapacity G A B splitSource (splitIn a) =
        Fintype.card V + 1 := by
    simp [splitCapacity, splitSource, splitIn, ha]
  exact no_large_arc_crosses G A B S hsmall hlarge ⟨hsource, hnot⟩

theorem split_adj_closed (G : SimpleGraph V) (A B : Finset V)
    (S : Finset (SplitVertex V))
    (hsmall : (splitNetwork G A B).cutCapacity S ≤ Fintype.card V)
    {u v : V} (hu : splitOut u ∈ S) (huv : G.Adj u v) :
    splitIn v ∈ S := by
  by_contra hnot
  have hlarge :
      splitCapacity G A B (splitOut u) (splitIn v) =
        Fintype.card V + 1 := by
    simp [splitCapacity, splitOut, splitIn, huv]
  exact no_large_arc_crosses G A B S hsmall hlarge ⟨hu, hnot⟩

theorem split_finish_not_in_cut (G : SimpleGraph V) (A B : Finset V)
    (S : Finset (SplitVertex V))
    (hsink : splitSink ∉ S)
    (hsmall : (splitNetwork G A B).cutCapacity S ≤ Fintype.card V)
    {b : V} (hb : b ∈ B) : splitOut b ∉ S := by
  intro h
  have hlarge :
      splitCapacity G A B (splitOut b) splitSink =
        Fintype.card V + 1 := by
    simp [splitCapacity, splitOut, splitSink, hb]
  exact no_large_arc_crosses G A B S hsmall hlarge ⟨h, hsink⟩

theorem split_out_of_not_separator
    (S : Finset (SplitVertex V)) {v : V}
    (hin : splitIn v ∈ S) (hnot : v ∉ splitSeparator S) :
    splitOut v ∈ S := by
  by_contra hout
  exact hnot (mem_splitSeparator.mpr ⟨hin, hout⟩)
private theorem walk_through_small_cut (G : SimpleGraph V) (A B : Finset V)
    (S : Finset (SplitVertex V))
    (hsmall : (splitNetwork G A B).cutCapacity S ≤ Fintype.card V)
    {x y : V} (w : G.Walk x y)
    (havoid : ∀ v ∈ w.support, v ∉ splitSeparator S)
    (hstart : splitIn x ∈ S) : splitOut y ∈ S := by
  induction w with
  | @nil a =>
      exact split_out_of_not_separator S hstart
        (havoid a (by simp))
  | @cons a c d hadj rest ih =>
      have ha : a ∉ splitSeparator S :=
        havoid a (by simp)
      have hOut : splitOut a ∈ S :=
        split_out_of_not_separator S hstart ha
      have hIn : splitIn c ∈ S :=
        split_adj_closed G A B S hsmall hOut hadj
      have hrest : ∀ v ∈ rest.support, v ∉ splitSeparator S := by
        intro v hv
        exact havoid v (by simp [hv])
      exact ih hrest hIn

/-- Every small split-network source--sink cut defines a vertex separator in
the original graph, with terminals permitted in the separator. -/
theorem splitSeparator_isABSeparator (G : SimpleGraph V)
    (A B : Finset V) (S : Finset (SplitVertex V))
    (hsource : splitSource ∈ S) (hsink : splitSink ∉ S)
    (hsmall : (splitNetwork G A B).cutCapacity S ≤ Fintype.card V) :
    IsABSeparator G A B (splitSeparator S) := by
  classical
  intro a ha b hb p
  by_contra hn
  have havoid : ∀ v ∈ (p : G.Walk a b).support,
      v ∉ splitSeparator S := by
    intro v hv hmem
    exact hn ⟨v, hmem, hv⟩
  have hstart : splitIn a ∈ S :=
    split_start_in_cut G A B S hsource hsmall ha
  have hend : splitOut b ∈ S :=
    walk_through_small_cut G A B S hsmall
      (p : G.Walk a b) havoid hstart
  exact (split_finish_not_in_cut G A B S hsink hsmall hb) hend
/-- The unit-capacity part of the vertex-split network. -/
def splitUnitCapacity : SplitVertex V → SplitVertex V → ℕ
  | .inl (some v), .inr (some w) => if v = w then 1 else 0
  | _, _ => 0

private theorem splitUnitCutCapacity (S : Finset (SplitVertex V)) :
    (∑ x ∈ S, ∑ y ∈ Finset.univ \ S,
      (splitUnitCapacity x y : ℤ)) = (splitSeparator S).card := by
  classical
  have hterm (v : V) (y : SplitVertex V) :
      (splitUnitCapacity (splitIn v) y : ℤ) =
        if y = splitOut v then 1 else 0 := by
    cases y with
    | inl o => cases o <;> simp [splitUnitCapacity, splitIn, splitOut]
    | inr o =>
        cases o with
        | none => simp [splitUnitCapacity, splitIn, splitOut]
        | some w => simp [splitUnitCapacity, splitIn, splitOut, eq_comm]
  have hinner (x : SplitVertex V) :
      (∑ y ∈ Finset.univ \ S, (splitUnitCapacity x y : ℤ)) =
        match x with
        | .inl (some v) => if splitOut v ∉ S then 1 else 0
        | _ => 0 := by
    cases x with
    | inl o =>
        cases o with
        | none => simp [splitUnitCapacity]
        | some v =>
            change (∑ y ∈ Finset.univ \ S,
              (splitUnitCapacity (splitIn v) y : ℤ)) =
                if splitOut v ∉ S then 1 else 0
            simp_rw [hterm v]
            rw [Finset.sum_ite_eq']
            simp
    | inr o => cases o <;> simp [splitUnitCapacity]
  simp_rw [hinner]
  have hsum (f : SplitVertex V → ℤ) :
      (∑ x ∈ S, f x) =
        ∑ x : SplitVertex V, if x ∈ S then f x else 0 := by
    rw [← Finset.sum_filter]
    simp
  rw [hsum]
  simp only [Fintype.sum_sum_type, Fintype.sum_option]
  simp only [ite_self, Finset.sum_const_zero, zero_add, add_zero]
  have hite (v : V) :
      (if splitIn v ∈ S then (if splitOut v ∉ S then (1 : ℤ) else 0) else 0) =
        if splitIn v ∈ S ∧ splitOut v ∉ S then 1 else 0 := by
    by_cases hi : splitIn v ∈ S <;> by_cases ho : splitOut v ∈ S <;> simp [hi, ho]
  change (∑ v : V, if splitIn v ∈ S then (if splitOut v ∉ S then (1 : ℤ) else 0) else 0) = ↑(splitSeparator S).card
  simp_rw [hite]
  simpa [splitSeparator] using
    (Finset.sum_boole (fun v : V => splitIn v ∈ S ∧ splitOut v ∉ S) (Finset.univ : Finset V) :
      (∑ v : V, if splitIn v ∈ S ∧ splitOut v ∉ S then (1 : ℤ) else 0) =
        ↑(Finset.univ.filter (fun v : V => splitIn v ∈ S ∧ splitOut v ∉ S)).card)
private theorem splitCapacity_eq_unit_of_small (G : SimpleGraph V) (A B : Finset V)
    (S : Finset (SplitVertex V))
    (hsmall : (splitNetwork G A B).cutCapacity S ≤ Fintype.card V)
    (x y : SplitVertex V) (hx : x ∈ S) (hy : y ∉ S) :
    splitCapacity G A B x y = splitUnitCapacity x y := by
  have hne : splitCapacity G A B x y ≠ Fintype.card V + 1 :=
    fun h => no_large_arc_crosses G A B S hsmall h ⟨hx, hy⟩
  cases x <;> cases y <;> rename_i ox oy <;>
    cases ox <;> cases oy <;>
    simp [splitCapacity, splitUnitCapacity] at * <;> assumption

/-- A small network cut has precisely the number of its separated vertex arcs. -/
theorem small_cut_capacity_eq_separator_card (G : SimpleGraph V)
    (A B : Finset V) (S : Finset (SplitVertex V))
    (hsmall : (splitNetwork G A B).cutCapacity S ≤ Fintype.card V) :
    (splitNetwork G A B).cutCapacity S = (splitSeparator S).card := by
  classical
  calc
    (splitNetwork G A B).cutCapacity S =
        ∑ x ∈ S, ∑ y ∈ Finset.univ \ S,
          (splitUnitCapacity x y : ℤ) := by
            unfold FiniteFlow.Network.cutCapacity
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro y hy
            exact_mod_cast splitCapacity_eq_unit_of_small G A B S hsmall x y hx
              (Finset.mem_sdiff.mp hy).2
    _ = (splitSeparator S).card := splitUnitCutCapacity S
end SetMenger
end HadwigerLean
