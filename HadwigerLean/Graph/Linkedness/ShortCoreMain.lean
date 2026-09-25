import HadwigerLean.Graph.Linkedness.ShortCore
import HadwigerLean.Graph.Linkedness.PathShortcut
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Tactic

/-!
# The linked small core: dense anticomplete sides

Appendix D ends by splitting the residual graph into two nonempty
anticomplete parts. The smaller induced side has at most seven times k
vertices and inherits minimum degree five times k.
-/

namespace HadwigerLean
namespace Linkedness
set_option maxHeartbeats 1000000

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A side of an anticomplete partition retains every degree. -/
theorem degree_induce_of_anticomplete_partition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [Fintype S]
    (hcover : S ∪ T = Set.univ)
    (hnoedge : ∀ x ∈ S, ∀ y ∈ T, ¬ G.Adj x y)
    (v : S) :
    (G.induce S).degree v = G.degree v.1 := by
  have hneighbors : G.neighborSet v.1 ⊆ S := by
    intro w hw
    by_contra hwS
    have hwV : w ∈ S ∪ T := by rw [hcover]; trivial
    have hwT : w ∈ T := by
      rcases hwV with hwS' | hwT
      · exact False.elim (hwS hwS')
      · exact hwT
    exact hnoedge v.1 v.property w hwT hw
  let e : S ↪ V := Function.Embedding.subtype (· ∈ S)
  have hmap : ((G.induce S).neighborFinset v).map e =
      G.neighborFinset v.1 := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
      have hadj : G.Adj v.1 u.1 :=
        ((G.induce S).mem_neighborFinset v u).mp hu
      exact (G.mem_neighborFinset v.1 u.1).mpr hadj
    · intro hx
      have hadj : G.Adj v.1 x :=
        (G.mem_neighborFinset v.1 x).mp hx
      let u : S := ⟨x, hneighbors hadj⟩
      have hu : u ∈ (G.induce S).neighborFinset v :=
        ((G.induce S).mem_neighborFinset v u).mpr hadj
      exact Finset.mem_map.mpr ⟨u, hu, rfl⟩
  calc
    (G.induce S).degree v = ((G.induce S).neighborFinset v).card :=
      ((G.induce S).card_neighborFinset_eq_degree v).symm
    _ = (((G.induce S).neighborFinset v).map e).card := by
      rw [Finset.card_map]
    _ = (G.neighborFinset v.1).card := congrArg Finset.card hmap
    _ = G.degree v.1 := G.card_neighborFinset_eq_degree v.1


/-- An anticomplete partition of a graph of order at most 14k and
minimum degree at least 5k has a k-linked induced side. -/
theorem linked_side_of_dense_anticomplete_partition
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
  · refine ⟨A, hA, hA_small, ?_⟩
    let S : Set V := A
    change KLinked (G.induce S) k
    apply kLinked_of_five_k_degree_seven_k_order
      (G.induce S) k
    · intro v
      rw [degree_induce_of_anticomplete_partition G S (B : Set V)
        hcoverSet hnoedge v]
      exact hdegree v.1
    · simpa [S] using hA_small
  · refine ⟨B, hB, hB_small, ?_⟩
    have hnoedge' : ∀ x ∈ B, ∀ y ∈ A, ¬ G.Adj x y := by
      intro x hx y hy hxy
      exact hnoedge y hy x hx hxy.symm
    have hcover' : (B : Set V) ∪ (A : Set V) = Set.univ := by
      simpa only [Set.union_comm] using hcoverSet
    let S : Set V := B
    change KLinked (G.induce S) k
    apply kLinked_of_five_k_degree_seven_k_order
      (G.induce S) k
    · intro v
      rw [degree_induce_of_anticomplete_partition G S (A : Set V)
        hcover' hnoedge' v]
      exact hdegree v.1
    · simpa [S] using hB_small


/-- A choice of paths for a subset of the prescribed pair indices. -/
abbrev ShortPartialData {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (P : IndexedPairs (Fin k) V) :=
  Σ U : Finset (Fin k),
    ∀ i : U, G.Path (P.start i.1) (P.finish i.1)

/-- Short, disjoint partial linkages whose interiors avoid all terminals. -/
def ShortPartialGood {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (P : IndexedPairs (Fin k) V) (X : Finset V)
    (D : ShortPartialData G P) : Prop :=
  (∀ i : D.1, (D.2 i : G.Walk (P.start i.1) (P.finish i.1)).length ≤ 7) ∧
  (∀ i : D.1, ∀ x ∈ pathVertexSet (D.2 i),
    x ∈ X → x ∈ P.terminals i.1) ∧
  (∀ i j : D.1, i.1 ≠ j.1 →
    Disjoint (pathVertexSet (D.2 i)) (pathVertexSet (D.2 j)))

/-- A partial linkage with the shortness, terminal, and disjointness
conditions bundled. -/
abbrev ShortPartial {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (P : IndexedPairs (Fin k) V) (X : Finset V) :=
  {D : ShortPartialData G P // ShortPartialGood G P X D}

namespace ShortPartial

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}
  {P : IndexedPairs (Fin k) V} {X : Finset V}

def used (C : ShortPartial G P X) : Finset (Fin k) := C.1.1

def path (C : ShortPartial G P X) (i : C.used) :
    G.Path (P.start i.1) (P.finish i.1) := C.1.2 i

def totalLength (C : ShortPartial G P X) : ℕ :=
  ∑ i : C.used, (C.path i : G.Walk (P.start i.1) (P.finish i.1)).length

theorem short (C : ShortPartial G P X) (i : C.used) :
    (C.path i : G.Walk (P.start i.1) (P.finish i.1)).length ≤ 7 :=
  C.2.1 i

theorem avoids (C : ShortPartial G P X) (i : C.used) (x : V)
    (hx : x ∈ pathVertexSet (C.path i)) (hxX : x ∈ X) :
    x ∈ P.terminals i.1 :=
  C.2.2.1 i x hx hxX

theorem disjoint (C : ShortPartial G P X) (i j : C.used)
    (hij : i.1 ≠ j.1) :
    Disjoint (pathVertexSet (C.path i)) (pathVertexSet (C.path j)) :=
  C.2.2.2 i j hij

/-- The empty partial linkage is always admissible. -/
def empty : ShortPartial G P X :=
  ⟨⟨∅, fun i => by cases i with | mk i hi => simp at hi⟩,
    ⟨fun i => by cases i with | mk i hi => simp at hi,
     fun i => by cases i with | mk i hi => simp at hi,
     fun i => by cases i with | mk i hi => simp at hi⟩⟩

end ShortPartial

/-- Among all admissible partial short linkages, choose first the
maximum number of completed pairs and then minimum total length. -/
theorem exists_optimal_short_partial
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (P : IndexedPairs (Fin k) V) (X : Finset V) :
    ∃ C : ShortPartial G P X,
      (∀ D : ShortPartial G P X, D.used.card ≤ C.used.card) ∧
      (∀ D : ShortPartial G P X,
        D.used.card = C.used.card →
          C.totalLength ≤ D.totalLength) := by
  classical
  letI : Fintype (ShortPartialData G P) := inferInstance
  letI : Fintype (ShortPartial G P X) := inferInstance
  let all : Finset (ShortPartial G P X) := Finset.univ
  have hnonempty : all.Nonempty := ⟨ShortPartial.empty, Finset.mem_univ _⟩
  obtain ⟨C, hC, hmax⟩ :=
    all.exists_max_image (fun D : ShortPartial G P X => D.used.card) hnonempty
  let best : Finset (ShortPartial G P X) :=
    all.filter (fun D => D.used.card = C.used.card)
  have hbest : best.Nonempty := by
    refine ⟨C, ?_⟩
    exact Finset.mem_filter.mpr ⟨hC, rfl⟩
  obtain ⟨E, hE, hmin⟩ :=
    best.exists_min_image (fun D : ShortPartial G P X => D.totalLength) hbest
  have hEcard : E.used.card = C.used.card :=
    (Finset.mem_filter.mp hE).2
  refine ⟨E, ?_, ?_⟩
  · intro D
    rw [hEcard]
    exact hmax D (Finset.mem_univ _)
  · intro D hD
    exact hmin D (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hD.trans hEcard⟩)


namespace ShortPartial

/-- If every pair index is used, the partial family is a full
linkage for the prescribed pairs. -/
def toLinkageOfFull
    {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {P : IndexedPairs (Fin k) V} {X : Finset V}
    (C : ShortPartial G P X)
    (hfull : C.used.card = k) :
    IndexedLinkage G P := by
  classical
  have hused : C.used = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa only [Finset.card_univ, Fintype.card_fin] using hfull.ge
  let f (i : Fin k) : C.used :=
    ⟨i, by rw [hused]; simp⟩
  refine {
    path := fun i => C.path (f i)
    disjoint := ?_
  }
  intro i j hij
  exact C.disjoint (f i) (f j) hij

/-- If the prescribed pairing has no full linkage, a partial family
leaves at least one pair unused. -/
theorem card_used_le_sub_one
    {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {P : IndexedPairs (Fin k) V} {X : Finset V}
    (C : ShortPartial G P X)
    (hnot : ¬ Nonempty (IndexedLinkage G P)) :
    C.used.card ≤ k - 1 := by
  have hle : C.used.card ≤ k := by
    simpa using Finset.card_le_card (Finset.subset_univ C.used)
  have hnecard : C.used.card ≠ k := by
    intro hcard
    exact hnot ⟨C.toLinkageOfFull hcard⟩
  omega

end ShortPartial


namespace ShortPartial

/-- All prescribed terminals plus the nonterminal vertices of the
completed short paths. -/
noncomputable def occupied
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {k : ℕ}
    {P : IndexedPairs (Fin k) V} {X : Finset V}
    (C : ShortPartial G P X) : Finset V := by
  classical
  exact X ∪ (Finset.univ : Finset C.used).biUnion (fun i =>
    ((C.path i : G.Walk (P.start i.1) (P.finish i.1)).support.toFinset) \ X)

theorem terminal_subset_occupied
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {k : ℕ}
    {P : IndexedPairs (Fin k) V} {X : Finset V}
    (C : ShortPartial G P X) :
    X ⊆ C.occupied := by
  classical
  intro x hx
  exact Finset.mem_union.mpr (Or.inl hx)

theorem path_subset_occupied
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {k : ℕ}
    {P : IndexedPairs (Fin k) V} {X : Finset V}
    (C : ShortPartial G P X) (i : C.used) :
    pathVertexSet (C.path i) ⊆ (C.occupied : Set V) := by
  classical
  intro x hx
  by_cases hxX : x ∈ X
  · exact C.terminal_subset_occupied hxX
  · apply Finset.mem_union.mpr
    right
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    exact Finset.mem_sdiff.mpr
      ⟨List.mem_toFinset.mpr hx, hxX⟩

/-- Each completed path contributes at most six vertices beyond the
terminal set. -/
theorem occupied_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {k : ℕ}
    {P : IndexedPairs (Fin k) V} {X : Finset V}
    (C : ShortPartial G P X)
    (hX : X.card = 2 * k)
    (hterm : ∀ i, P.terminals i ⊆ (X : Set V))
    (hne : ∀ i, P.start i ≠ P.finish i) :
    C.occupied.card ≤ 2 * k + 6 * C.used.card := by
  classical
  let rest : C.used → Finset V := fun i =>
    ((C.path i : G.Walk (P.start i.1) (P.finish i.1)).support.toFinset) \ X
  have hrest (i : C.used) : (rest i).card ≤ 6 := by
    apply short_path_nonterminal_card_le_six X (C.path i)
    · exact hterm i.1 (by simp [IndexedPairs.terminals])
    · exact hterm i.1 (by simp [IndexedPairs.terminals])
    · exact hne i.1
    · exact C.short i
  have hunion :
      ((Finset.univ : Finset C.used).biUnion rest).card ≤
        ∑ i : C.used, (rest i).card :=
    Finset.card_biUnion_le
  have hsum :
      (∑ i : C.used, (rest i).card) ≤ 6 * C.used.card := by
    calc
      (∑ i : C.used, (rest i).card) ≤
          ∑ _i : C.used, 6 := Finset.sum_le_sum (by
            intro i _
            exact hrest i)
      _ = 6 * C.used.card := by simp [mul_comm]
  calc
    C.occupied.card =
        (X ∪ (Finset.univ : Finset C.used).biUnion rest).card := rfl
    _ ≤ X.card + ((Finset.univ : Finset C.used).biUnion rest).card :=
      Finset.card_union_le _ _
    _ ≤ 2 * k + 6 * C.used.card := by omega

end ShortPartial


namespace ShortPartial

/-- Replacing one completed path by a shorter path that uses only its
old vertices and one entirely new vertex preserves admissibility and
strictly decreases the total path length. -/
theorem replace_shorter_path
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {k : ℕ} {P : IndexedPairs (Fin k) V} {X : Finset V}
    (C : ShortPartial G P X) (i : C.used) (x : V)
    (hx : x ∉ C.occupied)
    (q : G.Path (P.start i.1) (P.finish i.1))
    (hqsubset : pathVertexSet q ⊆
      pathVertexSet (C.path i) ∪ {x})
    (hqlt : (q : G.Walk (P.start i.1) (P.finish i.1)).length <
      (C.path i : G.Walk (P.start i.1) (P.finish i.1)).length) :
    ∃ D : ShortPartial G P X,
      D.used = C.used ∧ D.totalLength < C.totalLength := by
  classical
  let p (j : C.used) : G.Path (P.start j.1) (P.finish j.1) :=
    if h : j = i then by subst j; exact q else C.path j
  have hpeq : p i = q := by simp [p]
  have hpne (j : C.used) (hji : j ≠ i) : p j = C.path j := by
    simp [p, hji]
  have hxX : x ∉ X := by
    intro hmem
    exact hx (C.terminal_subset_occupied hmem)
  have hqshort : (q : G.Walk (P.start i.1) (P.finish i.1)).length ≤ 7 :=
    hqlt.le.trans (C.short i)
  have hqavoid (v : V) (hv : v ∈ pathVertexSet q) (hvX : v ∈ X) :
      v ∈ P.terminals i.1 := by
    rcases hqsubset hv with hvi | hvx
    · exact C.avoids i v hvi hvX
    · have hvx : v = x := by simpa using hvx
      exact False.elim (hxX (hvx ▸ hvX))
  have hqdis (j : C.used) (hji : j ≠ i) :
      Disjoint (pathVertexSet q) (pathVertexSet (C.path j)) := by
    apply Set.disjoint_left.mpr
    intro v hvq hvj
    rcases hqsubset hvq with hvi | hvx
    · have hij : i.1 ≠ j.1 := by
        intro h
        exact hji (Subtype.ext h.symm)
      exact (Set.disjoint_left.mp (C.disjoint i j hij)) hvi hvj
    · have hvx : v = x := by simpa using hvx
      exact hx (hvx ▸ C.path_subset_occupied j hvj)
  have hgood : ShortPartialGood G P X ⟨C.used, p⟩ := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      by_cases hji : j = i
      · subst j
        simpa [p] using hqshort
      · simpa [hpne j hji] using C.short j
    · intro j v hv hvX
      by_cases hji : j = i
      · subst j
        have hvq : v ∈ pathVertexSet q := by simpa [p] using hv
        exact hqavoid v hvq hvX
      · exact C.avoids j v (by simpa [hpne j hji] using hv) hvX
    · intro j l hjl
      by_cases hji : j = i
      · subst j
        have hli : l ≠ i := by
          intro h
          exact hjl (congrArg Subtype.val h).symm
        simpa [hpeq, hpne l hli] using hqdis l hli
      · by_cases hli : l = i
        · subst l
          have hdis := (hqdis j hji).symm
          simpa [hpeq, hpne j hji] using hdis
        · simpa [hpne j hji, hpne l hli] using
            C.disjoint j l hjl
  let D : ShortPartial G P X := ⟨⟨C.used, p⟩, hgood⟩
  refine ⟨D, rfl, ?_⟩
  change (∑ j : C.used,
      (p j : G.Walk (P.start j.1) (P.finish j.1)).length) <
    ∑ j : C.used,
      (C.path j : G.Walk (P.start j.1) (P.finish j.1)).length
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hji : j = i
    · subst j
      simpa [hpeq] using hqlt.le
    · simp [hpne j hji]
  · exact ⟨i, Finset.mem_univ _, by simpa [hpeq] using hqlt⟩


/-- In a length-minimal maximal partial linkage, an unused vertex
has at most three neighbors on each completed short path. -/
theorem outside_path_neighbor_card_le_three
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} {P : IndexedPairs (Fin k) V} {X : Finset V}
    (C : ShortPartial G P X)
    (hminimal : ∀ D : ShortPartial G P X,
      D.used.card = C.used.card →
      C.totalLength ≤ D.totalLength)
    (i : C.used) (x : V) (hx : x ∉ C.occupied) :
    (G.neighborFinset x ∩
      (C.path i : G.Walk (P.start i.1) (P.finish i.1)).support.toFinset).card ≤ 3 := by
  by_contra hle
  have hfour : 4 ≤
      (G.neighborFinset x ∩
        (C.path i : G.Walk (P.start i.1) (P.finish i.1)).support.toFinset).card := by
    omega
  obtain ⟨q, hqsubset, hqlt⟩ :=
    path_shortcut_of_four_neighbors (C.path i) hfour
  obtain ⟨D, hused, hlength⟩ :=
    C.replace_shorter_path i x hx q hqsubset hqlt
  have hmin := hminimal D (by rw [hused])
  omega
end ShortPartial
end Linkedness
end HadwigerLean
