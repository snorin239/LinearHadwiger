import HadwigerLean.Graph.RootedCliqueMinor

/-!
# Pulling separations through an edge contraction

The preimages of the two shores under a connected partition form a
separation in the original graph. For a single edge contraction its
boundary is at most one vertex larger than the quotient boundary.
-/

namespace HadwigerLean

universe u v

namespace VertexSeparation

/-- Preimages of a quotient separation form a separation. -/
noncomputable def pullbackPartition {V : Type u} {I : Type v}
    {G : SimpleGraph V} (P : ConnectedPartition G I)
    (S : VertexSeparation P.touchingQuotient) : VertexSeparation G where
  left := {x | P.index x ∈ S.left}
  right := {x | P.index x ∈ S.right}
  cover := by
    ext x
    change P.index x ∈ S.left ∪ S.right ↔ x ∈ Set.univ
    rw [S.cover]
    simp
  no_cross := by
    intro x y hxL hxNR hyR hyNL hxy
    change P.index x ∈ S.left at hxL
    change P.index x ∉ S.right at hxNR
    change P.index y ∈ S.right at hyR
    change P.index y ∉ S.left at hyNL
    have hne : P.index x ≠ P.index y := by
      intro heq
      exact hxNR (by simpa [heq] using hyR)
    have hq : P.touchingQuotient.Adj (P.index x) (P.index y) :=
      ⟨hne, x, P.index_mem x, y, P.index_mem y, hxy⟩
    exact S.no_cross hxL hxNR hyR hyNL hq

/-- A branch whose quotient image is strictly far remains strictly far
when the separation is pulled back. -/
theorem branch_subset_strictRight_pullback
    {V : Type u} {I : Type v} {G : SimpleGraph V}
    (P : ConnectedPartition G I)
    (S : VertexSeparation P.touchingQuotient)
    (B : Set V)
    (hB : P.index '' B ⊆ S.strictRight) :
    B ⊆ (S.pullbackPartition P).strictRight := by
  intro x hx
  exact hB ⟨x, hx, rfl⟩

end VertexSeparation

/-- The index map of an edge contraction is injective after deleting one
endpoint of the contracted edge. -/
theorem edgeContractionIndex_injOn_away
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) :
    Set.InjOn (edgeContractionPartition G hab).index {x : V | x ≠ a} := by
  let P := edgeContractionPartition G hab
  intro x hx y hy hxy
  have hxm : x ∈ P.block (P.index x) := P.index_mem x
  have hym : y ∈ P.block (P.index x) := by
    rw [hxy]
    exact P.index_mem y
  change x ∈ edgeContractionBlock (a := a) (b := b) (P.index x) at hxm
  change y ∈ edgeContractionBlock (a := a) (b := b) (P.index x) at hym
  cases hq : P.index x with
  | none =>
    rw [hq] at hxm hym
    have hxab : x = a ∨ x = b := by
      simpa only [edgeContractionBlock, Set.mem_insert_iff, Set.mem_singleton_iff] using hxm
    have hyab : y = a ∨ y = b := by
      simpa only [edgeContractionBlock, Set.mem_insert_iff, Set.mem_singleton_iff] using hym
    rcases hxab with hxa | hxb
    · exact (hx hxa).elim
    rcases hyab with hya | hyb
    · exact (hy hya).elim
    exact hxb.trans hyb.symm
  | some z =>
    rw [hq] at hxm hym
    have hxz : x = z.1 := by
      simpa only [edgeContractionBlock, Set.mem_insert_iff, Set.mem_singleton_iff] using hxm
    have hyz : y = z.1 := by
      simpa only [edgeContractionBlock, Set.mem_insert_iff, Set.mem_singleton_iff] using hym
    exact hxz.trans hyz.symm
/-- Pulling a separation back through one edge contraction increases its
boundary order by at most one. -/
theorem edgeContraction_pullback_order_le
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a b : V} (hab : G.Adj a b)
    [Fintype (EdgeContractionVertex a b)]
    [DecidableEq (EdgeContractionVertex a b)]
    (S : VertexSeparation (edgeContraction G hab)) :
    ((S.pullbackPartition (edgeContractionPartition G hab)).separatorFinset).card ≤
      S.separatorFinset.card + 1 := by
  let P := edgeContractionPartition G hab
  let T := S.pullbackPartition P
  let X := T.separatorFinset
  let Y := S.separatorFinset
  have hinj : Set.InjOn P.index (X.erase a : Set V) := by
    intro x hx y hy hxy
    apply edgeContractionIndex_injOn_away hab
    · exact (Finset.mem_erase.mp hx).1
    · exact (Finset.mem_erase.mp hy).1
    · exact hxy
  have hsubset : (X.erase a).image P.index ⊆ Y := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    have hxT : x ∈ T.separatorFinset := (Finset.mem_erase.mp hx).2
    have hxsep := (T.mem_separatorFinset x).mp hxT
    change P.index x ∈ S.left ∧ P.index x ∈ S.right at hxsep
    exact (S.mem_separatorFinset (P.index x)).mpr hxsep
  have himage : (X.erase a).card ≤ Y.card := by
    calc
      (X.erase a).card = ((X.erase a).image P.index).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ Y.card := Finset.card_le_card hsubset
  have herase : X.card ≤ (X.erase a).card + 1 := by
    by_cases ha : a ∈ X
    · have hcard := Finset.card_erase_add_one ha
      omega
    · have heq : X.erase a = X := Finset.erase_eq_of_notMem ha
      rw [heq]
      omega
  change X.card ≤ Y.card + 1
  omega
/-- If the deleted contraction endpoint is not on the pulled-back boundary,
no extra separator vertex is introduced. -/
theorem edgeContraction_pullback_order_le_of_a_not_mem
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a b : V} (hab : G.Adj a b)
    [Fintype (EdgeContractionVertex a b)]
    [DecidableEq (EdgeContractionVertex a b)]
    (S : VertexSeparation (edgeContraction G hab))
    (ha : a ∉
      (S.pullbackPartition (edgeContractionPartition G hab)).separatorFinset) :
    ((S.pullbackPartition (edgeContractionPartition G hab)).separatorFinset).card ≤
      S.separatorFinset.card := by
  let P := edgeContractionPartition G hab
  let T := S.pullbackPartition P
  let X := T.separatorFinset
  let Y := S.separatorFinset
  change a ∉ X at ha
  have hinj : Set.InjOn P.index (X : Set V) := by
    intro x hx y hy hxy
    apply edgeContractionIndex_injOn_away hab
    · intro hxa
      exact ha (hxa ▸ hx)
    · intro hya
      exact ha (hya ▸ hy)
    · exact hxy
  have hsubset : X.image P.index ⊆ Y := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    have hxsep := (T.mem_separatorFinset x).mp hx
    change P.index x ∈ S.left ∧ P.index x ∈ S.right at hxsep
    exact (S.mem_separatorFinset (P.index x)).mpr hxsep
  change X.card ≤ Y.card
  calc
    X.card = (X.image P.index).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ Y.card := Finset.card_le_card hsubset
/-- Pull back a quotient separator together with all prescribed roots and
an original branch known to map into the far strict shore. -/
theorem edgeContraction_pullback_roots_and_branch
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a b : V} (hab : G.Adj a b)
    [Fintype (EdgeContractionVertex a b)]
    [DecidableEq (EdgeContractionVertex a b)]
    {r : ℕ} (root : Fin r → V)
    (B : Set V)
    (S : VertexSeparation (edgeContraction G hab))
    (hroots : ∀ i, edgeContractionRoot hab root i ∈ S.left)
    (hfar : (edgeContractionPartition G hab).index '' B ⊆ S.strictRight) :
    ∃ T : VertexSeparation G,
      T.separatorFinset.card ≤ S.separatorFinset.card + 1 ∧
      (∀ i, root i ∈ T.left) ∧ B ⊆ T.strictRight := by
  let P := edgeContractionPartition G hab
  let T := S.pullbackPartition P
  refine ⟨T, edgeContraction_pullback_order_le hab S, ?_, ?_⟩
  · intro i
    exact hroots i
  · exact S.branch_subset_strictRight_pullback P B hfar
end HadwigerLean
