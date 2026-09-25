import HadwigerLean.Bootstrap.Definitions
import HadwigerLean.Graph.TouchingQuotient

/-!
# Packing connected bipartite induced subgraphs

The first step of the exponent bootstrap selects a maximal family of disjoint
connected bipartite induced subgraphs of a prescribed order.
-/

namespace HadwigerLean.Bootstrap

universe u

private def GoodBlock {V : Type u} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (S : Finset V) : Prop :=
  S.card = k ∧ (G.induce (S : Set V)).Connected ∧
    (G.induce (S : Set V)).IsBipartite

private def GoodPacking {V : Type u} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (P : Finset (Finset V)) : Prop :=
  (∀ S ∈ P, GoodBlock G k S) ∧
    (∀ S ∈ P, ∀ T ∈ P, S ≠ T → Disjoint S T)


/-- Flatten the two subtype layers in a twice-induced graph. -/
private def induceInduceIso {V : Type u} (G : SimpleGraph V)
    (R : Set V) (s : Set R) :
    (G.induce R).induce s ≃g
      G.induce {v | ∃ h : v ∈ R, (⟨v, h⟩ : R) ∈ s} where
  toEquiv := Equiv.subtypeSubtypeEquivSubtypeExists (· ∈ R) (· ∈ s)
  map_rel_iff' := by
    intro x y
    rfl

/-- A good block in a remainder induced graph gives a good block in the
ambient graph, on the same vertices. -/
private theorem goodBlock_of_induce {V : Type u} [Fintype V]
    (G : SimpleGraph V) (R : Set V) (k : ℕ) (s : Finset R)
    (hcard : s.card = k)
    (hconn : ((G.induce R).induce (s : Set R)).Connected)
    (hbip : ((G.induce R).induce (s : Set R)).IsBipartite) :
    GoodBlock G k (s.map ⟨Subtype.val, Subtype.val_injective⟩) := by
  classical
  let S : Finset V := s.map ⟨Subtype.val, Subtype.val_injective⟩
  have hset : (S : Set V) =
      {v | ∃ h : v ∈ R, (⟨v, h⟩ : R) ∈ (s : Set R)} := by
    ext v
    constructor
    · intro hv
      obtain ⟨a, ha, hav⟩ := Finset.mem_map.mp hv
      subst v
      exact ⟨a.property, ha⟩
    · rintro ⟨h, hh⟩
      exact Finset.mem_map.mpr ⟨⟨v, h⟩, hh, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa only [S, Finset.card_map] using hcard
  · change (G.induce (S : Set V)).Connected
    rw [hset]
    exact (induceInduceIso G R (s : Set R)).connected_iff.mp hconn
  · change (G.induce (S : Set V)).IsBipartite
    rw [hset]
    exact SimpleGraph.Colorable.of_hom
      (induceInduceIso G R (s : Set R)).symm.toHom hbip


/-- The absence of connected bipartite induced (k)-sets is inherited by
induced subgraphs. -/
theorem noLargeConnectedBipartite_induce {V : Type u} [Fintype V]
    (G : SimpleGraph V) (R : Set V) (k : ℕ)
    (h : NoLargeConnectedBipartite G k) :
    NoLargeConnectedBipartite (G.induce R) k := by
  intro s hs hpair
  let S : Finset V := s.map ⟨Subtype.val, Subtype.val_injective⟩
  have hgood : GoodBlock G k S :=
    goodBlock_of_induce G R k s hs hpair.1 hpair.2
  exact h S hgood.1 ⟨hgood.2.1, hgood.2.2⟩
/-- The quotient has one vertex for each packed block and retains all
adjacencies between different blocks. -/
private def packingQuotient {V : Type u} (G : SimpleGraph V)
    (P : Finset (Finset V)) : SimpleGraph P where
  Adj i j := i ≠ j ∧
    ∃ x ∈ (i.val : Finset V), ∃ y ∈ (j.val : Finset V), G.Adj x y
  symm := ⟨by
    intro i j hij
    obtain ⟨hne, x, hx, y, hy, hxy⟩ := hij
    exact ⟨hne.symm, y, hy, x, hx, hxy.symm⟩⟩
  loopless := ⟨by
    intro i hii
    exact hii.1 rfl⟩

private theorem packingQuotient_isMinor {V : Type u} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (P : Finset (Finset V))
    (hP : GoodPacking G k P) :
    HadwigerLean.IsMinor (packingQuotient G P) G := by
  refine ⟨{
    branch := fun i => (i.val : Set V)
    connected := ?_
    disjoint := ?_
    adjacent := ?_
  }⟩
  · intro i
    exact (hP.1 i.val i.property).2.1
  · intro i j hij
    have hne : i.val ≠ j.val := fun heq => hij (Subtype.ext heq)
    simpa using hP.2 i.val i.property j.val j.property hne
  · intro i j hij
    exact hij.2

private theorem packingQuotient_card_le {V : Type u} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (P : Finset (Finset V))
    (hP : GoodPacking G k P) (hk : 0 < k) :
    Fintype.card P ≤ Fintype.card V / k := by
  classical
  have hdisj : (P : Set (Finset V)).PairwiseDisjoint id := by
    intro S hS T hT hne
    exact hP.2 S hS T hT hne
  have hcount : (P.biUnion id).card = P.card * k := by
    rw [Finset.card_biUnion hdisj]
    calc
      (∑ S ∈ P, S.card) = ∑ _S ∈ P, k := by
        apply Finset.sum_congr rfl
        intro S hS
        exact (hP.1 S hS).1
      _ = P.card * k := by simp
  have hbound : (P.biUnion id).card ≤ Fintype.card V := by
    simpa using Finset.card_le_card (Finset.subset_univ (P.biUnion id))
  have hmul : Fintype.card P * k ≤ Fintype.card V := by
    simpa [Fintype.card_coe, hcount] using hbound
  exact (Nat.le_div_iff_mul_le hk).2 hmul

/-- Vertices covered by a family of packed blocks. -/
private def covered {V : Type u} (P : Finset (Finset V)) : Set V :=
  {x | ∃ S ∈ P, x ∈ S}

private noncomputable def chosenBlock {V : Type u}
    (P : Finset (Finset V)) (x : covered P) :
    {i : P // x.val ∈ (i.val : Finset V)} := by
  classical
  have h : ∃ i : P, x.val ∈ (i.val : Finset V) := by
    obtain ⟨S, hS, hx⟩ := x.property
    exact ⟨⟨S, hS⟩, hx⟩
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

/-- A quotient color and one bipartition bit color the covered vertices. -/
private theorem packing_chromatic_le {V : Type u} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (P : Finset (Finset V))
    (hP : GoodPacking G k P) :
    HadwigerLean.chromatic (G.induce (covered P)) ≤
      2 * HadwigerLean.chromatic (packingQuotient G P) := by
  classical
  let Q := packingQuotient G P
  let qcolor : Q.Coloring (Fin (HadwigerLean.chromatic Q)) :=
    (HadwigerLean.colorable_chromatic Q).some
  let bcolor (i : P) :
      (G.induce (i.val : Set V)).Coloring (Fin 2) :=
    (hP.1 i.val i.property).2.2.some
  let pick (x : covered P) := chosenBlock P x
  let color (x : covered P) :
      Fin (HadwigerLean.chromatic Q) × Fin 2 :=
    (qcolor (pick x).val,
      bcolor (pick x).val ⟨x.val, (pick x).property⟩)
  have hproper : ∀ {x y : covered P},
      (G.induce (covered P)).Adj x y → color x ≠ color y := by
    intro x y hxy heq
    by_cases hij : (pick x).val = (pick y).val
    · have hy : y.val ∈ ((pick x).val.val : Finset V) := by
        rw [hij]
        exact (pick y).property
      have hlocal : (G.induce ((pick x).val.val : Set V)).Adj
          ⟨x.val, (pick x).property⟩ ⟨y.val, hy⟩ := hxy
      have hbit := (bcolor (pick x).val).valid hlocal
      have hsnd := congrArg Prod.snd heq
      have bcolor_eq_of_eq {i j : P} (hij' : i = j) (v : V)
          (hi : v ∈ (i.val : Finset V)) (hj : v ∈ (j.val : Finset V)) :
          bcolor i ⟨v, hi⟩ = bcolor j ⟨v, hj⟩ := by
        cases hij'
        rfl
      have hbit_eq :
          bcolor (pick x).val ⟨y.val, hy⟩ =
            bcolor (pick y).val ⟨y.val, (pick y).property⟩ :=
        bcolor_eq_of_eq hij y.val hy (pick y).property
      apply hbit
      exact hsnd.trans hbit_eq.symm
    · have hq : Q.Adj (pick x).val (pick y).val :=
        ⟨hij, x.val, (pick x).property, y.val, (pick y).property, hxy⟩
      have hfirst := qcolor.valid hq
      apply hfirst
      exact congrArg Prod.fst heq
  let C : (G.induce (covered P)).Coloring
      (Fin (HadwigerLean.chromatic Q) × Fin 2) :=
    SimpleGraph.Coloring.mk color hproper
  have hc : (G.induce (covered P)).Colorable
      (2 * HadwigerLean.chromatic Q) := by
    simpa [Fintype.card_prod, mul_comm] using C.colorable
  exact (HadwigerLean.chromatic_le_iff_colorable _ _).mpr hc
/-- There is a packing to which no good block disjoint from the covered
vertices can be added. -/
private theorem exists_maximal_goodPacking {V : Type u} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) :
    ∃ P : Finset (Finset V), GoodPacking G k P ∧
      ∀ S : Finset V, GoodBlock G k S →
        (∀ T ∈ P, Disjoint S T) → S = ∅ := by
  classical
  let packs : Finset (Finset (Finset V)) :=
    Finset.univ.filter (GoodPacking G k)
  have hempty : (∅ : Finset (Finset V)) ∈ packs := by
    simp [packs, GoodPacking]
  obtain ⟨P, hP, hmax⟩ :=
    Finset.exists_mem_eq_sup packs ⟨∅, hempty⟩ Finset.card
  have hgood : GoodPacking G k P := by
    simpa [packs] using hP
  refine ⟨P, hgood, ?_⟩
  intro S hS hdisj
  by_contra hnonempty
  have hSnot : S ∉ P := by
    intro hSP
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hnonempty
    exact (Finset.disjoint_left.mp (hdisj S hSP)) hx hx
  have hpack' : GoodPacking G k (insert S P) := by
    constructor
    · intro T hT
      rcases Finset.mem_insert.mp hT with rfl | hTP
      · exact hS
      · exact hgood.1 T hTP
    · intro A hA B hB hAB
      rcases Finset.mem_insert.mp hA with rfl | hAP
      · rcases Finset.mem_insert.mp hB with rfl | hBP
        · exact (hAB rfl).elim
        · apply Finset.disjoint_left.mpr
          intro x hxS hxB
          exact (Finset.disjoint_left.mp (hdisj B hBP)) hxS hxB
      · rcases Finset.mem_insert.mp hB with rfl | hBP
        · apply Finset.disjoint_left.mpr
          intro x hxA hxS
          exact (Finset.disjoint_right.mp (hdisj A hAP)) hxA hxS
        · exact hgood.2 A hAP B hBP hAB
  have hmem : insert S P ∈ packs := by
    simp [packs, hpack']
  have hle : (insert S P).card ≤ P.card := by
    have h := Finset.le_sup (f := Finset.card) hmem
    simpa [hmax] using h
  have hlt : P.card < (insert S P).card := by
    simp [hSnot]
  exact (Nat.not_lt_of_ge hle hlt).elim


/-- Paper Lemma 12: pack disjoint connected bipartite induced (k)-sets,
contract them to a smaller minor, and leave a remainder with no such set. -/
theorem exists_packing {V : Type u} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (hk : 2 ≤ k) :
    ∃ (P : Finset (Finset V)) (W R : Set V) (Q : SimpleGraph P),
      Disjoint W R ∧ W ∪ R = Set.univ ∧
      HadwigerLean.IsMinor Q G ∧
      Fintype.card P ≤ Fintype.card V / k ∧
      NoLargeConnectedBipartite (G.induce R) k ∧
      HadwigerLean.chromatic (G.induce W) ≤
        2 * HadwigerLean.chromatic Q := by
  classical
  obtain ⟨P, hP, hmax⟩ := exists_maximal_goodPacking G k
  let W : Set V := covered P
  let R : Set V := Wᶜ
  let Q : SimpleGraph P := packingQuotient G P
  refine ⟨P, W, R, Q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact disjoint_compl_right
  · change W ∪ Wᶜ = Set.univ
    exact Set.union_compl_self W
  · exact packingQuotient_isMinor G k P hP
  · exact packingQuotient_card_le G k P hP (by omega)
  · intro s hcard hs
    let S : Finset V := s.map ⟨Subtype.val, Subtype.val_injective⟩
    have hgood : GoodBlock G k S :=
      goodBlock_of_induce G R k s hcard hs.1 hs.2
    have hdisj : ∀ T ∈ P, Disjoint S T := by
      intro T hT
      apply Finset.disjoint_left.mpr
      intro x hxS hxT
      obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hxS
      subst x
      have hyW : y.val ∈ W := ⟨T, hT, hxT⟩
      exact y.property hyW
    have hSempty := hmax S hgood hdisj
    have hScard : S.card = k := hgood.1
    have hzero : S.card = 0 := by simp [hSempty]
    omega
  · exact packing_chromatic_le G k P hP
end HadwigerLean.Bootstrap
