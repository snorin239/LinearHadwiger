import HadwigerLean.Graph.VertexConnectivity
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Partial coloring templates and weighted recoloring

These are the finite list-coloring objects used in the additive
Girão--Narayanan chromatic connectivity argument.  A template lives on a
vertex set `carrier`, precolors `precolored`, and forbids a finite set of
colors at each other vertex.  Its extension is a proper coloring of the
induced graph on `carrier` respecting both restrictions.
-/

namespace HadwigerLean

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

/-- A partial coloring and forbidden-color lists on a finite induced graph. -/
structure ChromaticTemplate (V C : Type*) [DecidableEq V] where
  carrier : Finset V
  precolored : Finset V
  precolored_subset : precolored ⊆ carrier
  color : V → C
  forbidden : V → Finset C

namespace ChromaticTemplate

variable (G : SimpleGraph V) (T : ChromaticTemplate V C)

/-- The prescribed colors form a proper coloring on the precolored vertices. -/
def ProperPrecoloring : Prop :=
  ∀ ⦃u v : V⦄, u ∈ T.precolored → v ∈ T.precolored →
    G.Adj u v → T.color u ≠ T.color v

/-- A full proper coloring which extends a template. -/
def Extends (f : V → C) : Prop :=
  (∀ ⦃u v : V⦄, u ∈ T.carrier → v ∈ T.carrier → G.Adj u v → f u ≠ f v) ∧
  (∀ v ∈ T.precolored, f v = T.color v) ∧
  (∀ v ∈ T.carrier \ T.precolored, f v ∉ T.forbidden v)

/-- The precolored vertices cost `k` each, while every forbidden color costs one. -/
def degree (k : ℕ) : ℕ :=
  k * T.precolored.card +
    ∑ v ∈ T.carrier \ T.precolored, (T.forbidden v).card

/-- The numerical and properness conditions of the GN template argument. -/
def Admissible (k : ℕ) : Prop :=
  T.ProperPrecoloring G ∧ T.degree k ≤ 2 * k ^ 2 ∧
    ∀ v ∈ T.carrier \ T.precolored, (T.forbidden v).card ≤ 2 * k

/-- An admissible template can still have no extension. -/
def Obstructing : Prop := ¬ ∃ f : V → C, T.Extends G f

/-- Restrict a template to a vertex subset. -/
def restrict (U : Finset V) : ChromaticTemplate V C where
  carrier := T.carrier ∩ U
  precolored := T.precolored ∩ U
  precolored_subset := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨T.precolored_subset (Finset.mem_inter.mp hx).1,
      (Finset.mem_inter.mp hx).2⟩
  color := T.color
  forbidden := T.forbidden

@[simp] theorem restrict_carrier (U : Finset V) : (T.restrict U).carrier = T.carrier ∩ U := rfl
@[simp] theorem restrict_precolored (U : Finset V) :
    (T.restrict U).precolored = T.precolored ∩ U := rfl

theorem properPrecoloring_restrict (h : T.ProperPrecoloring G) (U : Finset V) :
    (T.restrict U).ProperPrecoloring G := by
  intro u v hu hv huv
  exact h (Finset.mem_inter.mp hu).1 (Finset.mem_inter.mp hv).1 huv

theorem degree_restrict_le (k : ℕ) (U : Finset V) :
    (T.restrict U).degree k ≤ T.degree k := by
  classical
  unfold degree
  have hpre : (T.precolored ∩ U).card ≤ T.precolored.card :=
    Finset.card_le_card Finset.inter_subset_left
  have hsub : (T.carrier ∩ U) \ (T.precolored ∩ U) ⊆
      T.carrier \ T.precolored := by
    intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hx'.1).1, ?_⟩
    intro hp
    exact hx'.2 (Finset.mem_inter.mpr ⟨hp, (Finset.mem_inter.mp hx'.1).2⟩)
  exact add_le_add (Nat.mul_le_mul_left k hpre)
    (Finset.sum_le_sum_of_subset hsub)

theorem admissible_restrict (h : T.Admissible G k) (U : Finset V) :
    (T.restrict U).Admissible G k := by
  refine ⟨T.properPrecoloring_restrict G h.1 U,
    (T.degree_restrict_le k U).trans h.2.1, ?_⟩
  intro v hv
  exact h.2.2 v (by
    have hv' := Finset.mem_sdiff.mp hv
    refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hv'.1).1, ?_⟩
    intro hp
    exact hv'.2 (Finset.mem_inter.mpr ⟨hp, (Finset.mem_inter.mp hv'.1).2⟩))

/-- An admissible template precolors at most twice k vertices when k > 0. -/
theorem precolored_card_le (k : ℕ) (hk : 0 < k)
    (h : T.Admissible G k) : T.precolored.card ≤ 2 * k := by
  have hdeg : k * T.precolored.card ≤ 2 * k ^ 2 := by
    exact (Nat.le_add_right _ _).trans h.2.1
  have hdeg' : k * T.precolored.card ≤ k * (2 * k) := by
    simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hdeg
  exact le_of_mul_le_mul_left hdeg' hk

/-- The portion of a template's degree charged to a vertex set. -/
def degreeOn (k : ℕ) (U : Finset V) : ℕ :=
  k * (T.precolored ∩ U).card +
    ∑ v ∈ (T.carrier \ T.precolored) ∩ U, (T.forbidden v).card

theorem degreeOn_disjoint_add_le (k : ℕ) (Y Z : Finset V)
    (hYZ : Disjoint Y Z) :
    T.degreeOn k Y + T.degreeOn k Z ≤ T.degree k := by
  classical
  let SY := T.precolored ∩ Y
  let SZ := T.precolored ∩ Z
  let A := T.carrier \ T.precolored
  let AY := A ∩ Y
  let AZ := A ∩ Z
  have hSdisj : Disjoint SY SZ := by
    apply Finset.disjoint_left.mpr
    intro v hvY hvZ
    exact (Finset.disjoint_left.mp hYZ)
      (Finset.mem_inter.mp hvY).2 (Finset.mem_inter.mp hvZ).2
  have hSsub : SY ∪ SZ ⊆ T.precolored := by
    intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · exact (Finset.mem_inter.mp h).1
    · exact (Finset.mem_inter.mp h).1
  have hScard : SY.card + SZ.card ≤ T.precolored.card := by
    rw [← Finset.card_union_of_disjoint hSdisj]
    exact Finset.card_le_card hSsub
  have hAdisj : Disjoint AY AZ := by
    apply Finset.disjoint_left.mpr
    intro v hvY hvZ
    exact (Finset.disjoint_left.mp hYZ)
      (Finset.mem_inter.mp hvY).2 (Finset.mem_inter.mp hvZ).2
  have hAsub : AY ∪ AZ ⊆ A := by
    intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · exact (Finset.mem_inter.mp h).1
    · exact (Finset.mem_inter.mp h).1
  have hAsum : (∑ v ∈ AY, (T.forbidden v).card) +
      (∑ v ∈ AZ, (T.forbidden v).card) ≤
      ∑ v ∈ A, (T.forbidden v).card := by
    rw [← Finset.sum_union hAdisj]
    exact Finset.sum_le_sum_of_subset hAsub
  have hSmul := Nat.mul_le_mul_left k hScard
  rw [Nat.mul_add] at hSmul
  unfold degreeOn degree
  change k * SY.card + (∑ v ∈ AY, (T.forbidden v).card) +
      (k * SZ.card + ∑ v ∈ AZ, (T.forbidden v).card) ≤
    k * T.precolored.card + ∑ v ∈ A, (T.forbidden v).card
  omega

theorem one_side_low_degree (k : ℕ) (Y Z : Finset V)
    (h : T.degree k ≤ 2 * k ^ 2)
    (hYZ : Disjoint Y Z) :
    T.degreeOn k Y ≤ k ^ 2 ∨ T.degreeOn k Z ≤ k ^ 2 := by
  have hsum := (T.degreeOn_disjoint_add_le k Y Z hYZ).trans h
  omega

/-- Move one uncolored vertex into the precolored set. Its old forbidden
list is enforced by the choice of its new prescribed color. -/
def precolor (v : V) (hv : v ∈ T.carrier) (γ : C) : ChromaticTemplate V C where
  carrier := T.carrier
  precolored := insert v T.precolored
  precolored_subset := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hv
    · exact T.precolored_subset hx
  color := Function.update T.color v γ
  forbidden := Function.update T.forbidden v ∅

/-- Precoloring a vertex by a color outside its old forbidden list preserves
the failure of extendibility. -/
theorem precolor_obstructing (v : V) (hv : v ∈ T.carrier \ T.precolored)
    (γ : C) (hγ : γ ∉ T.forbidden v) (hobs : T.Obstructing G) :
    (T.precolor v (Finset.mem_sdiff.mp hv).1 γ).Obstructing G := by
  intro hnew
  obtain ⟨f, hf⟩ := hnew
  apply hobs
  refine ⟨f, ?_, ?_, ?_⟩
  · exact hf.1
  · intro w hw
    have hwv : w ≠ v := by
      intro heq
      subst w
      exact (Finset.mem_sdiff.mp hv).2 hw
    have h := hf.2.1 w (Finset.mem_insert_of_mem hw)
    simpa [precolor, Function.update, hwv] using h
  · intro w hw
    by_cases heq : w = v
    · subst w
      have h := hf.2.1 v (Finset.mem_insert_self v T.precolored)
      have hfγ : f v = γ := by simpa [precolor] using h
      simpa [hfγ] using hγ
    · have hmem : w ∈ T.carrier \ insert v T.precolored := by
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hw).1,
          (by
            intro hi
            rcases Finset.mem_insert.mp hi with h | h
            · exact heq h
            · exact (Finset.mem_sdiff.mp hw).2 h)⟩
      have h := hf.2.2 w hmem
      simpa [precolor, Function.update, heq] using h

/-- If the chosen color avoids all existing prescribed colors and the old
forbidden list is large enough, precoloring preserves admissibility. -/
theorem precolor_admissible (k : ℕ) (h : T.Admissible G k)
    (v : V) (hv : v ∈ T.carrier \ T.precolored) (γ : C)
    (hγ : γ ∉ T.precolored.image T.color)
    (hkF : k ≤ (T.forbidden v).card) :
    (T.precolor v (Finset.mem_sdiff.mp hv).1 γ).Admissible G k := by
  classical
  have hvC : v ∈ T.carrier := (Finset.mem_sdiff.mp hv).1
  have hvS : v ∉ T.precolored := (Finset.mem_sdiff.mp hv).2
  have hcolor : ∀ w ∈ T.precolored, γ ≠ T.color w := by
    intro w hw heq
    apply hγ
    exact Finset.mem_image.mpr ⟨w, hw, heq.symm⟩
  have hproper : (T.precolor v hvC γ).ProperPrecoloring G := by
    intro u w hu hw huw
    change (Function.update T.color v γ) u ≠ (Function.update T.color v γ) w
    have huwne : u ≠ w := G.ne_of_adj huw
    by_cases huv : u = v
    · have hwv : w ≠ v := by
        intro heq
        exact huwne (huv.trans heq.symm)
      have hwold : w ∈ T.precolored := by
        rcases Finset.mem_insert.mp hw with heq | hs
        · exact False.elim (hwv heq)
        · exact hs
      simpa [Function.update, huv, hwv] using hcolor w hwold
    · have huold : u ∈ T.precolored := by
        rcases Finset.mem_insert.mp hu with heq | hs
        · exact False.elim (huv heq)
        · exact hs
      by_cases hwv : w = v
      · simpa [Function.update, huv, hwv] using (hcolor u huold).symm
      · have hwold : w ∈ T.precolored := by
          rcases Finset.mem_insert.mp hw with heq | hs
          · exact False.elim (hwv heq)
          · exact hs
        simpa [Function.update, huv, hwv] using h.1 huold hwold huw
  let A := T.carrier \ T.precolored
  let B := T.carrier \ insert v T.precolored
  have hB : B = A.erase v := by
    ext w
    by_cases hwv : w = v
    · subst w
      simp [A, B]
    · simp [A, B, hwv, Finset.mem_sdiff, Finset.mem_insert]
  have hsum : (∑ w ∈ A, (T.forbidden w).card) =
      (T.forbidden v).card + ∑ w ∈ B, (T.forbidden w).card := by
    rw [hB, Finset.add_sum_erase A (fun w => (T.forbidden w).card) hv]
  have hnewsum : (∑ w ∈ B, ((Function.update T.forbidden v ∅) w).card) =
      ∑ w ∈ B, (T.forbidden w).card := by
    apply Finset.sum_congr rfl
    intro w hw
    have hwv : w ≠ v := by
      intro heq
      subst w
      exact (Finset.mem_sdiff.mp hw).2 (Finset.mem_insert_self _ _)
    simp [Function.update, hwv]
  have hprec : (insert v T.precolored).card = T.precolored.card + 1 := by
    simp [hvS]
  have hdegree : (T.precolor v hvC γ).degree k ≤ T.degree k := by
    unfold degree
    change k * (insert v T.precolored).card +
      (∑ w ∈ B, ((Function.update T.forbidden v ∅) w).card) ≤
      k * T.precolored.card + ∑ w ∈ A, (T.forbidden w).card
    rw [hprec, hnewsum, hsum, Nat.mul_add]
    omega
  refine ⟨hproper, hdegree.trans h.2.1, ?_⟩
  intro w hw
  have hwB : w ∈ B := hw
  have hwA : w ∈ A := by
    refine Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hwB).1, ?_⟩
    intro hws
    exact (Finset.mem_sdiff.mp hwB).2 (Finset.mem_insert_of_mem hws)
  have hwv : w ≠ v := by
    intro heq
    subst w
    exact (Finset.mem_sdiff.mp hwB).2 (Finset.mem_insert_self _ _)
  simpa [precolor, Function.update, hwv] using h.2.2 w hwA

/-- A palette with more than four k colors contains a color which is both
allowed at an uncolored vertex and unused by the precoloring. -/
theorem exists_fresh_color (k : ℕ) (hk : 0 < k) (h : T.Admissible G k)
    (hpalette : 4 * k < Fintype.card C)
    (v : V) (hv : v ∈ T.carrier \ T.precolored) :
    ∃ γ : C, γ ∉ T.forbidden v ∧ γ ∉ T.precolored.image T.color := by
  classical
  let U := T.forbidden v ∪ T.precolored.image T.color
  have hU : U.card < Fintype.card C := by
    have h1 : U.card ≤ (T.forbidden v).card +
        (T.precolored.image T.color).card := Finset.card_union_le _ _
    have h2 : (T.precolored.image T.color).card ≤ T.precolored.card :=
      Finset.card_image_le
    have h3 : (T.forbidden v).card ≤ 2 * k := h.2.2 v hv
    have h4 : T.precolored.card ≤ 2 * k := T.precolored_card_le G k hk h
    omega
  have hγ : ∃ γ : C, γ ∉ U := by
    by_contra hn
    have hsub : (Finset.univ : Finset C) ⊆ U := by
      intro x _
      by_cases hx : x ∈ U
      · exact hx
      · exact False.elim (hn ⟨x, hx⟩)
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_univ] at hcard
    omega
  obtain ⟨γ, hγ⟩ := hγ
  have hγ' : γ ∉ T.forbidden v ∧ γ ∉ T.precolored.image T.color := by
    simpa [U, Finset.mem_union] using hγ
  exact ⟨γ, hγ'.1, hγ'.2⟩

/-- If every uncolored vertex has at least as many available colors as there
are uncolored vertices, Hall's theorem gives an extension. -/
theorem extends_of_large_lists (base : C)
    (hproper : T.ProperPrecoloring G)
    (hlarge : ∀ v ∈ T.carrier \ T.precolored,
      (T.carrier \ T.precolored).card ≤
        ((Finset.univ : Finset C) \
          (T.forbidden v ∪ T.precolored.image T.color)).card) :
    ∃ f : V → C, T.Extends G f := by
  classical
  let A := T.carrier \ T.precolored
  let L : A → Finset C := fun v =>
    (Finset.univ : Finset C) \
      (T.forbidden v.1 ∪ T.precolored.image T.color)
  have hHall : ∀ s : Finset A, s.card ≤ (s.biUnion L).card := by
    intro s
    by_cases hs : s.Nonempty
    · obtain ⟨v, hv⟩ := hs
      calc
        s.card ≤ Fintype.card A := by
          simpa using Finset.card_le_card (Finset.subset_univ s)
        _ = A.card := Fintype.card_coe A
        _ ≤ (L v).card := hlarge v.1 v.2
        _ ≤ (s.biUnion L).card := by
          apply Finset.card_le_card
          intro c hc
          exact Finset.mem_biUnion.mpr ⟨v, hv, hc⟩
    · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      simp [hs0]
  obtain ⟨g, hginj, hgL⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' L).mp hHall
  let f : V → C := fun v =>
    if hs : v ∈ T.precolored then T.color v
    else if ha : v ∈ A then g ⟨v, ha⟩ else base
  have hfS : ∀ v ∈ T.precolored, f v = T.color v := by
    intro v hv
    simp [f, hv]
  have hfA : ∀ (v : V) (hv : v ∈ A), f v = g ⟨v, hv⟩ := by
    intro v hv
    have hvS : v ∉ T.precolored := (Finset.mem_sdiff.mp hv).2
    simp [f, hvS, hv]
  have hgavoid : ∀ v : A, g v ∉ T.forbidden v.1 ∧
      g v ∉ T.precolored.image T.color := by
    intro v
    have hv : g v ∈ (Finset.univ : Finset C) \
        (T.forbidden v.1 ∪ T.precolored.image T.color) := hgL v
    have hv' := (Finset.mem_sdiff.mp hv).2
    simpa only [Finset.mem_union, not_or] using hv'
  refine ⟨f, ?_, hfS, ?_⟩
  · intro u v hu hv huv
    by_cases huS : u ∈ T.precolored
    · by_cases hvS : v ∈ T.precolored
      · rw [hfS u huS, hfS v hvS]
        exact hproper huS hvS huv
      · have hvA : v ∈ A := Finset.mem_sdiff.mpr ⟨hv, hvS⟩
        rw [hfS u huS, hfA v hvA]
        intro heq
        have hmem : T.color u ∈ T.precolored.image T.color :=
          Finset.mem_image.mpr ⟨u, huS, rfl⟩
        exact (hgavoid ⟨v, hvA⟩).2 (heq.symm ▸ hmem)
    · have huA : u ∈ A := Finset.mem_sdiff.mpr ⟨hu, huS⟩
      by_cases hvS : v ∈ T.precolored
      · rw [hfA u huA, hfS v hvS]
        intro heq
        have hmem : T.color v ∈ T.precolored.image T.color :=
          Finset.mem_image.mpr ⟨v, hvS, rfl⟩
        exact (hgavoid ⟨u, huA⟩).2 (heq ▸ hmem)
      · have hvA : v ∈ A := Finset.mem_sdiff.mpr ⟨hv, hvS⟩
        rw [hfA u huA, hfA v hvA]
        intro heq
        have heqv : (⟨u, huA⟩ : A) = ⟨v, hvA⟩ := hginj heq
        exact (G.ne_of_adj huv) (congrArg Subtype.val heqv)
  · intro v hv
    rw [hfA v hv]
    exact (hgavoid ⟨v, hv⟩).1

/-- An admissible obstructing template with short lists needs more than k
vertices in its carrier. -/
theorem not_obstructing_of_small_carrier (base : C) (k : ℕ) (hk : 0 < k)
    (hpalette : 4 * k < Fintype.card C)
    (h : T.Admissible G k)
    (hshort : ∀ v ∈ T.carrier \ T.precolored, (T.forbidden v).card < k)
    (hcarrier : T.carrier.card ≤ k) :
    ¬ T.Obstructing G := by
  intro hobs
  have hpre : T.precolored.card ≤ 2 * k := T.precolored_card_le G k hk h
  have hlarge : ∀ v ∈ T.carrier \ T.precolored,
      (T.carrier \ T.precolored).card ≤
        ((Finset.univ : Finset C) \
          (T.forbidden v ∪ T.precolored.image T.color)).card := by
    intro v hv
    let B := T.forbidden v ∪ T.precolored.image T.color
    have hB : B.card ≤ (T.forbidden v).card +
        (T.precolored.image T.color).card := Finset.card_union_le _ _
    have himage : (T.precolored.image T.color).card ≤ T.precolored.card :=
      Finset.card_image_le
    have hA : (T.carrier \ T.precolored).card ≤ T.carrier.card :=
      Finset.card_le_card Finset.sdiff_subset
    have hC : ((Finset.univ : Finset C) \ B).card + B.card =
        Fintype.card C := by
      simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
    have hlist := hshort v hv
    dsimp [B] at hB hC
    omega
  obtain ⟨f, hf⟩ := T.extends_of_large_lists G base h.1 hlarge
  exact hobs ⟨f, hf⟩

/-- The first template in the separator argument: colors prescribed on the
far side are forbidden at the separator. -/
def firstSide (X Y Z : Finset V) : ChromaticTemplate V C where
  carrier := T.carrier ∩ (X ∪ Y)
  precolored := T.precolored ∩ (X ∪ Y)
  precolored_subset := by
    intro v hv
    exact Finset.mem_inter.mpr
      ⟨T.precolored_subset (Finset.mem_inter.mp hv).1,
        (Finset.mem_inter.mp hv).2⟩
  color := T.color
  forbidden := fun v =>
    if v ∈ X then T.forbidden v ∪
      ((T.precolored ∩ Z).image T.color)
    else T.forbidden v

/-- The second template in the separator argument: the separator is
precolored by an extension of the first side. -/
def secondSide (X Z : Finset V) (f : V → C) : ChromaticTemplate V C where
  carrier := T.carrier ∩ (X ∪ Z)
  precolored := (T.precolored ∩ Z) ∪ (T.carrier ∩ X)
  precolored_subset := by
    intro v hv
    rcases Finset.mem_union.mp hv with hSZ | hCX
    · have h := Finset.mem_inter.mp hSZ
      exact Finset.mem_inter.mpr
        ⟨T.precolored_subset h.1, Finset.mem_union.mpr (Or.inr h.2)⟩
    · have h := Finset.mem_inter.mp hCX
      exact Finset.mem_inter.mpr
        ⟨h.1, Finset.mem_union.mpr (Or.inl h.2)⟩
  color := fun v => if v ∈ X then f v else T.color v
  forbidden := T.forbidden

theorem firstSide_properPrecoloring (X Y Z : Finset V)
    (h : T.ProperPrecoloring G) :
    (T.firstSide X Y Z).ProperPrecoloring G := by
  intro u v hu hv huv
  exact h (Finset.mem_inter.mp hu).1 (Finset.mem_inter.mp hv).1 huv

theorem firstSide_list_bound (X Y Z : Finset V) (k : ℕ)
    (hshort : ∀ v ∈ T.carrier \ T.precolored, (T.forbidden v).card < k)
    (hSZ : (T.precolored ∩ Z).card ≤ k) :
    ∀ v ∈ (T.firstSide X Y Z).carrier \
      (T.firstSide X Y Z).precolored,
      ((T.firstSide X Y Z).forbidden v).card ≤ 2 * k := by
  classical
  intro v hv
  have hvC : v ∈ T.carrier := (Finset.mem_inter.mp
    (Finset.mem_sdiff.mp hv).1).1
  have hvS : v ∉ T.precolored := by
    intro h
    exact (Finset.mem_sdiff.mp hv).2
      (Finset.mem_inter.mpr
        ⟨h, (Finset.mem_inter.mp (Finset.mem_sdiff.mp hv).1).2⟩)
  have hvA : v ∈ T.carrier \ T.precolored :=
    Finset.mem_sdiff.mpr ⟨hvC, hvS⟩
  by_cases hx : v ∈ X
  · have hcard : ((T.precolored ∩ Z).image T.color).card ≤
        (T.precolored ∩ Z).card := Finset.card_image_le
    have hunion : (T.forbidden v ∪
        (T.precolored ∩ Z).image T.color).card ≤
        (T.forbidden v).card + ((T.precolored ∩ Z).image T.color).card :=
      Finset.card_union_le _ _
    have hF := hshort v hvA
    have hgoal : (T.forbidden v ∪
      (T.precolored ∩ Z).image T.color).card ≤ 2 * k := by omega
    simpa [firstSide, hx] using hgoal
  · have hF := hshort v hvA
    have hgoal : (T.forbidden v).card ≤ 2 * k := by omega
    simpa [firstSide, hx] using hgoal

theorem firstSide_degree_le (X Y Z : Finset V) (k : ℕ)
    (hX : X.card ≤ k) (hdisj : Disjoint Z (X ∪ Y)) :
    (T.firstSide X Y Z).degree k ≤ T.degree k := by
  classical
  let D := X ∪ Y
  let S₁ := T.precolored ∩ D
  let S₂ := T.precolored ∩ Z
  let A := (T.carrier ∩ D) \ S₁
  let A₀ := T.carrier \ T.precolored
  let P := S₂.image T.color
  have hA : A ⊆ A₀ := by
    intro v hv
    have hvc := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hv).1).1
    have hvd := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hv).1).2
    refine Finset.mem_sdiff.mpr ⟨hvc, ?_⟩
    intro hvs
    exact (Finset.mem_sdiff.mp hv).2
      (Finset.mem_inter.mpr ⟨hvs, hvd⟩)
  have hSdisj : Disjoint S₁ S₂ := by
    apply Finset.disjoint_left.mpr
    intro v hv₁ hv₂
    exact (Finset.disjoint_left.mp hdisj)
      (Finset.mem_inter.mp hv₂).2 (Finset.mem_inter.mp hv₁).2
  have hScard : S₁.card + S₂.card ≤ T.precolored.card := by
    have hsub : S₁ ∪ S₂ ⊆ T.precolored := by
      intro v hv
      rcases Finset.mem_union.mp hv with h₁ | h₂
      · exact (Finset.mem_inter.mp h₁).1
      · exact (Finset.mem_inter.mp h₂).1
    rw [← Finset.card_union_of_disjoint hSdisj]
    exact Finset.card_le_card hsub
  have hPcard : P.card ≤ S₂.card := Finset.card_image_le
  have hbase : (∑ v ∈ A, (T.forbidden v).card) ≤
      ∑ v ∈ A₀, (T.forbidden v).card :=
    Finset.sum_le_sum_of_subset hA
  let AX := A.filter (· ∈ X)
  have hAX : AX.card ≤ X.card := by
    apply Finset.card_le_card
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hbonusEq : (∑ v ∈ A, if v ∈ X then S₂.card else 0) =
      AX.card * S₂.card := by
    have hAXeq : A ∩ X = AX := by
      ext v
      simp [AX, Finset.mem_inter]
    simp [hAXeq, mul_comm]
  have hbonus : (∑ v ∈ A, if v ∈ X then S₂.card else 0) ≤
      k * S₂.card := by
    rw [hbonusEq]
    exact Nat.mul_le_mul_right S₂.card (hAX.trans hX)
  have hpoint : ∀ v ∈ A,
      ((T.firstSide X Y Z).forbidden v).card ≤
        (T.forbidden v).card + if v ∈ X then S₂.card else 0 := by
    intro v hv
    by_cases hx : v ∈ X
    · have hc := Finset.card_union_le (T.forbidden v) P
      have hcp : (T.forbidden v ∪ P).card ≤
          (T.forbidden v).card + S₂.card := by omega
      simpa [firstSide, hx, P, S₂] using hcp
    · simp [firstSide, hx]
  have hsum : (∑ v ∈ A, ((T.firstSide X Y Z).forbidden v).card) ≤
      (∑ v ∈ A, (T.forbidden v).card) +
        (∑ v ∈ A, if v ∈ X then S₂.card else 0) := by
    calc
      _ ≤ ∑ v ∈ A, ((T.forbidden v).card +
          if v ∈ X then S₂.card else 0) := Finset.sum_le_sum hpoint
      _ = _ := by rw [Finset.sum_add_distrib]
  have hmul := Nat.mul_le_mul_left k hScard
  rw [Nat.mul_add] at hmul
  change k * S₁.card + k * S₂.card ≤ k * T.precolored.card at hmul
  have hdegree : (T.firstSide X Y Z).degree k =
      k * S₁.card +
        ∑ v ∈ A, ((T.firstSide X Y Z).forbidden v).card := rfl
  rw [hdegree]
  unfold degree
  have hA₀ : A₀ = T.carrier \ T.precolored := rfl
  rw [← hA₀]
  omega

theorem firstSide_admissible (X Y Z : Finset V) (k : ℕ)
    (h : T.Admissible G k)
    (hshort : ∀ v ∈ T.carrier \ T.precolored, (T.forbidden v).card < k)
    (hX : X.card ≤ k) (hdisj : Disjoint Z (X ∪ Y))
    (hSZ : (T.precolored ∩ Z).card ≤ k) :
    (T.firstSide X Y Z).Admissible G k := by
  exact ⟨T.firstSide_properPrecoloring G X Y Z h.1,
    (T.firstSide_degree_le X Y Z k hX hdisj).trans h.2.1,
    T.firstSide_list_bound X Y Z k hshort hSZ⟩

theorem secondSide_list_bound (X Z : Finset V) (f : V → C) (k : ℕ)
    (h : T.Admissible G k) :
    ∀ v ∈ (T.secondSide X Z f).carrier \
      (T.secondSide X Z f).precolored,
      ((T.secondSide X Z f).forbidden v).card ≤ 2 * k := by
  intro v hv
  have hvC : v ∈ T.carrier :=
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp hv).1).1
  have hvXZ : v ∈ X ∪ Z :=
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp hv).1).2
  have hvNotX : v ∉ X := by
    intro hX
    exact (Finset.mem_sdiff.mp hv).2
      (Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hvC, hX⟩)))
  have hvZ : v ∈ Z := by
    rcases Finset.mem_union.mp hvXZ with hx | hz
    · exact False.elim (hvNotX hx)
    · exact hz
  have hvS : v ∉ T.precolored := by
    intro hs
    exact (Finset.mem_sdiff.mp hv).2
      (Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hs, hvZ⟩)))
  exact h.2.2 v (Finset.mem_sdiff.mpr ⟨hvC, hvS⟩)

theorem secondSide_degree_le (X Z : Finset V) (f : V → C) (k : ℕ)
    (hX : X.card ≤ k) (hdisjXZ : Disjoint X Z)
    (hlow : k * (T.precolored ∩ Z).card +
      (∑ v ∈ (T.carrier \ T.precolored) ∩ Z, (T.forbidden v).card) ≤
        k ^ 2) :
    (T.secondSide X Z f).degree k ≤ 2 * k ^ 2 := by
  classical
  let SZ := T.precolored ∩ Z
  let CX := T.carrier ∩ X
  let A := (T.secondSide X Z f).carrier \
    (T.secondSide X Z f).precolored
  let AZ := (T.carrier \ T.precolored) ∩ Z
  have hdisj : Disjoint SZ CX := by
    apply Finset.disjoint_left.mpr
    intro v hvSZ hvCX
    exact (Finset.disjoint_left.mp hdisjXZ)
      (Finset.mem_inter.mp hvCX).2 (Finset.mem_inter.mp hvSZ).2
  have hprec : (T.secondSide X Z f).precolored.card =
      SZ.card + CX.card := by
    change (SZ ∪ CX).card = SZ.card + CX.card
    exact Finset.card_union_of_disjoint hdisj
  have hA : A ⊆ AZ := by
    intro v hv
    have hvC : v ∈ T.carrier :=
      (Finset.mem_inter.mp (Finset.mem_sdiff.mp hv).1).1
    have hvXZ : v ∈ X ∪ Z :=
      (Finset.mem_inter.mp (Finset.mem_sdiff.mp hv).1).2
    have hvNotPre := (Finset.mem_sdiff.mp hv).2
    have hvNotX : v ∉ X := by
      intro hx
      exact hvNotPre (Finset.mem_union.mpr
        (Or.inr (Finset.mem_inter.mpr ⟨hvC, hx⟩)))
    have hvZ : v ∈ Z := by
      rcases Finset.mem_union.mp hvXZ with hx | hz
      · exact False.elim (hvNotX hx)
      · exact hz
    have hvNotS : v ∉ T.precolored := by
      intro hs
      exact hvNotPre (Finset.mem_union.mpr
        (Or.inl (Finset.mem_inter.mpr ⟨hs, hvZ⟩)))
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨hvC, hvNotS⟩, hvZ⟩
  have hsum : (∑ v ∈ A, (T.forbidden v).card) ≤
      ∑ v ∈ AZ, (T.forbidden v).card :=
    Finset.sum_le_sum_of_subset hA
  have hCXcard : CX.card ≤ k := by
    have hsub : CX ⊆ X := Finset.inter_subset_right
    exact (Finset.card_le_card hsub).trans hX
  have hXmul : k * CX.card ≤ k * k := Nat.mul_le_mul_left k hCXcard
  have hlow' : k * SZ.card +
      (∑ v ∈ AZ, (T.forbidden v).card) ≤ k ^ 2 := by
    simpa [SZ, AZ] using hlow
  have hdegree : (T.secondSide X Z f).degree k =
      k * (SZ.card + CX.card) +
      ∑ v ∈ A, (T.forbidden v).card := by
    unfold degree
    rw [hprec]
    rfl
  rw [hdegree, Nat.mul_add]
  simp only [pow_two, two_mul] at hlow' ⊢
  omega

theorem secondSide_properPrecoloring (X Y Z : Finset V) (f : V → C)
    (hT : T.ProperPrecoloring G)
    (hdisjXZ : Disjoint X Z)
    (hf : (T.firstSide X Y Z).Extends G f) :
    (T.secondSide X Z f).ProperPrecoloring G := by
  classical
  have hnotX : ∀ z ∈ Z, z ∉ X := by
    intro z hz hx
    exact (Finset.disjoint_left.mp hdisjXZ) hx hz
  have hcross : ∀ ⦃x z : V⦄, x ∈ T.carrier ∩ X →
      z ∈ T.precolored ∩ Z → G.Adj x z → f x ≠ T.color z := by
    intro x z hx hz hxz
    have hxC := (Finset.mem_inter.mp hx).1
    have hxX := (Finset.mem_inter.mp hx).2
    have hzS := (Finset.mem_inter.mp hz).1
    have hzZ := (Finset.mem_inter.mp hz).2
    by_cases hxS : x ∈ T.precolored
    · have hfx := hf.2.1 x
        (Finset.mem_inter.mpr
          ⟨hxS, Finset.mem_union.mpr (Or.inl hxX)⟩)
      have hproper := hT hxS hzS hxz
      simpa [firstSide] using hfx ▸ hproper
    · have hxA : x ∈ (T.firstSide X Y Z).carrier \
          (T.firstSide X Y Z).precolored := by
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr
              ⟨hxC, Finset.mem_union.mpr (Or.inl hxX)⟩,
            fun h => hxS (Finset.mem_inter.mp h).1⟩
      have havid := hf.2.2 x hxA
      have hmem : T.color z ∈ (T.firstSide X Y Z).forbidden x := by
        have himage : T.color z ∈
            (T.precolored ∩ Z).image T.color :=
          Finset.mem_image.mpr ⟨z,
            Finset.mem_inter.mpr ⟨hzS, hzZ⟩, rfl⟩
        simp [firstSide, hxX, himage]
      intro heq
      exact havid (heq.symm ▸ hmem)
  intro u v hu hv huv
  rcases Finset.mem_union.mp hu with huSZ | huCX
  · rcases Finset.mem_union.mp hv with hvSZ | hvCX
    · have huS := (Finset.mem_inter.mp huSZ).1
      have hvS := (Finset.mem_inter.mp hvSZ).1
      have huZ := (Finset.mem_inter.mp huSZ).2
      have hvZ := (Finset.mem_inter.mp hvSZ).2
      simpa [secondSide, hnotX u huZ, hnotX v hvZ] using
        hT huS hvS huv
    · have huZ := (Finset.mem_inter.mp huSZ).2
      have hvX := (Finset.mem_inter.mp hvCX).2
      simpa [secondSide, hnotX u huZ, hvX] using
        (hcross hvCX huSZ huv.symm).symm
  · rcases Finset.mem_union.mp hv with hvSZ | hvCX
    · have huX := (Finset.mem_inter.mp huCX).2
      have hvZ := (Finset.mem_inter.mp hvSZ).2
      simpa [secondSide, huX, hnotX v hvZ] using
        hcross huCX hvSZ huv
    · have huX := (Finset.mem_inter.mp huCX).2
      have hvX := (Finset.mem_inter.mp hvCX).2
      have hproper := hf.1
        (Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp huCX).1,
            Finset.mem_union.mpr (Or.inl huX)⟩)
        (Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hvCX).1,
            Finset.mem_union.mpr (Or.inl hvX)⟩) huv
      simpa [secondSide, huX, hvX] using hproper

theorem secondSide_admissible (X Y Z : Finset V) (f : V → C) (k : ℕ)
    (h : T.Admissible G k) (hX : X.card ≤ k)
    (hdisjXZ : Disjoint X Z)
    (hlow : k * (T.precolored ∩ Z).card +
      (∑ v ∈ (T.carrier \ T.precolored) ∩ Z, (T.forbidden v).card) ≤
        k ^ 2)
    (hf : (T.firstSide X Y Z).Extends G f) :
    (T.secondSide X Z f).Admissible G k := by
  exact ⟨T.secondSide_properPrecoloring G X Y Z f h.1 hdisjXZ hf,
    T.secondSide_degree_le X Z f k hX hdisjXZ hlow,
    T.secondSide_list_bound G X Z f k h⟩

theorem firstSide_extends_restrict (X Y Z : Finset V) (f : V → C)
    (hf : (T.firstSide X Y Z).Extends G f) :
    (T.restrict (X ∪ Y)).Extends G f := by
  refine ⟨hf.1, ?_, ?_⟩
  · intro v hv
    exact hf.2.1 v hv
  · intro v hv
    have hav := hf.2.2 v hv
    by_cases hx : v ∈ X
    · have hav' : f v ∉ T.forbidden v ∪
          (T.precolored ∩ Z).image T.color := by
        simpa [firstSide, hx, restrict] using hav
      exact fun h => hav' (Finset.mem_union.mpr (Or.inl h))
    · simpa [firstSide, hx, restrict] using hav

theorem secondSide_extends_restrict (X Y Z : Finset V) (f₁ f₂ : V → C)
    (hX : X ⊆ T.carrier)
    (h₁ : (T.firstSide X Y Z).Extends G f₁)
    (h₂ : (T.secondSide X Z f₁).Extends G f₂) :
    (T.restrict (X ∪ Z)).Extends G f₂ ∧
      ∀ x ∈ X, f₁ x = f₂ x := by
  have hagree : ∀ x ∈ X, f₁ x = f₂ x := by
    intro x hx
    have hxpre : x ∈ (T.secondSide X Z f₁).precolored :=
      Finset.mem_union.mpr (Or.inr
        (Finset.mem_inter.mpr ⟨hX hx, hx⟩))
    have h := h₂.2.1 x hxpre
    simpa [secondSide, hx] using h.symm
  have h₁r := T.firstSide_extends_restrict G X Y Z f₁ h₁
  refine ⟨?_, hagree⟩
  refine ⟨h₂.1, ?_, ?_⟩
  · intro v hv
    have hvS := (Finset.mem_inter.mp hv).1
    have hvXZ := (Finset.mem_inter.mp hv).2
    by_cases hvX : v ∈ X
    · have hv₁ : v ∈ (T.restrict (X ∪ Y)).precolored :=
        Finset.mem_inter.mpr
          ⟨hvS, Finset.mem_union.mpr (Or.inl hvX)⟩
      rw [← hagree v hvX]
      exact h₁r.2.1 v hv₁
    · have hvZ : v ∈ Z := by
        rcases Finset.mem_union.mp hvXZ with hx | hz
        · exact False.elim (hvX hx)
        · exact hz
      have hv₂ : v ∈ (T.secondSide X Z f₁).precolored :=
        Finset.mem_union.mpr (Or.inl
          (Finset.mem_inter.mpr ⟨hvS, hvZ⟩))
      have h := h₂.2.1 v hv₂
      simpa [secondSide, hvX, restrict] using h
  · intro v hv
    have hvC := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hv).1).1
    have hvXZ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hv).1).2
    have hvS : v ∉ T.precolored := by
      intro hs
      exact (Finset.mem_sdiff.mp hv).2
        (Finset.mem_inter.mpr ⟨hs, hvXZ⟩)
    by_cases hvX : v ∈ X
    · have hv₁ : v ∈ (T.restrict (X ∪ Y)).carrier \
          (T.restrict (X ∪ Y)).precolored :=
        Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr
            ⟨hvC, Finset.mem_union.mpr (Or.inl hvX)⟩,
            fun h => hvS (Finset.mem_inter.mp h).1⟩
      have h := h₁r.2.2 v hv₁
      rw [← hagree v hvX]
      simpa [restrict] using h
    · have hvZ : v ∈ Z := by
        rcases Finset.mem_union.mp hvXZ with hx | hz
        · exact False.elim (hvX hx)
        · exact hz
      have hv₂ : v ∈ (T.secondSide X Z f₁).carrier \
          (T.secondSide X Z f₁).precolored :=
        Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr
            ⟨hvC, Finset.mem_union.mpr (Or.inr hvZ)⟩,
            (by
              intro hp
              rcases Finset.mem_union.mp hp with hSZ | hCX
              · exact hvS (Finset.mem_inter.mp hSZ).1
              · exact hvX (Finset.mem_inter.mp hCX).2)⟩
      have h := h₂.2.2 v hv₂
      simpa [secondSide, restrict] using h

/-- Colorings of two overlapping sides glue when they agree on the separator
and there are no edges between the strict sides. -/
theorem glue_extensions (X Y Z : Finset V)
    (hcover : T.carrier = X ∪ Y ∪ Z)
    (hno : ∀ ⦃y z : V⦄, y ∈ Y → z ∈ Z → ¬ G.Adj y z)
    (f₁ f₂ : V → C)
    (h₁ : (T.restrict (X ∪ Y)).Extends G f₁)
    (h₂ : (T.restrict (X ∪ Z)).Extends G f₂)
    (hagree : ∀ x ∈ X, f₁ x = f₂ x) :
    ∃ f : V → C, T.Extends G f := by
  classical
  let f : V → C := fun v => if v ∈ Z then f₂ v else f₁ v
  have hpart : ∀ v ∈ T.carrier, v ∈ X ∨ v ∈ Y ∨ v ∈ Z := by
    intro v hv
    rw [hcover] at hv
    simpa only [Finset.mem_union, or_assoc] using hv
  have hleft : ∀ v ∈ T.carrier, v ∉ Z → v ∈ X ∪ Y := by
    intro v hv hvZ
    rcases hpart v hv with hx | hy | hz
    · exact Finset.mem_union.mpr (Or.inl hx)
    · exact Finset.mem_union.mpr (Or.inr hy)
    · exact False.elim (hvZ hz)
  have hright : ∀ v ∈ T.carrier, v ∈ Z → v ∈ X ∪ Z := by
    intro v hv hz
    exact Finset.mem_union.mpr (Or.inr hz)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro u v hu hv huv
    by_cases huZ : u ∈ Z
    · by_cases hvZ : v ∈ Z
      · have h := h₂.1 (Finset.mem_inter.mpr ⟨hu, hright u hu huZ⟩)
          (Finset.mem_inter.mpr ⟨hv, hright v hv hvZ⟩) huv
        simpa [f, huZ, hvZ] using h
      · rcases hpart v hv with hvX | hvY | hvZ'
        · have h := h₂.1 (Finset.mem_inter.mpr ⟨hu, hright u hu huZ⟩)
            (Finset.mem_inter.mpr ⟨hv,
              Finset.mem_union.mpr (Or.inl hvX)⟩) huv
          simpa [f, huZ, hvZ, hagree v hvX] using h
        · exact False.elim ((hno hvY huZ) huv.symm)
        · exact False.elim (hvZ hvZ')
    · by_cases hvZ : v ∈ Z
      · rcases hpart u hu with huX | huY | huZ'
        · have h := h₂.1 (Finset.mem_inter.mpr ⟨hu,
              Finset.mem_union.mpr (Or.inl huX)⟩)
            (Finset.mem_inter.mpr ⟨hv, hright v hv hvZ⟩) huv
          simpa [f, huZ, hvZ, hagree u huX] using h
        · exact False.elim ((hno huY hvZ) huv)
        · exact False.elim (huZ huZ')
      · have h := h₁.1
          (Finset.mem_inter.mpr ⟨hu, hleft u hu huZ⟩)
          (Finset.mem_inter.mpr ⟨hv, hleft v hv hvZ⟩) huv
        simpa [f, huZ, hvZ] using h
  · intro v hv
    have hvC := T.precolored_subset hv
    by_cases hvZ : v ∈ Z
    · have h := h₂.2.1 v (Finset.mem_inter.mpr
        ⟨hv, hright v hvC hvZ⟩)
      simpa [f, hvZ, restrict] using h
    · have h := h₁.2.1 v (Finset.mem_inter.mpr
        ⟨hv, hleft v hvC hvZ⟩)
      simpa [f, hvZ, restrict] using h
  · intro v hv
    have hvC := (Finset.mem_sdiff.mp hv).1
    have hvS := (Finset.mem_sdiff.mp hv).2
    by_cases hvZ : v ∈ Z
    · have hmem : v ∈ (T.restrict (X ∪ Z)).carrier \
          (T.restrict (X ∪ Z)).precolored := by
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨hvC, hright v hvC hvZ⟩,
            fun h => hvS (Finset.mem_inter.mp h).1⟩
      have h := h₂.2.2 v hmem
      simpa [f, hvZ, restrict] using h
    · have hmem : v ∈ (T.restrict (X ∪ Y)).carrier \
          (T.restrict (X ∪ Y)).precolored := by
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨hvC, hleft v hvC hvZ⟩,
            fun h => hvS (Finset.mem_inter.mp h).1⟩
      have h := h₁.2.2 v hmem
      simpa [f, hvZ, restrict] using h

/-- The two separator-side templates cannot both be extendible when the
original template obstructs its carrier. -/
theorem not_both_side_extensions (X Y Z : Finset V)
    (hcover : T.carrier = X ∪ Y ∪ Z)
    (hX : X ⊆ T.carrier)
    (hno : ∀ ⦃y z : V⦄, y ∈ Y → z ∈ Z → ¬ G.Adj y z)
    (hobs : T.Obstructing G)
    (f₁ f₂ : V → C)
    (h₁ : (T.firstSide X Y Z).Extends G f₁)
    (h₂ : (T.secondSide X Z f₁).Extends G f₂) : False := by
  have h₁r := T.firstSide_extends_restrict G X Y Z f₁ h₁
  obtain ⟨h₂r, hagree⟩ :=
    T.secondSide_extends_restrict G X Y Z f₁ f₂ hX h₁ h₂
  exact hobs (T.glue_extensions G X Y Z hcover hno
    f₁ f₂ h₁r h₂r hagree)

/-- A vertex-minimal obstructing template cannot have a separator for which
one strict side carries at most k squared units of template degree. -/
theorem no_low_weight_separation (k : ℕ) (hk : 0 < k)
    (hT : T.Admissible G k) (hobs : T.Obstructing G)
    (hshort : ∀ v ∈ T.carrier \ T.precolored,
      (T.forbidden v).card < k)
    (hminimal : ∀ T' : ChromaticTemplate V C,
      T'.carrier.card < T.carrier.card →
      T'.Admissible G k → ∃ f : V → C, T'.Extends G f)
    (X Y Z : Finset V) (hcover : T.carrier = X ∪ Y ∪ Z)
    (hX : X.card < k) (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (hdisjZ : Disjoint Z (X ∪ Y))
    (hdisjY : Disjoint Y (X ∪ Z))
    (hno : ∀ ⦃y z : V⦄, y ∈ Y → z ∈ Z → ¬ G.Adj y z)
    (hlow : k * (T.precolored ∩ Z).card +
      (∑ v ∈ (T.carrier \ T.precolored) ∩ Z,
        (T.forbidden v).card) ≤ k ^ 2) : False := by
  classical
  have hXsub : X ⊆ T.carrier := by
    intro v hv
    rw [hcover]
    exact Finset.mem_union.mpr
      (Or.inl (Finset.mem_union.mpr (Or.inl hv)))
  have hdisjXZ : Disjoint X Z := by
    apply Finset.disjoint_left.mpr
    intro v hvX hvZ
    exact (Finset.disjoint_left.mp hdisjZ) hvZ
      (Finset.mem_union.mpr (Or.inl hvX))
  have hSZmul : k * (T.precolored ∩ Z).card ≤ k * k := by
    have hle : k * (T.precolored ∩ Z).card ≤ k ^ 2 :=
      (Nat.le_add_right _ _).trans hlow
    simpa [pow_two] using hle
  have hSZcard : (T.precolored ∩ Z).card ≤ k :=
    le_of_mul_le_mul_left hSZmul hk
  let T₁ := T.firstSide X Y Z
  have h₁card : T₁.carrier.card < T.carrier.card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro v hv
      exact (Finset.mem_inter.mp hv).1
    · intro heq
      obtain ⟨z, hz⟩ := hZ
      have hzC : z ∈ T.carrier := by
        rw [hcover]
        exact Finset.mem_union.mpr (Or.inr hz)
      have hzT₁ : z ∈ T₁.carrier := by rw [heq]; exact hzC
      exact (Finset.disjoint_left.mp hdisjZ) hz
        (Finset.mem_inter.mp hzT₁).2
  have h₁ad : T₁.Admissible G k :=
    T.firstSide_admissible G X Y Z k hT hshort
      (Nat.le_of_lt hX) hdisjZ hSZcard
  obtain ⟨f₁, hf₁⟩ := hminimal T₁ h₁card h₁ad
  let T₂ := T.secondSide X Z f₁
  have h₂card : T₂.carrier.card < T.carrier.card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro v hv
      exact (Finset.mem_inter.mp hv).1
    · intro heq
      obtain ⟨y, hy⟩ := hY
      have hyC : y ∈ T.carrier := by
        rw [hcover]
        exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_union.mpr (Or.inr hy)))
      have hyT₂ : y ∈ T₂.carrier := by rw [heq]; exact hyC
      exact (Finset.disjoint_left.mp hdisjY) hy
        (Finset.mem_inter.mp hyT₂).2
  have h₂ad : T₂.Admissible G k :=
    T.secondSide_admissible G X Y Z f₁ k hT
      (Nat.le_of_lt hX) hdisjXZ hlow hf₁
  obtain ⟨f₂, hf₂⟩ := hminimal T₂ h₂card h₂ad
  exact T.not_both_side_extensions G X Y Z hcover hXsub hno
    hobs f₁ f₂ hf₁ hf₂

/-- The extremal template admits no separator smaller than k with two
nonempty anticomplete strict sides. -/
theorem no_small_separation (k : ℕ) (hk : 0 < k)
    (hT : T.Admissible G k) (hobs : T.Obstructing G)
    (hshort : ∀ v ∈ T.carrier \ T.precolored,
      (T.forbidden v).card < k)
    (hminimal : ∀ T' : ChromaticTemplate V C,
      T'.carrier.card < T.carrier.card →
      T'.Admissible G k → ∃ f : V → C, T'.Extends G f)
    (X Y Z : Finset V) (hcover : T.carrier = X ∪ Y ∪ Z)
    (hX : X.card < k) (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (hdisjZ : Disjoint Z (X ∪ Y))
    (hdisjY : Disjoint Y (X ∪ Z))
    (hno : ∀ ⦃y z : V⦄, y ∈ Y → z ∈ Z → ¬ G.Adj y z) :
    False := by
  have hYZ : Disjoint Y Z := by
    apply Finset.disjoint_left.mpr
    intro v hvY hvZ
    exact (Finset.disjoint_left.mp hdisjY) hvY
      (Finset.mem_union.mpr (Or.inr hvZ))
  rcases T.one_side_low_degree k Y Z hT.2.1 hYZ with hlowY | hlowZ
  · have hcover' : T.carrier = X ∪ Z ∪ Y := by
      simpa only [Finset.union_assoc, Finset.union_comm, Finset.union_left_comm]
        using hcover
    have hno' : ∀ ⦃z y : V⦄, z ∈ Z → y ∈ Y → ¬ G.Adj z y := by
      intro z y hz hy hzy
      exact hno hy hz hzy.symm
    exact T.no_low_weight_separation G k hk hT hobs hshort
      hminimal X Z Y hcover' hX hZ hY hdisjY hdisjZ hno' hlowY
  · exact T.no_low_weight_separation G k hk hT hobs hshort
      hminimal X Y Z hcover hX hY hZ hdisjZ hdisjY hno hlowZ

/-- The unrestricted template on all vertices. -/
def empty (baseColor : C) : ChromaticTemplate V C where
  carrier := Finset.univ
  precolored := ∅
  precolored_subset := Finset.empty_subset _
  color := fun _ => baseColor
  forbidden := fun _ => ∅

theorem empty_admissible (baseColor : C) (k : ℕ) :
    (empty baseColor : ChromaticTemplate V C).Admissible G k := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro u v hu
    simp [empty] at hu
  · simp [degree, empty]
  · intro v hv
    simp [empty]

theorem empty_extends_iff_colorable {n : ℕ} (baseColor : Fin n) :
    (∃ f : V → Fin n, (empty baseColor).Extends G f) ↔ G.Colorable n := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨SimpleGraph.Coloring.mk f ?_⟩
    intro u v huv
    exact hf.1 (Finset.mem_univ u) (Finset.mem_univ v) huv
  · rintro ⟨f⟩
    refine ⟨f, ?_, ?_, ?_⟩
    · intro u v _ _ huv
      exact f.valid huv
    · intro v hv
      simp [empty] at hv
    · intro v hv
      simp [empty]

theorem empty_obstructing {n : ℕ} (baseColor : Fin n) (hn : ¬ G.Colorable n) :
    (empty baseColor).Obstructing G := by
  intro h
  exact hn ((empty_extends_iff_colorable G baseColor).mp h)

end ChromaticTemplate

/-- A finite family of weights below k whose total exceeds k contains a
subset of weight strictly between k and 2k. This is the chunk-cutting step
in the additive chromatic connectivity proof. -/
theorem exists_medium_weight_subset (S : Finset V) (w : V → ℕ) (k : ℕ)
    (hunit : ∀ v ∈ S, w v < k)
    (htotal : k < ∑ v ∈ S, w v) :
    ∃ B : Finset V, B ⊆ S ∧
      k < ∑ v ∈ B, w v ∧ ∑ v ∈ B, w v < 2 * k := by
  classical
  let Q : Finset (Finset V) :=
    Finset.univ.filter (fun B => B ⊆ S ∧ k < ∑ v ∈ B, w v)
  have hQ : Q.Nonempty := by
    refine ⟨S, ?_⟩
    simp [Q, htotal]
  obtain ⟨B, hBQ, hmin⟩ := Finset.exists_min_image Q Finset.card hQ
  have hBS : B ⊆ S := (Finset.mem_filter.mp hBQ).2.1
  have hBsum : k < ∑ v ∈ B, w v := (Finset.mem_filter.mp hBQ).2.2
  have hBnonempty : B.Nonempty := by
    by_contra h
    have hzero : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [hzero] at hBsum
  obtain ⟨b, hb⟩ := hBnonempty
  have herase : ∑ v ∈ B.erase b, w v ≤ k := by
    by_contra h
    have hsum : k < ∑ v ∈ B.erase b, w v := by omega
    have hmem : B.erase b ∈ Q := by
      simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(by intro x hx; exact hBS (Finset.mem_erase.mp hx).2), hsum⟩
    have hmin' := hmin (B.erase b) hmem
    exact (Finset.card_erase_lt_of_mem hb).not_ge hmin'
  have hbunit : w b < k := hunit b (hBS hb)
  have hsumEq : w b + ∑ v ∈ B.erase b, w v = ∑ v ∈ B, w v :=
    Finset.add_sum_erase B w hb
  refine ⟨B, hBS, hBsum, ?_⟩
  omega

/-- Heavy color-class chunks and a light remainder. -/
structure WeightedChunkPacking (S : Finset V) (w : V → ℕ)
    (color : V → Fin m) (k : ℕ) where
  chunks : Finset (Finset V)
  residual : Finset V
  chunks_subset : ∀ B ∈ chunks, B ⊆ S
  chunks_color : ∀ B ∈ chunks, ∃ a : Fin m, ∀ v ∈ B, color v = a
  chunks_weight : ∀ B ∈ chunks,
    k < ∑ v ∈ B, w v ∧ ∑ v ∈ B, w v < 2 * k
  chunks_disjoint : ∀ B ∈ chunks, ∀ D ∈ chunks, B ≠ D → Disjoint B D
  residual_subset : residual ⊆ S
  residual_disjoint : ∀ B ∈ chunks, Disjoint B residual
  cover : chunks.biUnion id ∪ residual = S
  residual_light : ∀ a : Fin m,
    (∑ v ∈ residual.filter (fun v => color v = a), w v) ≤ k
  charge : chunks.card * (k + 1) ≤ ∑ v ∈ S, w v

/-- Greedily extract medium-weight subsets from heavy color classes. -/
theorem exists_weighted_chunk_packing (w : V → ℕ)
    (color : V → Fin m) (k : ℕ) (S : Finset V)
    (hunit : ∀ v ∈ S, w v < k) :
    Nonempty (WeightedChunkPacking S w color k) := by
  classical
  suffices aux : ∀ S : Finset V, (∀ v ∈ S, w v < k) →
      Nonempty (WeightedChunkPacking S w color k) from aux S hunit
  intro S
  refine Finset.strongInductionOn S ?_
  intro S ih hunit
  by_cases hheavy : ∃ a : Fin m,
      k < ∑ v ∈ S.filter (fun v => color v = a), w v
  · obtain ⟨a, ha⟩ := hheavy
    let A := S.filter (fun v => color v = a)
    have hAunit : ∀ v ∈ A, w v < k := by
      intro v hv
      exact hunit v (Finset.mem_filter.mp hv).1
    obtain ⟨B, hBA, hBweight, hBupper⟩ :=
      exists_medium_weight_subset A w k hAunit ha
    have hBS : B ⊆ S :=
      hBA.trans (Finset.filter_subset _ _)
    have hBnonempty : B.Nonempty := by
      by_contra h
      have hzero : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simp [hzero] at hBweight
    let S' := S \ B
    have hS'sub : S' ⊆ S := Finset.sdiff_subset
    have hS'lt : S' ⊂ S := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hS'sub, ?_⟩
      intro heq
      obtain ⟨b, hb⟩ := hBnonempty
      have hbS' : b ∈ S' := heq ▸ hBS hb
      exact (Finset.mem_sdiff.mp hbS').2 hb
    have hS'unit : ∀ v ∈ S', w v < k := by
      intro v hv
      exact hunit v (hS'sub hv)
    obtain ⟨p⟩ := ih S' hS'lt hS'unit
    have hBdisjS' : Disjoint B S' := by
      apply Finset.disjoint_left.mpr
      intro v hvB hvS'
      exact (Finset.mem_sdiff.mp hvS').2 hvB
    have hBdisjChunk : ∀ D ∈ p.chunks, Disjoint B D := by
      intro D hD
      apply Finset.disjoint_left.mpr
      intro v hvB hvD
      exact (Finset.disjoint_left.mp hBdisjS') hvB
        (p.chunks_subset D hD hvD)
    have hBnot : B ∉ p.chunks := by
      intro hmem
      obtain ⟨b, hb⟩ := hBnonempty
      exact (Finset.disjoint_left.mp hBdisjS') hb
        (p.chunks_subset B hmem hb)
    have hsumSplit : (∑ v ∈ B, w v) +
        (∑ v ∈ S', w v) = ∑ v ∈ S, w v := by
      rw [← Finset.sum_union hBdisjS']
      exact congrArg (fun U : Finset V => ∑ v ∈ U, w v)
        (Finset.union_sdiff_of_subset hBS)
    refine ⟨{
      chunks := insert B p.chunks
      residual := p.residual
      chunks_subset := ?_
      chunks_color := ?_
      chunks_weight := ?_
      chunks_disjoint := ?_
      residual_subset := p.residual_subset.trans hS'sub
      residual_disjoint := ?_
      cover := ?_
      residual_light := p.residual_light
      charge := ?_
    }⟩
    · intro D hD
      rcases Finset.mem_insert.mp hD with rfl | hD
      · exact hBS
      · exact (p.chunks_subset D hD).trans hS'sub
    · intro D hD
      rcases Finset.mem_insert.mp hD with rfl | hD
      · refine ⟨a, ?_⟩
        intro v hv
        exact (Finset.mem_filter.mp (hBA hv)).2
      · exact p.chunks_color D hD
    · intro D hD
      rcases Finset.mem_insert.mp hD with rfl | hD
      · exact ⟨hBweight, hBupper⟩
      · exact p.chunks_weight D hD
    · intro D hD E hE hDE
      rcases Finset.mem_insert.mp hD with rfl | hD
      · rcases Finset.mem_insert.mp hE with rfl | hE
        · exact False.elim (hDE rfl)
        · exact hBdisjChunk E hE
      · rcases Finset.mem_insert.mp hE with rfl | hE
        · exact (hBdisjChunk D hD).symm
        · exact p.chunks_disjoint D hD E hE hDE
    · intro D hD
      rcases Finset.mem_insert.mp hD with rfl | hD
      · exact hBdisjS'.mono_right p.residual_subset
      · exact p.residual_disjoint D hD
    · rw [Finset.biUnion_insert]
      calc
        (B ∪ p.chunks.biUnion id) ∪ p.residual =
            B ∪ (p.chunks.biUnion id ∪ p.residual) := by
              rw [Finset.union_assoc]
        _ = B ∪ S' := by rw [p.cover]
        _ = S := Finset.union_sdiff_of_subset hBS
    · have hcard : (insert B p.chunks).card = p.chunks.card + 1 := by
        simp [hBnot]
      rw [hcard, Nat.add_mul]
      simp only [one_mul]
      have hweight : k + 1 ≤ ∑ v ∈ B, w v := by omega
      calc
        p.chunks.card * (k + 1) + (k + 1)
            ≤ (∑ v ∈ S', w v) + (∑ v ∈ B, w v) :=
              Nat.add_le_add p.charge hweight
        _ = ∑ v ∈ S, w v := by simpa [Nat.add_comm] using hsumSplit
  · refine ⟨{
      chunks := ∅
      residual := S
      chunks_subset := ?_
      chunks_color := ?_
      chunks_weight := ?_
      chunks_disjoint := ?_
      residual_subset := Finset.Subset.refl S
      residual_disjoint := ?_
      cover := ?_
      residual_light := ?_
      charge := ?_
    }⟩
    · intro B hB
      simp at hB
    · intro B hB
      simp at hB
    · intro B hB
      simp at hB
    · intro B hB
      simp at hB
    · intro B hB
      simp at hB
    · simp
    · intro a
      by_contra h
      have hweight : k < ∑ v ∈ S.filter (fun v => color v = a), w v := by omega
      exact hheavy ⟨a, hweight⟩
    · simp


namespace WeightedChunkPacking

variable {V : Type*} [DecidableEq V] {m : ℕ} {S : Finset V}
  {w : V → ℕ} {color : V → Fin m} {k : ℕ}

theorem card_le (p : WeightedChunkPacking S w color k)
    (hweight : (∑ v ∈ S, w v) ≤ 2 * k ^ 2) :
    p.chunks.card ≤ 2 * k := by
  nlinarith [p.charge]

end WeightedChunkPacking

namespace ChromaticTemplate

variable (G : SimpleGraph V) (T : ChromaticTemplate V C)

/-- Color independent chunks with distinct palette colors, avoiding all lists
inside each chunk and every color already used by the precoloring. -/
theorem extends_of_independent_chunks (base : C) (k : ℕ)
    {I : Type*} [Fintype I] [DecidableEq I]
    (B : I → Finset V)
    (hproper : T.ProperPrecoloring G)
    (hsub : ∀ i, B i ⊆ T.carrier \ T.precolored)
    (hcover : ∀ v ∈ T.carrier \ T.precolored, ∃ i, v ∈ B i)
    (hunique : ∀ i j v, v ∈ B i → v ∈ B j → i = j)
    (hindep : ∀ i u v, u ∈ B i → v ∈ B i → G.Adj u v → False)
    (hweight : ∀ i, (∑ v ∈ B i, (T.forbidden v).card) ≤ 2 * k)
    (hpalette : Fintype.card I + T.precolored.card + 2 * k ≤ Fintype.card C) :
    ∃ f : V → C, T.Extends G f := by
  classical
  let used : I → Finset C := fun i =>
    T.precolored.image T.color ∪ (B i).biUnion T.forbidden
  let L : I → Finset C := fun i => Finset.univ \ used i
  have hfree : ∀ i, Fintype.card I ≤ (L i).card := by
    intro i
    have hforb : ((B i).biUnion T.forbidden).card ≤ 2 * k :=
      (Finset.card_biUnion_le).trans (hweight i)
    have hused : (used i).card ≤ T.precolored.card + 2 * k := by
      exact (Finset.card_union_le _ _).trans
        (add_le_add Finset.card_image_le hforb)
    have hdecomp : Fintype.card C ≤ (L i).card + (used i).card := by
      simpa [L] using
        (Finset.card_le_card_sdiff_add_card
          (s := (Finset.univ : Finset C)) (t := used i))
    omega
  have hHall : ∀ s : Finset I, s.card ≤ (s.biUnion L).card := by
    intro s
    by_cases hs : s.Nonempty
    · obtain ⟨i, hi⟩ := hs
      calc
        s.card ≤ Fintype.card I := by
          simpa using Finset.card_le_card (Finset.subset_univ s)
        _ ≤ (L i).card := hfree i
        _ ≤ (s.biUnion L).card := by
          apply Finset.card_le_card
          intro c hc
          exact Finset.mem_biUnion.mpr ⟨i, hi, hc⟩
    · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      simp [hs0]
  obtain ⟨g, hginj, hgL⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' L).mp hHall
  let A := T.carrier \ T.precolored
  let idx (v : V) (hv : v ∈ A) : I := Classical.choose (hcover v hv)
  have hidx (v : V) (hv : v ∈ A) : v ∈ B (idx v hv) :=
    Classical.choose_spec (hcover v hv)
  let f : V → C := fun v =>
    if hs : v ∈ T.precolored then T.color v
    else if ha : v ∈ A then g (idx v ha) else base
  have hfS : ∀ v ∈ T.precolored, f v = T.color v := by
    intro v hv
    simp [f, hv]
  have hfA : ∀ (v : V) (hv : v ∈ A), f v = g (idx v hv) := by
    intro v hv
    have hvS : v ∉ T.precolored := (Finset.mem_sdiff.mp hv).2
    simp [f, hvS, hv]
  have hgavoid : ∀ i, g i ∉ T.precolored.image T.color ∧
      ∀ v ∈ B i, g i ∉ T.forbidden v := by
    intro i
    have hgi : g i ∉ used i := (Finset.mem_sdiff.mp (hgL i)).2
    refine ⟨?_, ?_⟩
    · intro h
      exact hgi (Finset.mem_union.mpr (Or.inl h))
    · intro v hv h
      exact hgi (Finset.mem_union.mpr
        (Or.inr (Finset.mem_biUnion.mpr ⟨v, hv, h⟩)))
  refine ⟨f, ?_, hfS, ?_⟩
  · intro u v hu hv huv
    by_cases huS : u ∈ T.precolored
    · by_cases hvS : v ∈ T.precolored
      · rw [hfS u huS, hfS v hvS]
        exact hproper huS hvS huv
      · have hvA : v ∈ A := Finset.mem_sdiff.mpr ⟨hv, hvS⟩
        rw [hfS u huS, hfA v hvA]
        intro heq
        have hmem : T.color u ∈ T.precolored.image T.color :=
          Finset.mem_image.mpr ⟨u, huS, rfl⟩
        exact (hgavoid (idx v hvA)).1 (heq.symm ▸ hmem)
    · have huA : u ∈ A := Finset.mem_sdiff.mpr ⟨hu, huS⟩
      by_cases hvS : v ∈ T.precolored
      · rw [hfA u huA, hfS v hvS]
        intro heq
        have hmem : T.color v ∈ T.precolored.image T.color :=
          Finset.mem_image.mpr ⟨v, hvS, rfl⟩
        exact (hgavoid (idx u huA)).1 (heq ▸ hmem)
      · have hvA : v ∈ A := Finset.mem_sdiff.mpr ⟨hv, hvS⟩
        rw [hfA u huA, hfA v hvA]
        intro heq
        have heqi : idx u huA = idx v hvA := hginj heq
        have huB : u ∈ B (idx u huA) := hidx u huA
        have hvB : v ∈ B (idx v hvA) := hidx v hvA
        exact hindep (idx u huA) u v huB (heqi ▸ hvB) huv
  · intro v hv
    rw [hfA v hv]
    exact (hgavoid (idx v hv)).2 v (hidx v hv)

end ChromaticTemplate

namespace ChromaticTemplate

variable (G : SimpleGraph V) (T : ChromaticTemplate V C)

/-- The quantitative recoloring step: a template with short lists extends
whenever the unprecolored graph uses at most palette-size minus six k colors. -/
theorem extends_of_colorable_remainder (base : C) (k m : ℕ) (hk : 0 < k)
    (ha : T.Admissible G k)
    (hshort : ∀ v ∈ T.carrier \ T.precolored,
      (T.forbidden v).card < k)
    (color : V → Fin m)
    (hcolor : ∀ ⦃u v : V⦄,
      u ∈ T.carrier \ T.precolored →
      v ∈ T.carrier \ T.precolored →
      G.Adj u v → color u ≠ color v)
    (hpalette : m + 6 * k ≤ Fintype.card C) :
    ∃ f : V → C, T.Extends G f := by
  classical
  let A := T.carrier \ T.precolored
  let w : V → ℕ := fun v => (T.forbidden v).card
  have hunit : ∀ v ∈ A, w v < k := hshort
  obtain ⟨p⟩ := exists_weighted_chunk_packing w color k A hunit
  have hsum : (∑ v ∈ A, w v) ≤ 2 * k ^ 2 := by
    exact (Nat.le_add_left _ _).trans ha.2.1
  have hpcount : p.chunks.card ≤ 2 * k := p.card_le hsum
  have hprecount : T.precolored.card ≤ 2 * k :=
    T.precolored_card_le G k hk ha
  let I := ({D : Finset V // D ∈ p.chunks} ⊕ Fin m)
  let B : I → Finset V := fun i =>
    match i with
    | Sum.inl D => D.1
    | Sum.inr a => p.residual.filter (fun v => color v = a)
  have hIsize : Fintype.card I = p.chunks.card + m := by
    simp [I]
  have hsub : ∀ i, B i ⊆ A := by
    intro i
    cases i with
    | inl D => exact p.chunks_subset D.1 D.2
    | inr a => exact (Finset.filter_subset _ _).trans p.residual_subset
  have hcover : ∀ v ∈ A, ∃ i, v ∈ B i := by
    intro v hv
    have hcov : v ∈ p.chunks.biUnion id ∪ p.residual := by
      rw [p.cover]
      exact hv
    rcases Finset.mem_union.mp hcov with hh | hr
    · obtain ⟨D, hD, hvD⟩ := Finset.mem_biUnion.mp hh
      exact ⟨Sum.inl ⟨D, hD⟩, hvD⟩
    · exact ⟨Sum.inr (color v), Finset.mem_filter.mpr ⟨hr, rfl⟩⟩
  have hunique : ∀ i j v, v ∈ B i → v ∈ B j → i = j := by
    intro i j v hvi hvj
    cases i with
    | inl D =>
      cases j with
      | inl E =>
        congr 1
        apply Subtype.ext
        by_contra hDE
        exact (Finset.disjoint_left.mp
          (p.chunks_disjoint D.1 D.2 E.1 E.2 hDE)) hvi hvj
      | inr a =>
        exact False.elim ((Finset.disjoint_left.mp
          (p.residual_disjoint D.1 D.2)) hvi (Finset.mem_filter.mp hvj).1)
    | inr a =>
      cases j with
      | inl D =>
        exact False.elim ((Finset.disjoint_left.mp
          (p.residual_disjoint D.1 D.2)) hvj (Finset.mem_filter.mp hvi).1)
      | inr b =>
        congr 1
        exact (Finset.mem_filter.mp hvi).2.symm.trans
          (Finset.mem_filter.mp hvj).2
  have hindep : ∀ i u v, u ∈ B i → v ∈ B i → G.Adj u v → False := by
    intro i u v hu hv huv
    have huA := hsub i hu
    have hvA := hsub i hv
    apply hcolor huA hvA huv
    cases i with
    | inl D =>
      obtain ⟨a, hD⟩ := p.chunks_color D.1 D.2
      exact (hD u hu).trans (hD v hv).symm
    | inr a =>
      exact (Finset.mem_filter.mp hu).2.trans
        (Finset.mem_filter.mp hv).2.symm
  have hweight : ∀ i, (∑ v ∈ B i, (T.forbidden v).card) ≤ 2 * k := by
    intro i
    cases i with
    | inl D =>
      change (∑ v ∈ D.1, w v) ≤ 2 * k
      exact (p.chunks_weight D.1 D.2).2.le
    | inr a =>
      have h := p.residual_light a
      dsimp [B, w] at h ⊢
      omega
  have hpalletteI : Fintype.card I + T.precolored.card + 2 * k ≤
      Fintype.card C := by
    rw [hIsize]
    omega
  exact T.extends_of_independent_chunks G base k B ha.1 hsub hcover
    hunique hindep hweight hpalletteI

end ChromaticTemplate
end HadwigerLean
