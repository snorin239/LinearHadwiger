import HadwigerLean.Graph.Finite
import HadwigerLean.Graph.Minor
import Mathlib.Tactic

/-!
# Removing stable sets

A stable set can be assigned one fresh color while the remaining induced
subgraph keeps its coloring. This is the local step for the final peeling
argument in Theorem 2.
-/

namespace HadwigerLean

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertices remaining after deleting a finite set. -/
def remainingSet (s : Finset V) : Set V := {v | v ∉ s}

noncomputable instance remainingSetFintype (s : Finset V) :
    Fintype (remainingSet s) := by
  classical
  infer_instance

omit [Fintype V] in
/-- One stable set costs at most one color. -/
theorem colorable_delete_stable_set (G : SimpleGraph V)
    (s : Finset V) (hs : G.IsIndepSet (s : Set V))
    (k : ℕ) (hc : (G.induce (remainingSet s)).Colorable k) :
    G.Colorable (k + 1) := by
  classical
  let C : (G.induce (remainingSet s)).Coloring (Fin k) :=
    Classical.choice hc
  let f : V → Fin (k + 1) := fun v =>
    if hv : v ∈ s then 0 else (C ⟨v, hv⟩).succ
  have hproper : ∀ {v w : V}, G.Adj v w → f v ≠ f w := by
    intro v w hadj
    by_cases hv : v ∈ s
    · by_cases hw : w ∈ s
      · exact False.elim (hs hv hw (G.ne_of_adj hadj) hadj)
      · simpa [f, hv, hw] using
          (Fin.succ_ne_zero (C ⟨w, hw⟩)).symm
    · by_cases hw : w ∈ s
      · simp [f, hv, hw]
      · have hC : C ⟨v, hv⟩ ≠ C ⟨w, hw⟩ := C.valid hadj
        intro h
        apply hC
        exact Fin.succ_injective k (by simpa [f, hv, hw] using h)
  exact ⟨SimpleGraph.Coloring.mk f hproper⟩

theorem chromatic_le_delete_stable_set (G : SimpleGraph V)
    (s : Finset V) (hs : G.IsIndepSet (s : Set V)) :
    chromatic G ≤ chromatic (G.induce (remainingSet s)) + 1 := by
  apply (chromatic_le_iff_colorable G _).2
  exact colorable_delete_stable_set G s hs _
    (colorable_chromatic (G.induce (remainingSet s)))


omit [Fintype V] [DecidableEq V] in
/-- A residual coloring plus one fresh color per stable covering block
colors the whole graph. Blocks may overlap; the chosen block for each vertex
is enough for properness. -/
theorem colorable_of_stable_cover (G : SimpleGraph V)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Set V) (block : ι → Finset V)
    (hstable : ∀ i, G.IsIndepSet (block i : Set V))
    (hcover : ∀ v, v ∉ J → ∃ i, v ∈ block i)
    (k : ℕ) (hc : (G.induce J).Colorable k) :
    G.Colorable (Fintype.card ι + k) := by
  classical
  let C : (G.induce J).Coloring (Fin k) := Classical.choice hc
  let chooseBlock (v : V) (hv : v ∉ J) : ι :=
    Classical.choose (hcover v hv)
  have hmem (v : V) (hv : v ∉ J) :
      v ∈ block (chooseBlock v hv) :=
    Classical.choose_spec (hcover v hv)
  let f : V → ι ⊕ Fin k := fun v =>
    if hv : v ∈ J then Sum.inr (C ⟨v, hv⟩)
    else Sum.inl (chooseBlock v hv)
  have hproper : ∀ {v w : V}, G.Adj v w → f v ≠ f w := by
    intro v w hadj
    by_cases hv : v ∈ J
    · by_cases hw : w ∈ J
      · simpa [f, hv, hw] using
          (C.valid hadj : C ⟨v, hv⟩ ≠ C ⟨w, hw⟩)
      · simp [f, hv, hw]
    · by_cases hw : w ∈ J
      · simp [f, hv, hw]
      · intro heq
        have hsame : chooseBlock v hv = chooseBlock w hw := by
          simpa [f, hv, hw] using heq
        have hvmem := hmem v hv
        have hwmem := hmem w hw
        rw [← hsame] at hwmem
        exact (hstable (chooseBlock v hv)) hvmem hwmem
          (G.ne_of_adj hadj) hadj
  have hc' : G.Colorable (Fintype.card (ι ⊕ Fin k)) :=
    (SimpleGraph.Coloring.mk f hproper).colorable
  simpa using hc'

/-- A finite family of pairwise disjoint stable sets, each of size m+1. -/
def IsStablePacking (G : SimpleGraph V) (m : ℕ)
    (P : Finset (Finset V)) : Prop :=
  (∀ s ∈ P, s.card = m + 1 ∧ G.IsIndepSet (s : Set V)) ∧
  ∀ s ∈ P, ∀ t ∈ P, s ≠ t → Disjoint s t

/-- Vertices left after deleting the blocks of a packing. -/
def packingRemainder (P : Finset (Finset V)) : Finset V :=
  (Finset.univ : Finset V) \ (P.biUnion id)

noncomputable def allStablePackings (G : SimpleGraph V) (m : ℕ) :
    Finset (Finset (Finset V)) := by
  classical
  exact Finset.univ.filter (IsStablePacking G m)

/-- A maximum-cardinality packing leaves no stable set of size m+1. -/
theorem exists_maximal_stable_packing (G : SimpleGraph V) (m : ℕ) :
    ∃ P : Finset (Finset V),
      IsStablePacking G m P ∧
      ∀ s : Finset V,
        s.card = m + 1 →
        G.IsIndepSet (s : Set V) →
        s ⊆ packingRemainder P →
        False := by
  classical
  have hempty : IsStablePacking G m ∅ := by
    simp [IsStablePacking]
  have hnonempty : (allStablePackings G m).Nonempty := by
    refine ⟨∅, ?_⟩
    simp [allStablePackings, hempty]
  obtain ⟨P, hPmem, hmax⟩ :=
    (allStablePackings G m).exists_max_image Finset.card hnonempty
  have hP : IsStablePacking G m P := by
    simpa [allStablePackings] using hPmem
  refine ⟨P, hP, ?_⟩
  intro s hcard hstable hsubset
  have hdisj (t : Finset V) (ht : t ∈ P) : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro v hvs hvt
    have hvR := hsubset hvs
    have hvU : v ∈ P.biUnion id :=
      Finset.mem_biUnion.mpr ⟨t, ht, hvt⟩
    exact (Finset.mem_sdiff.mp hvR).2 hvU
  have hnot : s ∉ P := by
    intro hs
    have hpos : 0 < s.card := by omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    exact (Finset.disjoint_left.mp (hdisj s hs)) hv hv
  have hnew : IsStablePacking G m (insert s P) := by
    constructor
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | htP
      · exact ⟨hcard, hstable⟩
      · exact hP.1 t htP
    · intro t ht u hu htu
      rcases Finset.mem_insert.mp ht with rfl | htP
      · rcases Finset.mem_insert.mp hu with rfl | huP
        · exact False.elim (htu rfl)
        · exact hdisj u huP
      · rcases Finset.mem_insert.mp hu with rfl | huP
        · exact (hdisj t htP).symm
        · exact hP.2 t htP u huP htu
  have hnewmem : insert s P ∈ allStablePackings G m := by
    simpa [allStablePackings] using hnew
  have hmax' := hmax (insert s P) hnewmem
  rw [Finset.card_insert_of_notMem hnot] at hmax'
  omega

/-- The number of removed blocks is bounded by n/(m+1), without introducing
a floor into the statement. -/
theorem stablePacking_count_bound (G : SimpleGraph V) (m : ℕ)
    (P : Finset (Finset V)) (hP : IsStablePacking G m P) :
    P.card * (m + 1) ≤ Fintype.card V := by
  classical
  have hdisj : (P : Set (Finset V)).PairwiseDisjoint id := by
    intro s hs t ht hne
    exact hP.2 s hs t ht hne
  have hcount : (P.biUnion id).card = P.card * (m + 1) := by
    calc
      (P.biUnion id).card = ∑ s ∈ P, s.card :=
        Finset.card_biUnion hdisj
      _ = ∑ _s ∈ P, (m + 1) := by
        apply Finset.sum_congr rfl
        intro s hs
        exact (hP.1 s hs).1
      _ = P.card * (m + 1) := by simp
  rw [← hcount]
  exact Finset.card_le_card (Finset.subset_univ _)

/-- If the remainder contains no stable set of size m+1, its induced
graph has independence number at most m. -/
theorem independenceNumber_remainder_le (G : SimpleGraph V) (m : ℕ)
    (P : Finset (Finset V))
    (hmax : ∀ s : Finset V,
      s.card = m + 1 →
      G.IsIndepSet (s : Set V) →
      s ⊆ packingRemainder P →
      False) :
    independenceNumber
      (G.induce (packingRemainder P : Set V)) ≤ m := by
  classical
  let J : Set V := packingRemainder P
  let H := G.induce J
  by_contra hnot
  change ¬ independenceNumber H ≤ m at hnot
  have hlarge : m + 1 ≤ independenceNumber H := by omega
  obtain ⟨t, htind, htcard⟩ :=
    exists_stable_card_eq_independenceNumber H
  have htlarge : m + 1 ≤ t.card := by omega
  obtain ⟨u, hut, hucard⟩ :=
    Finset.exists_subset_card_eq htlarge
  let s : Finset V := u.image Subtype.val
  have hscard : s.card = m + 1 := by
    rw [show s.card = u.card by
      exact Finset.card_image_of_injective u Subtype.val_injective]
    exact hucard
  have hsJ : s ⊆ packingRemainder P := by
    intro v hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact w.property
  have hsG : G.IsIndepSet (s : Set V) := by
    intro v hv w hw hvw hadj
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hw
    have hvw' : v' ≠ w' := by
      intro heq
      exact hvw (congrArg Subtype.val heq)
    exact htind (hut hv') (hut hw') hvw' hadj
  exact hmax s hscard hsG hsJ


/-- A stable packing plus an induced-remainder coloring colors the whole
graph with one additional color for each removed block. -/
theorem chromatic_le_packing_remainder (G : SimpleGraph V) (m : ℕ)
    (P : Finset (Finset V)) (hP : IsStablePacking G m P) :
    chromatic G ≤ P.card +
      chromatic (G.induce (packingRemainder P : Set V)) := by
  classical
  let J : Set V := packingRemainder P
  let Block := {s : Finset V // s ∈ P}
  have hstable (s : Block) : G.IsIndepSet (s.1 : Set V) :=
    (hP.1 s.1 s.2).2
  have hcover (v : V) (hv : v ∉ J) : ∃ s : Block, v ∈ s.1 := by
    have hvU : v ∈ P.biUnion id := by
      by_contra hvU
      have hvR : v ∈ packingRemainder P :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvU⟩
      exact hv hvR
    obtain ⟨s, hs, hvs⟩ := Finset.mem_biUnion.mp hvU
    exact ⟨⟨s, hs⟩, hvs⟩
  have hc : G.Colorable (Fintype.card Block +
      chromatic (G.induce J)) :=
    colorable_of_stable_cover G J
      (fun s : Block => s.1) hstable hcover
      (chromatic (G.induce J))
      (colorable_chromatic (G.induce J))
  have hc' : G.Colorable (P.card +
      chromatic (G.induce (packingRemainder P : Set V))) := by
    simpa [Block, J] using hc
  exact (chromatic_le_iff_colorable G _).2 hc'

/-- The complete structural peeling lemma. The quantitative proof only
needs to bound the number of removed blocks and analyze the residual graph. -/
theorem exists_stable_peeling (G : SimpleGraph V) (m : ℕ) :
    ∃ P : Finset (Finset V),
      IsStablePacking G m P ∧
      P.card * (m + 1) ≤ Fintype.card V ∧
      independenceNumber
        (G.induce (packingRemainder P : Set V)) ≤ m ∧
      chromatic G ≤ P.card +
        chromatic (G.induce (packingRemainder P : Set V)) := by
  obtain ⟨P, hP, hmax⟩ := exists_maximal_stable_packing G m
  exact ⟨P, hP,
    stablePacking_count_bound G m P hP,
    independenceNumber_remainder_le G m P hmax,
    chromatic_le_packing_remainder G m P hP⟩

/-- Generic final reduction: a bound for all induced residual graphs with
independence number at most m extends to every graph, at the cost εn/2.
Only the real inequality 2/ε ≤ m+1 is needed. -/
theorem chromatic_bound_of_bounded_induced
    (G : SimpleGraph V) (m : ℕ) (ε B : ℝ)
    (hε : 0 < ε)
    (hm : 2 / ε ≤ (m + 1 : ℕ))
    (hsmall : ∀ J : Finset V,
      independenceNumber (G.induce (J : Set V)) ≤ m →
      (chromatic (G.induce (J : Set V)) : ℝ) ≤
        4 * (cliqueMinorNumber (G.induce (J : Set V)) : ℝ) +
          ε * (J.card : ℝ) / 2 + B) :
    (chromatic G : ℝ) ≤
      4 * (cliqueMinorNumber G : ℝ) +
        ε * (Fintype.card V : ℝ) + B := by
  classical
  obtain ⟨P, hP, hcount, hα, hcolor⟩ :=
    exists_stable_peeling G m
  let J := packingRemainder P
  have hPcount :
      (P.card : ℝ) * (m + 1 : ℕ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast hcount
  have hPlow :
      (P.card : ℝ) * (2 / ε) ≤ (Fintype.card V : ℝ) :=
    (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg P.card)).trans hPcount
  have hscaled :
      ((P.card : ℝ) * (2 / ε)) * ε ≤
        (Fintype.card V : ℝ) * ε :=
    mul_le_mul_of_nonneg_right hPlow hε.le
  have hleft :
      ((P.card : ℝ) * (2 / ε)) * ε = 2 * (P.card : ℝ) := by
    field_simp
  rw [hleft] at hscaled
  have hPbound :
      (P.card : ℝ) ≤ ε * (Fintype.card V : ℝ) / 2 := by
    nlinarith
  have hJcard : (J.card : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.subset_univ J)
  have hJscale :
      ε * (J.card : ℝ) ≤ ε * (Fintype.card V : ℝ) :=
    mul_le_mul_of_nonneg_left hJcard hε.le
  have hminor :
      (cliqueMinorNumber (G.induce (J : Set V)) : ℝ) ≤
        (cliqueMinorNumber G : ℝ) := by
    exact_mod_cast cliqueMinorNumber_induce G (J : Set V)
  have hsmallJ := hsmall J hα
  have hcolorR :
      (chromatic G : ℝ) ≤ (P.card : ℝ) +
        (chromatic (G.induce (J : Set V)) : ℝ) := by
    exact_mod_cast hcolor
  nlinarith
end HadwigerLean