import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Finite graph parameters

The paper uses natural-valued chromatic and independence numbers, with value
zero on the empty graph. Mathlib's `SimpleGraph.chromaticNumber` takes values in
`ℕ∞`; on finite vertex types its `ENat.toNat` is the ordinary chromatic number.
We retain Mathlib's independent-set predicate and enumerate the stable finsets
for later finite linear programs.
-/

namespace HadwigerLean

variable {V : Type*} [Fintype V]

/-- The number of vertices of a graph with finite vertex type. -/
def graphOrder (_G : SimpleGraph V) : ℕ := Fintype.card V

/-- The natural-valued chromatic number of a finite graph. -/
noncomputable def chromatic (G : SimpleGraph V) : ℕ :=
  ENat.toNat G.chromaticNumber

/-- The independence number of a finite graph. -/
noncomputable def independenceNumber (G : SimpleGraph V) : ℕ :=
  G.indepNum

/-- The finite family of stable vertex sets, including the empty set. -/
noncomputable def stableFinsets (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (fun s => G.IsIndepSet (s : Set V))

@[simp] theorem graphOrder_eq (G : SimpleGraph V) : graphOrder G = Fintype.card V := rfl

omit [Fintype V] in
theorem chromatic_eq_toNat (G : SimpleGraph V) :
    chromatic G = ENat.toNat G.chromaticNumber := rfl

theorem chromatic_le_iff_colorable (G : SimpleGraph V) (n : ℕ) :
    chromatic G ≤ n ↔ G.Colorable n := by
  rw [chromatic]
  have h : G.chromaticNumber ≠ ⊤ := by
    exact (G.colorable_of_fintype.chromaticNumber_le.trans_lt (ENat.coe_lt_top _)).ne
  rw [← SimpleGraph.chromaticNumber_le_iff_colorable]
  constructor
  · intro hc
    calc
      G.chromaticNumber = (ENat.toNat G.chromaticNumber : ℕ∞) := (ENat.coe_toNat h).symm
      _ ≤ n := by exact_mod_cast hc
  · exact ENat.toNat_le_of_le_coe

theorem colorable_chromatic (G : SimpleGraph V) : G.Colorable (chromatic G) := by
  simpa only [chromatic] using G.colorable_chromaticNumber_of_fintype

theorem chromatic_le_card (G : SimpleGraph V) : chromatic G ≤ Fintype.card V :=
  (chromatic_le_iff_colorable G _).2 G.colorable_of_fintype

theorem chromatic_eq_zero_iff (G : SimpleGraph V) :
    chromatic G = 0 ↔ IsEmpty V := by
  constructor
  · intro h
    exact SimpleGraph.colorable_zero_iff.mp
      ((chromatic_le_iff_colorable G 0).mp (Nat.le_zero.mpr h))
  · intro h
    apply Nat.eq_zero_of_le_zero
    exact (chromatic_le_iff_colorable G 0).mpr
      (SimpleGraph.colorable_zero_iff.mpr h)

theorem chromatic_mono {G H : SimpleGraph V} (h : G ≤ H) :
    chromatic G ≤ chromatic H := by
  apply (chromatic_le_iff_colorable G _).2
  exact (colorable_chromatic H).mono_left h

@[simp] theorem mem_stableFinsets (G : SimpleGraph V) (s : Finset V) :
    s ∈ stableFinsets G ↔ G.IsIndepSet (s : Set V) := by
  classical
  simp [stableFinsets]

theorem stableFinsets_mono {G H : SimpleGraph V} (h : G ≤ H) :
    stableFinsets H ⊆ stableFinsets G := by
  intro s hs
  rw [mem_stableFinsets] at hs ⊢
  intro v hv w hw hvw hadj
  exact hs hv hw hvw (h hadj)

theorem stableFinsets_downward (G : SimpleGraph V) {s t : Finset V}
    (hts : t ⊆ s) (hs : s ∈ stableFinsets G) : t ∈ stableFinsets G := by
  rw [mem_stableFinsets] at hs ⊢
  intro v hv w hw hvw
  exact hs (hts hv) (hts hw) hvw

theorem stable_card_le_independenceNumber (G : SimpleGraph V) {s : Finset V}
    (hs : G.IsIndepSet (s : Set V)) : s.card ≤ independenceNumber G := by
  exact hs.card_le_indepNum

omit [Fintype V] in
theorem exists_stable_card_eq_independenceNumber (G : SimpleGraph V) :
    ∃ s : Finset V, G.IsIndepSet (s : Set V) ∧ s.card = independenceNumber G := by
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  exact ⟨s, hs.isIndepSet, hs.card_eq⟩

theorem independenceNumber_le_card (G : SimpleGraph V) :
    independenceNumber G ≤ Fintype.card V := by
  classical
  obtain ⟨s, _, hs⟩ := exists_stable_card_eq_independenceNumber G
  rw [← hs]
  simpa using Finset.card_le_card (Finset.subset_univ s)

theorem independenceNumber_antitone {G H : SimpleGraph V} (h : G ≤ H) :
    independenceNumber H ≤ independenceNumber G := by
  obtain ⟨s, hs, hcard⟩ := exists_stable_card_eq_independenceNumber H
  rw [← hcard]
  exact stable_card_le_independenceNumber G
    ((mem_stableFinsets G s).mp
      (stableFinsets_mono h ((mem_stableFinsets H s).mpr hs)))

end HadwigerLean
