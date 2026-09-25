import HadwigerLean.Deduction.PublicStatements

/-! Translate an internal linear bound into a Mathlib-facing coloring theorem. -/

namespace HadwigerLean.Deduction

universe u

/-- The checked bridge from the internal minor/chromatic vocabulary to a
statement using only Mathlib coloring and expanded connected branch sets. -/
theorem linear_mathlib_of_internal
    (hlinear : ∃ C : ℕ,
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (t : ℕ),
        2 ≤ t → ¬ HasCliqueMinor G t → chromatic G ≤ C * t) :
    ∃ C : ℕ,
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (t : ℕ),
        2 ≤ t →
        (¬ ∃ B : Fin t → Set V,
          (∀ i, (G.induce (B i)).Connected) ∧
          (Pairwise fun i j => Disjoint (B i) (B j)) ∧
          (∀ i j : Fin t, i ≠ j →
            ∃ x ∈ B i, ∃ y ∈ B j, G.Adj x y)) →
        G.Colorable (C * t) := by
  obtain ⟨C, hC⟩ := hlinear
  refine ⟨C, ?_⟩
  intro V _ G t ht hnot
  have hminor : ¬ HasCliqueMinor G t := by
    simpa only [hasCliqueMinor_iff_branchSets] using hnot
  exact (chromatic_le_iff_colorable G (C * t)).mp
    (hC V G t ht hminor)

end HadwigerLean.Deduction
