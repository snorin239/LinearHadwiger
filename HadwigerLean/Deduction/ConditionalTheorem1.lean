import HadwigerLean.Deduction.Theorem1FromPath

/-!
# Theorem 1 conditional on the two named paper inputs

The path-localization premise of the intermediate deduction is discharged by
the checked graph lemma. Only Theorem 4 and Corollary 24 remain as explicit
hypotheses.
-/

namespace HadwigerLean.Deduction

open HadwigerLean.Bootstrap

universe u

/-- Paper Theorem 1 from paper Theorem 4 and Corollary 24. -/
theorem linear_of_theorem4_corollary24
    (h4 : Theorem4Statement.{u})
    (h24 : Corollary24Statement.{u}) :
    ∃ C : ℕ,
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (t : ℕ),
        2 ≤ t → ¬ HadwigerLean.HasCliqueMinor G t →
        HadwigerLean.chromatic G ≤ C * t := by
  exact linear_of_theorem4_corollary24_of_path h4 h24
    (fun W _ _ H k q => path_localization H k q)

/-- Mathlib-facing form with an expanded branch-set hypothesis and a
`SimpleGraph.Colorable` conclusion. -/
theorem linear_mathlib_of_theorem4_corollary24
    (h4 : Theorem4Statement.{u})
    (h24 : Corollary24Statement.{u}) :
    ∃ C : ℕ,
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (t : ℕ),
        2 ≤ t →
        (¬ ∃ B : Fin t → Set V,
          (∀ i, (G.induce (B i)).Connected) ∧
          (Pairwise fun i j => Disjoint (B i) (B j)) ∧
          (∀ i j : Fin t, i ≠ j →
            ∃ x ∈ B i, ∃ y ∈ B j, G.Adj x y)) →
        G.Colorable (C * t) := by
  exact linear_mathlib_of_internal
    (linear_of_theorem4_corollary24 h4 h24)

end HadwigerLean.Deduction
