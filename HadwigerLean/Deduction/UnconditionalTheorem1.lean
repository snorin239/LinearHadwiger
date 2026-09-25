import HadwigerLean.Deduction.Theorem4Proof
import HadwigerLean.Deduction.Corollary24Complete
import HadwigerLean.Deduction.ConditionalTheorem1

/-! The unconditional Theorem 1 endpoints obtained from the checked
Theorem 4 and Corollary 24. -/

namespace HadwigerLean.Deduction

universe u

/-- Paper Theorem 1: graphs without a `K_t` minor have chromatic number
at most a universal constant times `t`. -/
theorem theorem1_proved :
    ∃ C : ℕ,
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (t : ℕ),
        2 ≤ t → ¬ HadwigerLean.HasCliqueMinor G t →
        HadwigerLean.chromatic G ≤ C * t :=
  linear_of_theorem4_corollary24 theorem4_proved corollary24_proved

/-- Theorem 1 expressed using an explicit branch-set obstruction and
Mathlib's `SimpleGraph.Colorable` conclusion. -/
theorem theorem1_mathlib_proved :
    ∃ C : ℕ,
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (t : ℕ),
        2 ≤ t →
        (¬ ∃ B : Fin t → Set V,
          (∀ i, (G.induce (B i)).Connected) ∧
          (Pairwise fun i j => Disjoint (B i) (B j)) ∧
          (∀ i j : Fin t, i ≠ j →
            ∃ x ∈ B i, ∃ y ∈ B j, G.Adj x y)) →
        G.Colorable (C * t) :=
  linear_mathlib_of_theorem4_corollary24 theorem4_proved corollary24_proved

end HadwigerLean.Deduction
