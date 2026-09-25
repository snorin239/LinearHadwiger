import HadwigerLean.Deduction.Theorem1
import HadwigerLean.Bootstrap.Step
import HadwigerLean.Deduction.PublicLinearBridge

/-! Final deduction with its remaining graph lemma made explicit. -/

namespace HadwigerLean.Deduction

open HadwigerLean.Bootstrap

universe u

/-- The full deduction, currently conditional on the path-localization lemma
as well as the two named paper inputs. -/
theorem linear_of_theorem4_corollary24_of_path
    (h4 : Theorem4Statement.{u})
    (h24 : Corollary24Statement.{u})
    (hpath : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) (k q : ℕ), PathLocalizationStatement H k q) :
    ∃ C : ℕ,
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (t : ℕ),
        2 ≤ t → ¬ HadwigerLean.HasCliqueMinor G t →
        HadwigerLean.chromatic G ≤ C * t := by
  exact linear_of_bootstrap h4
    (fun α hα hlocal => local_linear_bound_step_of_path h24 hpath α hα hlocal)

/-- Mathlib-facing form of the same conditional result. -/
theorem linear_mathlib_of_theorem4_corollary24_of_path
    (h4 : Theorem4Statement.{u})
    (h24 : Corollary24Statement.{u})
    (hpath : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) (k q : ℕ), PathLocalizationStatement H k q) :
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
    (linear_of_theorem4_corollary24_of_path h4 h24 hpath)

end HadwigerLean.Deduction
