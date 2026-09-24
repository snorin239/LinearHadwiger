import HadwigerLean.Coloring.FractionalLP
import HadwigerLean.Graph.Minor

/-!
# From weighted stable sets to the Reed--Seymour fractional bound

The combinatorial part of Reed and Seymour's argument constructs a stable set
carrying at least `1 / (2 h(G))` of every nonnegative vertex weight. This file
isolates the final use of fractional-coloring LP duality. The hypothesis of the
main theorem is an explicit weighted stable-set assertion, not an axiom.
-/

namespace HadwigerLean

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A weighted stable-set bound implies the fractional Reed--Seymour bound.
The combinatorial bound is supplied as a hypothesis here; the egg-decomposition
modules will prove it. -/
theorem fractionalChromaticNumber_le_twice_cliqueMinorNumber_of_weighted
    (G : SimpleGraph V)
    (hweighted : ∀ w : V → ℝ, (∀ v, 0 ≤ w v) →
      ∃ s : Finset V, G.IsIndepSet (s : Set V) ∧
        (∑ v, w v) ≤ 2 * (cliqueMinorNumber G : ℝ) * ∑ v ∈ s, w v) :
    fractionalChromaticNumber G ≤ 2 * (cliqueMinorNumber G : ℝ) := by
  classical
  obtain ⟨w, hw, hopt⟩ := exists_fractionalDual_optimum G
  obtain ⟨s, hs, hbound⟩ := hweighted w hw.1
  have hstable : (∑ v ∈ s, w v) ≤ 1 := by
    by_cases hne : s.Nonempty
    · let S : StableSet G := ⟨s, hne, hs⟩
      exact hw.2 S
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp
  have hfactor : (0 : ℝ) ≤ 2 * (cliqueMinorNumber G : ℝ) := by positivity
  calc
    fractionalChromaticNumber G = fractionalDualValue w := hopt.symm
    _ = ∑ v, w v := rfl
    _ ≤ 2 * (cliqueMinorNumber G : ℝ) * ∑ v ∈ s, w v := hbound
    _ ≤ 2 * (cliqueMinorNumber G : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hstable hfactor
    _ = 2 * (cliqueMinorNumber G : ℝ) := by ring

end HadwigerLean
