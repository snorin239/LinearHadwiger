import HadwigerLean.Graph.MinorFree
import HadwigerLean.Quantitative.Theorem2FinalBridge

/-!
# Mathlib-facing quantitative bound

Theorem 2 is stated here with Mathlib's `chromaticNumber`, an expanded
branch-set exclusion, and the explicit real-valued additive term.
-/

namespace HadwigerLean.Deduction

universe u

/-- Theorem 2 in Mathlib graph terminology, parameterized by any excluded
complete-minor order `h + 1`. -/
theorem quantitative_bound_mathlib
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h : ℕ)
    (hminor : ¬ ∃ B : Fin (h + 1) → Set V,
      (∀ i, (G.induce (B i)).Connected) ∧
      (Pairwise fun i j => Disjoint (B i) (B j)) ∧
      (∀ i j : Fin (h + 1), i ≠ j →
        ∃ x ∈ B i, ∃ y ∈ B j, G.Adj x y)) :
    (ENat.toNat G.chromaticNumber : ℝ) ≤
      4 * (h : ℝ) + ε * (Fintype.card V : ℝ) +
        (100 / ε) ^ (2000 / ε ^ 2) := by
  classical
  have hnot : ¬ HasCliqueMinor G (h + 1) := by
    simpa only [hasCliqueMinor_iff_branchSets] using hminor
  have hnum : cliqueMinorNumber G ≤ h := by
    have := (not_hasCliqueMinor_iff_cliqueMinorNumber_lt G (h + 1)).mp hnot
    omega
  have hbound := Theorem2.quantitative_bound G ε hε hε1
  change (ENat.toNat G.chromaticNumber : ℝ) ≤
    4 * (cliqueMinorNumber G : ℝ) + ε * (Fintype.card V : ℝ) +
      (100 / ε) ^ (2000 / ε ^ 2) at hbound
  have hnumR : (cliqueMinorNumber G : ℝ) ≤ (h : ℝ) := by exact_mod_cast hnum
  linarith

/-- Setting `h` to the actual complete-minor number gives the exact
quantitative inequality from the paper. -/
theorem quantitative_bound_mathlib_at_minor_number
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (ENat.toNat G.chromaticNumber : ℝ) ≤
      4 * (cliqueMinorNumber G : ℝ) + ε * (Fintype.card V : ℝ) +
        (100 / ε) ^ (2000 / ε ^ 2) := by
  classical
  apply quantitative_bound_mathlib G ε hε hε1 (cliqueMinorNumber G)
  rw [← hasCliqueMinor_iff_branchSets]
  exact (not_hasCliqueMinor_iff_cliqueMinorNumber_lt G _).mpr (Nat.lt_succ_self _)

end HadwigerLean.Deduction
