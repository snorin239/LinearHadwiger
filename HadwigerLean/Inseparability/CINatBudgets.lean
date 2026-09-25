import HadwigerLean.Inseparability.CICoreBudgets
import Mathlib.Tactic

/-!
# Linear connectivity and chromatic budgets for CI

Once `r*x ≤ 3t` and `x ≤ t`, the fixed large coefficients pay for
every graph-theoretic cost in one stage. The local-window estimate is
handled separately because it uses logarithms.
-/

namespace HadwigerLean.Inseparability

def ciConnectivity (t : ℕ) : ℕ := 18000000 * t
def ciPieceConnectivity (t : ℕ) : ℕ := 9000000 * t
def ciCoefficient : ℕ := 943718400000000
def ciChromaticBudget (t s : ℕ) : ℕ := ciCoefficient * t * (1 + s)
def ciLocalChromatic (t s : ℕ) : ℕ := t * s

theorem ci_linear_stage_budgets
    (t s r x χ : ℕ)
    (ht : 3 ≤ t) (hx : x ≤ t) (hrx : r * x ≤ 3 * t)
    (hχ : 2 * ciChromaticBudget t s ≤ χ) :
    (r * x + ciPieceConnectivity t ≤ ciConnectivity t) ∧
    (ciLocalChromatic t s +
      2 * (480 * 6400 * ciPieceConnectivity t) +
      ciChromaticBudget t s / 2 + r * x < χ) ∧
    (ciChromaticBudget t s / 2 + r * x +
      ciLocalChromatic t s + 4 * (3 * r * x) +
      7 * ciConnectivity t ≤ χ) ∧
    (ciChromaticBudget t s / 2 + r * x +
      ciLocalChromatic t s + 4 * (3 * r * x) +
      6 * ciConnectivity t ≤ ciChromaticBudget t s) ∧
    (3 * (3 * r * x) ≤ ciConnectivity t) ∧
    (2 * (3 * r * x) ≤ ciPieceConnectivity t) ∧
    (3 * r * x + 2 * (r * x) ≤ ciConnectivity t) ∧
    (2 * (r * x) ≤ ciConnectivity t) ∧
    (2 * (r * x) ≤ ciPieceConnectivity t) ∧
    (2 * x ≤ ciPieceConnectivity t) ∧
    (33 * ((4 * r + 1) * x) ≤ ciPieceConnectivity t) ∧
    (12 * ciConnectivity t ≤ ciChromaticBudget t s) ∧
    (ciLocalChromatic t s + 2 * (r * x) +
      7 * ciConnectivity t ≤ χ) ∧
    (ciLocalChromatic t s + 2 * (r * x) +
      6 * ciConnectivity t ≤ ciChromaticBudget t s / 2) ∧
    (ciChromaticBudget t s / 2 + ciConnectivity t ≤
      ciChromaticBudget t s) := by
  dsimp [ciConnectivity, ciPieceConnectivity, ciChromaticBudget,
    ciCoefficient, ciLocalChromatic] at *
  norm_num1 at *
  have hnonneg : 0 ≤ t * s := Nat.zero_le _
  have hmLower : 943718400000000 * t ≤
      943718400000000 * t * (1 + s) := by
    nlinarith
  have hmRatio : 943718400000000 * (t * s) ≤
      943718400000000 * t * (1 + s) := by
    nlinarith
  have hfan : 3 * r * x = 3 * (r * x) := by ring
  have hknit : 33 * ((4 * r + 1) * x) =
      132 * (r * x) + 33 * x := by ring
  simp only [hfan, hknit] at *
  omega

end HadwigerLean.Inseparability



