import HadwigerLean.Graph.RootedDensity.DisjointEdge
import HadwigerLean.Graph.CliqueDensity.Theorem
import Mathlib.Tactic

/-! An unrooted density threshold for a clique plus disjoint matching edges. -/

namespace HadwigerLean.RootedDensity

/-- Labels for a clique followed by `b` independent edge components. -/
def CliqueMatchingLabels (a : ℕ) : ℕ → Type
  | 0 => Fin a
  | b + 1 => CliqueMatchingLabels a b ⊕ Fin 2

instance cliqueMatchingLabelsFintype (a b : ℕ) :
    Fintype (CliqueMatchingLabels a b) := by
  induction b with
  | zero => exact inferInstanceAs (Fintype (Fin a))
  | succ b ih =>
      change Fintype (CliqueMatchingLabels a b ⊕ Fin 2)
      letI := ih
      infer_instance

/-- The target `K_a + b K₂`, with its matching edges added recursively. -/
def cliqueMatchingGraph (a : ℕ) :
    (b : ℕ) → SimpleGraph (CliqueMatchingLabels a b)
  | 0 => SimpleGraph.completeGraph (Fin a)
  | b + 1 => cliqueMatchingGraph a b ⊕g SimpleGraph.completeGraph (Fin 2)

/-- The density threshold used in Appendix F, Section 7.1. -/
noncomputable def cliqueMatchingThreshold (a b : ℕ) : ℝ :=
  30 * (a : ℝ) * Real.sqrt (Real.log (a : ℝ)) + 2 * (b : ℝ)

/-- `30 a √(log a) + 2b` edge density forces a minor of `K_a + b K₂`.
The target is represented as a recursive disjoint graph sum. -/
theorem densityForcesMinor_cliqueMatching
    (a b : ℕ) (ha : 2 ≤ a) :
    DensityForcesMinor (cliqueMatchingGraph a b)
      (cliqueMatchingThreshold a b) := by
  induction b with
  | zero =>
      intro V _ G hn hdense
      classical
      have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
      have hd : 30 * (a : ℝ) * Real.sqrt (Real.log (a : ℝ)) ≤
          edgeDensity G := by
        unfold edgeDensity cliqueMatchingThreshold at *
        exact (le_div_iff₀ hnR).2 (by simpa using hdense)
      exact hasCliqueMinor_of_edgeDensity_ge G a ha hd
  | succ b ih =>
      have hnonneg : 0 ≤ cliqueMatchingThreshold a b := by
        unfold cliqueMatchingThreshold
        positivity
      have hsum := densityForcesMinor_sum_edge
        (cliqueMatchingGraph a b) (cliqueMatchingThreshold a b) hnonneg ih
      have hth : cliqueMatchingThreshold a (b + 1) =
          cliqueMatchingThreshold a b + 2 := by
        unfold cliqueMatchingThreshold
        push_cast
        ring
      change DensityForcesMinor
        (cliqueMatchingGraph a b ⊕g SimpleGraph.completeGraph (Fin 2))
        (cliqueMatchingThreshold a (b + 1))
      rw [hth]
      exact hsum


/-- The recursive target has exactly the expected number of labels. -/
theorem cliqueMatchingLabels_card (a b : ℕ) :
    Fintype.card (CliqueMatchingLabels a b) = a + 2 * b := by
  induction b with
  | zero =>
      change Fintype.card (Fin a) = a
      exact Fintype.card_fin a
  | succ b ih =>
      change Fintype.card (CliqueMatchingLabels a b ⊕ Fin 2) = a + 2 * (b + 1)
      rw [Fintype.card_sum, ih]
      simp
      omega

/-- The base density threshold is nonnegative. -/
theorem cliqueMatchingThreshold_nonneg (a b : ℕ) :
    0 ≤ cliqueMatchingThreshold a b := by
  unfold cliqueMatchingThreshold
  positivity

/-- The target has at least three vertices outside the lone excluded case
`(a,b)=(2,0)` of the uniform woven argument. -/
theorem cliqueMatchingLabels_card_ge_three
    (a b : ℕ) (ha : 2 ≤ a) (hcase : 3 ≤ a ∨ 1 ≤ b) :
    3 ≤ Fintype.card (CliqueMatchingLabels a b) := by
  rw [cliqueMatchingLabels_card]
  omega
end HadwigerLean.RootedDensity






