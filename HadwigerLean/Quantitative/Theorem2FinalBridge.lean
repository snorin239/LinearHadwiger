import HadwigerLean.Quantitative.RoundingBridge
import HadwigerLean.Quantitative.Theorem2

/-!
# Unconditional quantitative bound

The checked low-codegree rounding theorem applies to every finite residual
graph. Combining it with the robust fractional bound gives the paper's
Theorem 2 inequality.
-/

namespace HadwigerLean.Theorem2

universe u

/-- The low-codegree rounding theorem in the universe-polymorphic form
required by the induced-subgraph assembly. -/
theorem low_codegree_rounding_for_all_graphs
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W),
      independenceNumber H ≤ m ε →
      n0 ε ≤ Fintype.card W →
      ∀ x : StableSet H → ℝ,
        IsPairConstrainedColoring H (mu ε / 4) x →
        (∀ v, vertexLoad H x v = 1) →
        (chromatic H : ℝ) ≤ fractionalCost H x +
          gamma ε * (Fintype.card W : ℝ) := by
  intro W _ _ H hα hn x hx hload
  exact low_codegree_rounding H ε hε hε1 hα hn x hx hload

/-- Theorem 2: the quantitative chromatic bound with the paper's explicit
additive constant. -/
theorem quantitative_bound
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (chromatic G : ℝ) ≤
      4 * (cliqueMinorNumber G : ℝ) +
        ε * (Fintype.card V : ℝ) + Aepsilon ε := by
  exact quantitative_bound_of_rounding G ε hε hε1
    (low_codegree_rounding_for_all_graphs ε hε hε1)

end HadwigerLean.Theorem2