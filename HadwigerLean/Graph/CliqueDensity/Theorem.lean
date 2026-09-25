import HadwigerLean.Graph.CliqueDensity.BranchConstruction

/-!
# Quantitative clique-minor density theorem

Appendix E's coefficient-30 Kostochka–Thomason bound, with the finite
range and random branch construction assembled into one checked theorem.
-/

namespace HadwigerLean

/-- Density at least `30 r √(log r)` forces a complete minor of order `r`
for every `r ≥ 2`. -/
theorem hasCliqueMinor_of_edgeDensity_ge
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : ℕ) (hr : 2 ≤ r)
    (hdense : 30 * (r : ℝ) * Real.sqrt (Real.log (r : ℝ)) ≤
      edgeDensity G) :
    HasCliqueMinor G r := by
  classical
  by_cases hsmall : r ≤ 12
  · exact hasCliqueMinor_of_edgeDensity_ge_twelve G r hr hsmall hdense
  · exact hasCliqueMinor_of_edgeDensity_ge_large G r (by omega) hdense

end HadwigerLean
