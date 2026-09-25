import HadwigerLean.Inseparability.CIFromLocalBoundSharp
import HadwigerLean.Inseparability.StageSharpBudget
import HadwigerLean.Woven.UniformSparseFinal

/-! Unconditional chromatic inseparability at the explicit CI coefficient. -/

namespace HadwigerLean.Inseparability

universe u

theorem chromatic_separable_of_local_bound_complete
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (t s : ℕ)
    (ht : 3 ≤ t) (hminor : ¬ HasCliqueMinor G t)
    (hlocal : ∀ Y : Finset V,
      (Y.card : ℝ) ≤ (ciCoefficient : ℝ) * (t : ℝ) *
        (Real.log (t : ℝ)) ^ 4 →
      chromatic (G.induce (Y : Set V)) ≤ t * s)
    (hχ : 2 * ciChromaticBudget t s ≤ chromatic G) :
    Bootstrap.ChromaticSeparable G (ciChromaticBudget t s) := by
  classical
  apply chromatic_separable_of_local_bound_and_sharp_woven
    G t s ht hminor hlocal hχ
  intro p hp Y hconn
  have hx : 0 < stageBlockSize t := stageBlockSize_pos t ht
  have ha : 2 ≤ 2 * stageBlockSize t := by omega
  have hbudget : 1000000 *
      HadwigerLean.RootedDensity.cliqueMatchingScale
        (2 * stageBlockSize t) ((4 * p + 1) * stageBlockSize t) ≤
      (ciPieceConnectivity t : ℝ) := by
    simpa only [ciPieceConnectivity] using
      stage_sharp_woven_budget t p 9000000 ht hp le_rfl
  exact HadwigerLean.Woven.woven_of_sharp_connectivity
    (G.induce (Y : Set V))
    (2 * stageBlockSize t) ((4 * p + 1) * stageBlockSize t)
    (ciPieceConnectivity t) ha hconn hbudget

end HadwigerLean.Inseparability
