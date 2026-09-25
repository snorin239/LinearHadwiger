import HadwigerLean.Inseparability.ScaleCeilEstimates
import HadwigerLean.Inseparability.SharpWovenBudget

/-! The paper's logarithmic stage parameters fit the sharp woven budget. -/

namespace HadwigerLean.Inseparability

theorem stage_sharp_woven_budget
    (t p C : ℕ) (ht : 3 ≤ t)
    (hp : p < stageCount t) (hC : 9000000 ≤ C) :
    1000000 *
      HadwigerLean.RootedDensity.cliqueMatchingScale
        (2 * stageBlockSize t) ((4 * p + 1) * stageBlockSize t) ≤
      ((C * t : ℕ) : ℝ) := by
  exact sharp_woven_stage_budget t p (stageBlockSize t) C
    (stageBlockSize_root_log_bound t ht)
    (stageIndex_mul_block_le t p ht hp)
    (stageBlockSize_le t ht) hC

end HadwigerLean.Inseparability
