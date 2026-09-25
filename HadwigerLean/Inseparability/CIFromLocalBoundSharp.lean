import HadwigerLean.Inseparability.CIFromStageBudgets
import HadwigerLean.Inseparability.CILocalWindow
import HadwigerLean.Inseparability.StageSharpBudget
import HadwigerLean.Inseparability.FirstWovenBudget

/-!
# Chromatic inseparability from the local bound and sharp wovenness

All numerical CI parameters are now fixed. The only remaining graph
input is the sharp woven theorem on the packed small connected pieces.
-/

namespace HadwigerLean.Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem chromatic_separable_of_local_bound_and_sharp_woven
    (G : SimpleGraph V) (t s : ℕ)
    (ht : 3 ≤ t) (hminor : ¬ HasCliqueMinor G t)
    (hlocal : ∀ Y : Finset V,
      (Y.card : ℝ) ≤ (ciCoefficient : ℝ) * (t : ℝ) *
        (Real.log (t : ℝ))^4 →
      chromatic (G.induce (Y : Set V)) ≤ t * s)
    (hχ : 2 * ciChromaticBudget t s ≤ chromatic G)
    (hsharp : ∀ p, p < stageCount t → ∀ Y : Finset V,
      VertexConnected (G.induce (Y : Set V))
        (ciPieceConnectivity t) →
      Woven (G.induce (Y : Set V))
        (2 * stageBlockSize t)
        ((4 * p + 1) * stageBlockSize t)) :
    Bootstrap.ChromaticSeparable G (ciChromaticBudget t s) := by
  classical
  let r := stageCount t
  let x := stageBlockSize t
  let N := ciPieceOrderBound t
  let b : ℕ → ℕ := ciCoreBound N x
  have hrx : r * x ≤ 3 * t := stageCount_mul_block_le_three t ht
  have horder : t ≤ r * x := stageCount_mul_block_ge t ht
  have hx : 0 < x := by
    by_contra h
    have hx0 : x = 0 := Nat.eq_zero_of_not_pos h
    simp [hx0] at horder
    omega
  have hk : 0 < ciConnectivity t := by
    dsimp [ciConnectivity]
    omega
  have hNat := ci_linear_stage_budgets t s r x (chromatic G)
    ht (stageBlockSize_le t ht) hrx hχ
  rcases hNat with ⟨hconnect,hχPacking,hχRaw,hreserveRaw,
    hSourceFan,hSourceFinish,hMixedBudget,hMiddleSize,
    hFinishSize,hChildRoots,hKnitting,hbaseBudget,
    hχIter,hreserveIter,hbudgetIter⟩
  have hlocalCore : ∀ Y : Finset V, Y.card ≤ 3 * b r →
      chromatic (G.induce (Y : Set V)) ≤ ciLocalChromatic t s := by
    intro Y hY
    apply hlocal Y
    have hYR : (Y.card : ℝ) ≤ ((3 * b r : ℕ) : ℝ) := by
      exact_mod_cast hY
    exact hYR.trans (ciCoreBound_local_window t ht)
  have hLocalWindow : r * N ≤ 3 * b r :=
    ciCoreBound_localWindow N x r (stageCount_pos t ht)
  have hsize : (480 * 6400 : ℝ)^2 * (t : ℝ) *
      (Real.log (t : ℝ))^3 ≤ (N : ℝ) :=
    ciPieceOrderBound_ge t
  have htℓ : t ≤ ciPieceConnectivity t := by
    dsimp [ciPieceConnectivity]
    omega
  have hfirst : Woven.uniformCliqueK x 0 ≤ ciPieceConnectivity t :=
    first_stage_uniformCliqueK_le t 9000000 ht le_rfl
  exact chromatic_separable_of_SC_stage_budgets G t r x
    (ciConnectivity t) (ciChromaticBudget t s)
    (ciLocalChromatic t s) (ciPieceConnectivity t) N b
    ht hx hk hminor horder
    (ciCoreBound_zero N x)
    (fun u hu => ciCoreBound_mono N x u r hu)
    hsize htℓ hlocalCore hLocalWindow
    hconnect hχPacking hχRaw hreserveRaw
    hSourceFan hSourceFinish hMixedBudget hMiddleSize
    hFinishSize hChildRoots hsharp hfirst hKnitting
    (ciCoreBound_first N x)
    (fun u _ => ciCoreBound_step N x u)
    hbaseBudget hχIter hreserveIter hbudgetIter

end HadwigerLean.Inseparability
