import HadwigerLean.Deduction.Corollary24Final
import HadwigerLean.Deduction.Corollary24Transport
import HadwigerLean.Woven.ScaleBridge
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Corollary 24 specialization of the shared outer woven induction. -/

namespace HadwigerLean.Deduction

open HadwigerLean.Bootstrap

universe u

/-- At the top scale, the Corollary 24 cutoff is strict. -/
theorem cor24_top_scale_above_cutoff
    (T : ℕ) (hT : 100 ≤ T) :
    (T : ℝ) / Real.sqrt (Real.log (T : ℝ)) < (T : ℝ) := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hlog : (1 : ℝ) < Real.log (T : ℝ) := by
    apply (Real.lt_log_iff_exp_lt hTpos).2
    have h3T : (3 : ℝ) ≤ T := by exact_mod_cast (by omega : 3 ≤ T)
    exact Real.exp_one_lt_three.trans_le h3T
  have hsqrt : (1 : ℝ) < Real.sqrt (Real.log (T : ℝ)) := by
    have hsq := Real.sq_sqrt (show 0 ≤ Real.log (T : ℝ) by linarith)
    have hnon := Real.sqrt_nonneg (Real.log (T : ℝ))
    nlinarith
  apply (div_lt_iff₀ (by linarith : 0 < Real.sqrt (Real.log (T : ℝ)))).2
  nlinarith

/-- The shared scale-by-scale woven theorem, stated as the exact input
needed by the Corollary 24 specialization. -/
def Cor24SharedOuterWoven : Prop :=
  ∀ (V : Type u) [Fintype V] (G : SimpleGraph V)
    (T d a : ℕ),
    100 ≤ T → 1 ≤ d →
    IsOuterScale T a →
    (T : ℝ) / Real.sqrt (Real.log (T : ℝ)) < (a : ℝ) →
    OuterSeparation G T d →
    VertexConnected G (10000 * a) →
    2000 * T + cor24B d * a ≤ chromatic G →
    Woven G a (3 * a)

/-- The common woven induction at Corollary 24's numerical constants
implies the paper's complete Corollary 24 statement. -/
theorem corollary24_of_shared_outer_woven
    (hOuter : Cor24SharedOuterWoven.{u}) :
    Corollary24Statement.{u} := by
  classical
  intro V _ G t T d ht hT hd hminor hsep
  apply cor24_final_of_top_woven G t T d ht hT hminor
  intro U hconn hχ
  have hT100 : 100 ≤ T := le_trans ht hT.2.1
  have hscale : IsOuterScale T T := by
    exact ⟨0, by simp⟩
  have hcut := cor24_top_scale_above_cutoff T hT100
  have hsepU : OuterSeparation (G.induce (U : Set V)) T d :=
    outerSeparation_induce G T d hsep (U : Set V)
  exact hOuter (U : Set V) (G.induce (U : Set V)) T d T
    hT100 hd hscale hcut hsepU hconn hχ

end HadwigerLean.Deduction
