import HadwigerLean.Deduction.Asymptotics
import HadwigerLean.Graph.MinorFree
import HadwigerLean.Bootstrap.Definitions

/-! The initial exponent-one-third local linear bound from checked Theorem 2. -/

namespace HadwigerLean.Deduction

open Filter

universe u

/-- For sufficiently large excluded-clique order, Theorem 2 colors graphs
on at most `t (log t)^(1/3)` vertices with at most `6t` colors. -/
theorem initial_local_bound :
    HadwigerLean.Bootstrap.LocalLinearBound.{u} ((1 : ℝ) / 3) := by
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp eventually_initial_epsilon
  refine ⟨6, max t₀ 2, by omega, by omega, ?_⟩
  intro V _ G t ht hminor horder
  classical
  obtain ⟨ht2, hx1, hεpos, hε1, hA, hcancel⟩ :=
    ht₀ t ((Nat.le_max_left _ _).trans ht)
  let x : ℝ := (Real.log (t : ℝ)) ^ ((1 : ℝ) / 3)
  let ε : ℝ := x⁻¹
  have horder' : (Fintype.card V : ℝ) ≤ (t : ℝ) * x := horder
  have hεorder : ε * (Fintype.card V : ℝ) ≤ (t : ℝ) := by
    calc
      ε * (Fintype.card V : ℝ) ≤ ε * ((t : ℝ) * x) :=
        mul_le_mul_of_nonneg_left horder' hεpos.le
      _ = (t : ℝ) := hcancel
  have hh : cliqueMinorNumber G ≤ t :=
    (not_hasCliqueMinor_iff_cliqueMinorNumber_lt G t).mp hminor |>.le
  have hh' : (cliqueMinorNumber G : ℝ) ≤ (t : ℝ) := by exact_mod_cast hh
  have hquant := HadwigerLean.Theorem2.quantitative_bound G ε hεpos hε1
  have hreal : (HadwigerLean.chromatic G : ℝ) ≤ (6 * t : ℕ) := by
    push_cast
    nlinarith
  exact_mod_cast hreal

end HadwigerLean.Deduction
