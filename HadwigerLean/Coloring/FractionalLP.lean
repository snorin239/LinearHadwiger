import HadwigerLean.Coloring.Fractional
import HadwigerLean.Optimization.FiniteLP

/-!
# Fractional coloring as a finite covering linear program

The rows are vertices and the columns are nonempty stable sets.  This module
identifies both feasible regions and both objective functions with the generic
finite LP interface.
-/

namespace HadwigerLean

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The covering LP for fractional chromatic number. -/
noncomputable def fractionalLP (G : SimpleGraph V) :
    FiniteLP.Problem V (StableSet G) where
  A v S := if v ∈ S.1 then 1 else 0
  b _ := 1
  c _ := 1

theorem fractionalLP_primalFeasible_iff (G : SimpleGraph V)
    (x : StableSet G → ℝ) :
    (fractionalLP G).PrimalFeasible x ↔ IsFractionalColoring G x := by
  classical
  simp only [FiniteLP.Problem.PrimalFeasible, IsFractionalColoring,
    fractionalLP, vertexLoad]
  constructor <;> rintro ⟨hnonneg, hcover⟩ <;> refine ⟨hnonneg, ?_⟩
  · intro v
    simpa [ite_mul] using hcover v
  · intro v
    simpa [ite_mul] using hcover v

theorem fractionalLP_dualFeasible_iff (G : SimpleGraph V) (w : V → ℝ) :
    (fractionalLP G).DualFeasible w ↔ IsFractionalDualFeasible G w := by
  classical
  simp only [FiniteLP.Problem.DualFeasible, IsFractionalDualFeasible,
    fractionalLP]
  constructor <;> rintro ⟨hnonneg, hstable⟩ <;> refine ⟨hnonneg, ?_⟩
  · intro S
    simpa [ite_mul, Finset.sum_ite] using hstable S
  · intro S
    simpa [ite_mul, Finset.sum_ite] using hstable S

theorem fractionalLP_primalValue (G : SimpleGraph V) (x : StableSet G → ℝ) :
    (fractionalLP G).primalValue x = fractionalCost G x := by
  simp [FiniteLP.Problem.primalValue, fractionalLP, fractionalCost]

theorem fractionalLP_dualValue (G : SimpleGraph V) (w : V → ℝ) :
    (fractionalLP G).dualValue w = fractionalDualValue w := by
  simp [FiniteLP.Problem.dualValue, fractionalLP, fractionalDualValue]

/-- On a finite graph, the infimum defining fractional chromatic number is attained. -/
theorem exists_fractionalColoring_minimizer (G : SimpleGraph V) :
    ∃ x : StableSet G → ℝ,
      IsFractionalColoring G x ∧
        fractionalCost G x = fractionalChromaticNumber G := by
  classical
  have hc : ∀ S : StableSet G, 0 < (fractionalLP G).c S := by
    intro S
    simp [fractionalLP]
  have hsingle : (fractionalLP G).PrimalFeasible
      (singletonFractionalColoring G) :=
    (fractionalLP_primalFeasible_iff G _).2
      (singletonFractionalColoring_feasible G)
  obtain ⟨x, hx, hmin⟩ :=
    (fractionalLP G).exists_primal_minimizer hc hsingle
  have hx' : IsFractionalColoring G x :=
    (fractionalLP_primalFeasible_iff G x).1 hx
  refine ⟨x, hx', le_antisymm ?_ (fractionalChromaticNumber_le_cost G hx')⟩
  unfold fractionalChromaticNumber
  apply le_csInf
  · exact ⟨fractionalCost G x, x, hx', rfl⟩
  · rintro t ⟨z, hz, rfl⟩
    simpa only [fractionalLP_primalValue] using
      hmin z ((fractionalLP_primalFeasible_iff G z).2 hz)

/-- Fractional coloring has optimal primal and dual solutions with equal values. -/
theorem exists_fractional_primal_dual_optima (G : SimpleGraph V) :
    ∃ x : StableSet G → ℝ, ∃ w : V → ℝ,
      IsFractionalColoring G x ∧ IsFractionalDualFeasible G w ∧
        fractionalCost G x = fractionalDualValue w ∧
        fractionalChromaticNumber G = fractionalCost G x := by
  classical
  have hc : ∀ S : StableSet G, 0 < (fractionalLP G).c S := by
    intro S
    simp [fractionalLP]
  have hsingle : (fractionalLP G).PrimalFeasible
      (singletonFractionalColoring G) :=
    (fractionalLP_primalFeasible_iff G _).2
      (singletonFractionalColoring_feasible G)
  obtain ⟨x, w, hx, hw, heq⟩ :=
    (fractionalLP G).exists_primal_dual_optima hc hsingle
  have hx' : IsFractionalColoring G x :=
    (fractionalLP_primalFeasible_iff G x).1 hx
  have hw' : IsFractionalDualFeasible G w :=
    (fractionalLP_dualFeasible_iff G w).1 hw
  have hcost : fractionalCost G x = fractionalDualValue w := by
    simpa only [fractionalLP_primalValue, fractionalLP_dualValue] using heq
  refine ⟨x, w, hx', hw', hcost, ?_⟩
  apply le_antisymm (fractionalChromaticNumber_le_cost G hx')
  calc
    fractionalCost G x = fractionalDualValue w := hcost
    _ ≤ fractionalChromaticNumber G := fractionalDualValue_le_chromatic G hw'

/-- The dual vertex-weight formulation attains fractional chromatic number. -/
theorem exists_fractionalDual_optimum (G : SimpleGraph V) :
    ∃ w : V → ℝ,
      IsFractionalDualFeasible G w ∧
        fractionalDualValue w = fractionalChromaticNumber G := by
  obtain ⟨x, w, _, hw, hcost, hchrom⟩ :=
    exists_fractional_primal_dual_optima G
  exact ⟨w, hw, hcost.symm.trans hchrom.symm⟩

@[simp] theorem fractionalChromaticNumber_eq_zero_of_isEmpty
    (G : SimpleGraph V) [IsEmpty V] : fractionalChromaticNumber G = 0 := by
  obtain ⟨w, _, hw⟩ := exists_fractionalDual_optimum G
  simpa [fractionalDualValue] using hw.symm

end HadwigerLean
