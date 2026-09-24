import HadwigerLean.Graph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
Finite fractional colorings and their dual vertex weights.

The weights are indexed by nonempty finite stable sets. The paper's vertex
coverage inequalities and stable-set dual constraints appear directly in the
definitions below. Strong duality is developed separately in
`HadwigerLean.Optimization.FiniteLP`.
-/

namespace HadwigerLean

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A nonempty independent set, used as an index for a fractional coloring. -/
abbrev StableSet (G : SimpleGraph V) :=
  {S : Finset V // S.Nonempty ∧ G.IsIndepSet (S : Set V)}

noncomputable instance stableSetFintype (G : SimpleGraph V) : Fintype (StableSet G) := by
  classical
  infer_instance

/-- The total weight given by a coloring to stable sets containing `v`. -/
noncomputable def vertexLoad (G : SimpleGraph V) (x : StableSet G → ℝ) (v : V) : ℝ :=
  ∑ S : StableSet G, if v ∈ S.1 then x S else 0

/-- The cost of a fractional coloring. -/
noncomputable def fractionalCost (G : SimpleGraph V) (x : StableSet G → ℝ) : ℝ :=
  ∑ S : StableSet G, x S

/-- Fractional coloring in the covering (primal) formulation. -/
def IsFractionalColoring (G : SimpleGraph V) (x : StableSet G → ℝ) : Prop :=
  (∀ S, 0 ≤ x S) ∧ ∀ v, 1 ≤ vertexLoad G x v

/-- Feasibility for the dual formulation of fractional coloring. -/
def IsFractionalDualFeasible (G : SimpleGraph V) (w : V → ℝ) : Prop :=
  (∀ v, 0 ≤ w v) ∧ ∀ S : StableSet G, (∑ v ∈ S.1, w v) ≤ 1

/-- The objective value of a feasible dual vertex weight. -/
noncomputable def fractionalDualValue (w : V → ℝ) : ℝ :=
  ∑ v, w v

theorem fractionalCost_nonneg (G : SimpleGraph V) {x : StableSet G → ℝ}
    (hx : IsFractionalColoring G x) : 0 ≤ fractionalCost G x := by
  classical
  exact Finset.sum_nonneg (fun S _ => hx.1 S)

omit [DecidableEq V] in
theorem stableSet_mem (G : SimpleGraph V) (S : StableSet G) :
    S.1 ∈ stableFinsets G := by
  simp [S.property.2]
/-- The singleton at a vertex is a legal stable-set column. -/
def singletonStableSet (G : SimpleGraph V) (v : V) : StableSet G :=
  ⟨{v}, by simp [SimpleGraph.isIndepSet_iff]⟩

omit [Fintype V] [DecidableEq V] in
theorem dual_weight_le_one (G : SimpleGraph V) {w : V → ℝ}
    (hw : IsFractionalDualFeasible G w) (v : V) : w v ≤ 1 := by
  simpa [singletonStableSet] using hw.2 (singletonStableSet G v)

/-- Assign weight one to every singleton stable set. -/
noncomputable def singletonFractionalColoring (G : SimpleGraph V) : StableSet G → ℝ :=
  fun S => if S.1.card = 1 then 1 else 0

omit [Fintype V] [DecidableEq V] in
private theorem stableSet_eq_singleton (G : SimpleGraph V) (S : StableSet G)
    (v : V) (hv : v ∈ S.1) (hcard : S.1.card = 1) :
    S = singletonStableSet G v := by
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcard
  have hvu : v = u := by simpa [hu] using hv
  subst u
  exact Subtype.ext hu

theorem singletonFractionalColoring_vertexLoad (G : SimpleGraph V) (v : V) :
    vertexLoad G (singletonFractionalColoring G) v = 1 := by
  classical
  have hterm (S : StableSet G) :
      (if v ∈ S.1 then singletonFractionalColoring G S else 0) =
        if S = singletonStableSet G v then 1 else 0 := by
    by_cases hs : S = singletonStableSet G v
    · subst S
      simp [singletonFractionalColoring, singletonStableSet]
    · by_cases hcard : S.1.card = 1
      · have hvnot : v ∉ S.1 := by
          intro hv
          exact hs (stableSet_eq_singleton G S v hv hcard)
        simp [hvnot, hs]
      · simp [singletonFractionalColoring, hcard, hs]
  calc
    vertexLoad G (singletonFractionalColoring G) v =
        ∑ S : StableSet G, if S = singletonStableSet G v then 1 else 0 := by
          unfold vertexLoad
          apply Finset.sum_congr rfl
          intro S _
          exact hterm S
    _ = 1 := by simp

theorem singletonFractionalColoring_feasible (G : SimpleGraph V) :
    IsFractionalColoring G (singletonFractionalColoring G) := by
  constructor
  · intro S
    by_cases h : S.1.card = 1 <;> simp [singletonFractionalColoring, h]
  · intro v
    rw [singletonFractionalColoring_vertexLoad]
/-- Minimum cost of a fractional coloring, represented as an infimum. -/
noncomputable def fractionalChromaticNumber (G : SimpleGraph V) : ℝ :=
  sInf {t : ℝ | ∃ x : StableSet G → ℝ,
    IsFractionalColoring G x ∧ fractionalCost G x = t}

private theorem fractionalCosts_nonempty (G : SimpleGraph V) :
    {t : ℝ | ∃ x : StableSet G → ℝ,
      IsFractionalColoring G x ∧ fractionalCost G x = t}.Nonempty := by
  refine ⟨fractionalCost G (singletonFractionalColoring G), ?_⟩
  exact ⟨singletonFractionalColoring G,
    singletonFractionalColoring_feasible G, rfl⟩

private theorem fractionalCosts_bddBelow (G : SimpleGraph V) :
    BddBelow {t : ℝ | ∃ x : StableSet G → ℝ,
      IsFractionalColoring G x ∧ fractionalCost G x = t} := by
  refine ⟨0, ?_⟩
  rintro t ⟨x, hx, rfl⟩
  exact fractionalCost_nonneg G hx

theorem fractionalChromaticNumber_nonneg (G : SimpleGraph V) :
    0 ≤ fractionalChromaticNumber G := by
  unfold fractionalChromaticNumber
  apply le_csInf (fractionalCosts_nonempty G)
  rintro t ⟨x, hx, rfl⟩
  exact fractionalCost_nonneg G hx

theorem fractionalChromaticNumber_le_cost (G : SimpleGraph V)
    {x : StableSet G → ℝ} (hx : IsFractionalColoring G x) :
    fractionalChromaticNumber G ≤ fractionalCost G x := by
  unfold fractionalChromaticNumber
  apply csInf_le (fractionalCosts_bddBelow G)
  exact ⟨x, hx, rfl⟩
theorem weighted_vertexLoad_eq (G : SimpleGraph V) (x : StableSet G → ℝ)
    (w : V → ℝ) :
    (∑ v, w v * vertexLoad G x v) =
      ∑ S : StableSet G, x S * ∑ v ∈ S.1, w v := by
  classical
  calc
    (∑ v, w v * vertexLoad G x v) =
        ∑ v, ∑ S : StableSet G, if v ∈ S.1 then w v * x S else 0 := by
          simp [vertexLoad, mul_sum, mul_ite]
    _ = ∑ S : StableSet G, ∑ v, if v ∈ S.1 then w v * x S else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ S : StableSet G, x S * ∑ v ∈ S.1, w v := by
          apply Finset.sum_congr rfl
          intro S _
          simp [mul_sum, mul_comm]

/-- Weak duality for fractional coloring. -/
theorem fractional_weak_duality (G : SimpleGraph V) {x : StableSet G → ℝ}
    {w : V → ℝ} (hx : IsFractionalColoring G x)
    (hw : IsFractionalDualFeasible G w) :
    fractionalDualValue w ≤ fractionalCost G x := by
  classical
  rcases hx with ⟨hx_nonneg, hx_cover⟩
  rcases hw with ⟨hw_nonneg, hw_stable⟩
  have hcover : (∑ v, w v) ≤ ∑ v, w v * vertexLoad G x v := by
    apply Finset.sum_le_sum
    intro v _
    simpa using mul_le_mul_of_nonneg_left (hx_cover v) (hw_nonneg v)
  have hstable :
      (∑ S : StableSet G, x S * ∑ v ∈ S.1, w v) ≤
        ∑ S : StableSet G, x S := by
    apply Finset.sum_le_sum
    intro S _
    simpa using mul_le_mul_of_nonneg_left (hw_stable S) (hx_nonneg S)
  calc
    fractionalDualValue w = ∑ v, w v := rfl
    _ ≤ ∑ v, w v * vertexLoad G x v := hcover
    _ = ∑ S : StableSet G, x S * ∑ v ∈ S.1, w v :=
      weighted_vertexLoad_eq G x w
    _ ≤ ∑ S : StableSet G, x S := hstable
    _ = fractionalCost G x := rfl
theorem fractionalDualValue_le_chromatic (G : SimpleGraph V) {w : V → ℝ}
    (hw : IsFractionalDualFeasible G w) :
    fractionalDualValue w ≤ fractionalChromaticNumber G := by
  unfold fractionalChromaticNumber
  apply le_csInf (fractionalCosts_nonempty G)
  rintro t ⟨x, hx, rfl⟩
  exact fractional_weak_duality G hx hw
end HadwigerLean
