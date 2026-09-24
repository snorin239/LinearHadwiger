import HadwigerLean.Vendor.EconCSLib.Math.LinearProgramming.StrongDuality
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FunProp

/-!
# Finite covering linear programs

We use a covering form with nonnegative variables.  Upper bounds, including the
pair-load constraints in the coloring argument, are represented by negating a
row of the matrix and its right-hand side.  Thus the dual variables for those
rows are still nonnegative.
-/

namespace HadwigerLean.FiniteLP

variable {Row Col : Type*} [Fintype Row] [Fintype Col]

/-- A finite covering linear program: minimize `c ⬝ x` subject to `x ≥ 0` and
`A x ≥ b`. -/
structure Problem (Row Col : Type*) where
  A : Row → Col → ℝ
  b : Row → ℝ
  c : Col → ℝ

namespace Problem

variable (P : Problem Row Col)

/-- Feasible primal point for a covering linear program. -/
def PrimalFeasible (x : Col → ℝ) : Prop :=
  (∀ j, 0 ≤ x j) ∧ (∀ i, P.b i ≤ ∑ j, P.A i j * x j)

/-- Feasible dual point. -/
def DualFeasible (y : Row → ℝ) : Prop :=
  (∀ i, 0 ≤ y i) ∧ (∀ j, (∑ i, P.A i j * y i) ≤ P.c j)

def primalValue (x : Col → ℝ) : ℝ := ∑ j, P.c j * x j

def dualValue (y : Row → ℝ) : ℝ := ∑ i, P.b i * y i

/-- The part of the feasible region below a prescribed primal cost. -/
def primalSublevel (r : ℝ) : Set (Col → ℝ) :=
  {x | P.PrimalFeasible x ∧ P.primalValue x ≤ r}

omit [Fintype Row] in
theorem continuous_primalValue : Continuous P.primalValue := by
  unfold primalValue
  fun_prop

omit [Fintype Row] in
theorem continuous_rowValue (i : Row) :
    Continuous (fun x : Col → ℝ => ∑ j, P.A i j * x j) := by
  fun_prop

omit [Fintype Row] in
theorem isClosed_primalFeasible : IsClosed {x : Col → ℝ | P.PrimalFeasible x} := by
  unfold PrimalFeasible
  apply IsClosed.inter
  · change IsClosed {x : Col → ℝ | ∀ j, 0 ≤ x j}
    rw [Set.setOf_forall]
    exact isClosed_iInter (fun j : Col =>
      isClosed_le (continuous_const : Continuous (fun _ : Col → ℝ => (0 : ℝ)))
        (continuous_apply j))
  · change IsClosed {x : Col → ℝ | ∀ i, P.b i ≤ ∑ j, P.A i j * x j}
    rw [Set.setOf_forall]
    exact isClosed_iInter (fun i : Row =>
      isClosed_le (continuous_const : Continuous (fun _ : Col → ℝ => P.b i))
        (P.continuous_rowValue i))

omit [Fintype Row] in
theorem isClosed_primalSublevel (r : ℝ) : IsClosed (P.primalSublevel r) := by
  unfold primalSublevel
  exact P.isClosed_primalFeasible.inter
    (isClosed_le P.continuous_primalValue continuous_const)

/-- Strictly positive costs make every primal sublevel compact. -/
theorem isCompact_primalSublevel (hc : ∀ j, 0 < P.c j) (r : ℝ) :
    IsCompact (P.primalSublevel r) := by
  classical
  apply IsCompact.of_isClosed_subset (isCompact_Icc :
    IsCompact (Set.Icc (fun _ : Col => (0 : ℝ)) (fun j => r / P.c j)))
    (P.isClosed_primalSublevel r)
  intro x hx
  refine ⟨fun j => hx.1.1 j, fun j => ?_⟩
  have hsingle : P.c j * x j ≤ P.primalValue x := by
    unfold primalValue
    exact Finset.single_le_sum
      (fun k _ => mul_nonneg (le_of_lt (hc k)) (hx.1.1 k)) (Finset.mem_univ j)
  exact (le_div_iff₀ (hc j)).2 (by simpa [mul_comm] using hsingle.trans hx.2)
/-- A feasible covering LP with strictly positive costs attains its minimum. -/
theorem exists_primal_minimizer (hc : ∀ j, 0 < P.c j)
    {x₀ : Col → ℝ} (hx₀ : P.PrimalFeasible x₀) :
    ∃ x, P.PrimalFeasible x ∧
      ∀ z, P.PrimalFeasible z → P.primalValue x ≤ P.primalValue z := by
  let K := P.primalSublevel (P.primalValue x₀)
  have hK : IsCompact K := P.isCompact_primalSublevel hc _
  have hne : K.Nonempty := ⟨x₀, hx₀, le_rfl⟩
  obtain ⟨x, hx, hmin⟩ :=
    hK.exists_isMinOn hne P.continuous_primalValue.continuousOn
  refine ⟨x, hx.1, ?_⟩
  intro z hz
  by_cases hcost : P.primalValue z ≤ P.primalValue x₀
  · exact hmin ⟨hz, hcost⟩
  · exact hx.2.trans (le_of_lt (lt_of_not_ge hcost))
/-- Every dual feasible value is at most every primal feasible value. -/
theorem weak_duality {x : Col → ℝ} {y : Row → ℝ}
    (hx : P.PrimalFeasible x) (hy : P.DualFeasible y) :
    P.dualValue y ≤ P.primalValue x := by
  classical
  calc
    P.dualValue y ≤ ∑ i, (∑ j, P.A i j * x j) * y i := by
      unfold dualValue
      exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (hx.2 i) (hy.1 i)
    _ = ∑ j, (∑ i, P.A i j * y i) * x j := by
      simp_rw [Finset.sum_mul, mul_assoc, mul_comm (x _) (y _)]
      exact Finset.sum_comm
    _ ≤ P.primalValue x := by
      unfold primalValue
      exact Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_right (hy.2 j) (hx.1 j)

/-- Reindex a finite LP by a canonical finite set of columns. -/
noncomputable def toFin : Problem Row (Fin (Fintype.card Col)) where
  A i j := P.A i ((Fintype.equivFin Col).symm j)
  b := P.b
  c j := P.c ((Fintype.equivFin Col).symm j)

private theorem toFin_row_sum (x : Fin (Fintype.card Col) → ℝ) (i : Row) :
    (∑ j, P.toFin.A i j * x j) =
      ∑ j, P.A i j * x ((Fintype.equivFin Col) j) := by
  classical
  let e := (Fintype.equivFin Col).symm
  simpa [toFin, e] using
    (Fintype.sum_equiv e
      (fun j : Fin (Fintype.card Col) => P.A i (e j) * x j)
      (fun j : Col => P.A i j * x (e.symm j))
      (fun j => by simp))

theorem toFin_primal_iff (x : Fin (Fintype.card Col) → ℝ) :
    P.toFin.PrimalFeasible x ↔
      P.PrimalFeasible (fun j => x ((Fintype.equivFin Col) j)) := by
  classical
  constructor
  · intro hx
    refine ⟨fun j => hx.1 ((Fintype.equivFin Col) j), fun i => ?_⟩
    have hrow := hx.2 i
    change P.b i ≤ ∑ j, P.toFin.A i j * x j at hrow
    rw [P.toFin_row_sum x i] at hrow
    exact hrow
  · intro hx
    refine ⟨fun j => ?_, fun i => ?_⟩
    · simpa using hx.1 ((Fintype.equivFin Col).symm j)
    · change P.b i ≤ ∑ j, P.toFin.A i j * x j
      rw [P.toFin_row_sum x i]
      exact hx.2 i

theorem toFin_dual_iff (y : Row → ℝ) :
    P.toFin.DualFeasible y ↔ P.DualFeasible y := by
  classical
  constructor
  · intro hy
    refine ⟨hy.1, fun j => ?_⟩
    simpa [toFin] using hy.2 ((Fintype.equivFin Col) j)
  · intro hy
    refine ⟨hy.1, fun j => ?_⟩
    simpa [toFin] using hy.2 ((Fintype.equivFin Col).symm j)

theorem toFin_primalValue (x : Fin (Fintype.card Col) → ℝ) :
    P.toFin.primalValue x =
      P.primalValue (fun j => x ((Fintype.equivFin Col) j)) := by
  classical
  let e := (Fintype.equivFin Col).symm
  simpa [toFin, primalValue, e] using
    (Fintype.sum_equiv e
      (fun j : Fin (Fintype.card Col) => P.c (e j) * x j)
      (fun j : Col => P.c j * x (e.symm j))
      (fun j => by simp))
/-- A lower bound on every feasible primal point has an attained dual certificate. -/
theorem exists_dual_ge (d : ℝ)
    (hfeas : ∃ x, P.PrimalFeasible x)
    (hbound : ∀ x, P.PrimalFeasible x → d ≤ P.primalValue x) :
    ∃ y, P.DualFeasible y ∧ d ≤ P.dualValue y := by
  classical
  let Q := P.toFin
  have hQfeas : EconCSLib.LinearProgramming.PrimalFeasible Q.A Q.b := by
    obtain ⟨x, hx⟩ := hfeas
    let xf : Fin (Fintype.card Col) → ℝ :=
      fun j => x ((Fintype.equivFin Col).symm j)
    have hQ : Q.PrimalFeasible xf := by
      apply (P.toFin_primal_iff xf).2
      simpa [xf] using hx
    exact ⟨xf, hQ.2, hQ.1⟩
  have hQbound : ∀ xf : Fin (Fintype.card Col) → ℝ,
      (∀ i, Q.b i ≤ ∑ j, Q.A i j * xf j) →
      (∀ j, 0 ≤ xf j) →
      d ≤ ∑ j, Q.c j * xf j := by
    intro xf hrows hnn
    have hQ : Q.PrimalFeasible xf := ⟨hnn, hrows⟩
    have hP := (P.toFin_primal_iff xf).1 hQ
    change d ≤ Q.primalValue xf
    rw [P.toFin_primalValue xf]
    exact hbound _ hP
  obtain ⟨y, hy, hval⟩ :=
    EconCSLib.LinearProgramming.lp_strong_duality Q.A Q.b Q.c d hQfeas hQbound
  have hyQ : Q.DualFeasible y := by
    refine ⟨hy.1, fun j => ?_⟩
    simpa only [mul_comm] using hy.2 j
  refine ⟨y, (P.toFin_dual_iff y).1 hyQ, ?_⟩
  simpa [Q, toFin, dualValue, mul_comm] using hval

/-- Under positive costs, a feasible LP has attained equal primal and dual optima. -/
theorem exists_primal_dual_optima (hc : ∀ j, 0 < P.c j)
    {x₀ : Col → ℝ} (hx₀ : P.PrimalFeasible x₀) :
    ∃ x y, P.PrimalFeasible x ∧ P.DualFeasible y ∧
      P.primalValue x = P.dualValue y := by
  obtain ⟨x, hx, hmin⟩ := P.exists_primal_minimizer hc hx₀
  obtain ⟨y, hy, hge⟩ :=
    P.exists_dual_ge (P.primalValue x) ⟨x, hx⟩ hmin
  exact ⟨x, y, hx, hy, le_antisymm hge (P.weak_duality hx hy)⟩
end Problem

end HadwigerLean.FiniteLP
