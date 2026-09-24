import HadwigerLean.Coloring.Fractional
import HadwigerLean.Optimization.FiniteLP
import Mathlib.Tactic.Linarith

/-!
# Pair loads in fractional colorings

In the paper's rounding lemma, a pair has load
`∑_{S ⊇ {u,v}} x_S`.  The augmentation LP (equation `eq:pairlp`) bounds
this load by `μ / 4` for each distinct pair.  We use a general tolerance
`δ`; the intended later specialization is `δ = μ / 4`.

Only nonedge pairs need LP rows: no stable set contains an edge.  We index
these rows by two-element independent `Finset`s, so an unordered pair occurs
once.  A pair-load upper bound is a covering LP row with both sides negated.
-/

namespace HadwigerLean

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An unordered nonedge pair, represented by a two-element independent set. -/
abbrev NonedgePair (G : SimpleGraph V) :=
  {p : Finset V // p.card = 2 ∧ G.IsIndepSet (p : Set V)}

noncomputable instance nonedgePairFintype (G : SimpleGraph V) :
    Fintype (NonedgePair G) := by
  classical
  infer_instance

/-- Weight of stable sets containing all vertices of `p`.  In applications
`p` is a two-element set. -/
noncomputable def pairLoad (G : SimpleGraph V) (x : StableSet G → ℝ)
    (p : Finset V) : ℝ :=
  ∑ S : StableSet G, if p ⊆ S.1 then x S else 0

theorem pairLoad_pair (G : SimpleGraph V) (x : StableSet G → ℝ) (u v : V) :
    pairLoad G x {u, v} =
      ∑ S : StableSet G, if u ∈ S.1 ∧ v ∈ S.1 then x S else 0 := by
  classical
  unfold pairLoad
  apply Finset.sum_congr rfl
  intro S _
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]

theorem pairLoad_nonneg (G : SimpleGraph V) {x : StableSet G → ℝ}
    (hx : ∀ S, 0 ≤ x S) (p : Finset V) : 0 ≤ pairLoad G x p := by
  classical
  unfold pairLoad
  apply Finset.sum_nonneg
  intro S _
  split_ifs
  · exact hx S
  · exact le_rfl

/-- Equation `eq:pairlp`'s primal feasibility, at tolerance `δ`. -/
def IsPairConstrainedColoring (G : SimpleGraph V) (δ : ℝ)
    (x : StableSet G → ℝ) : Prop :=
  IsFractionalColoring G x ∧ ∀ p : NonedgePair G, pairLoad G x p.1 ≤ δ

theorem pairLoad_singletonFractionalColoring (G : SimpleGraph V)
    (p : NonedgePair G) :
    pairLoad G (singletonFractionalColoring G) p.1 = 0 := by
  classical
  unfold pairLoad
  apply Finset.sum_eq_zero
  intro S _
  by_cases hp : p.1 ⊆ S.1
  · have hcard : S.1.card ≠ 1 := by
      have hle := Finset.card_le_card hp
      have hp_card := p.property.1
      intro hcard
      rw [hp_card, hcard] at hle
      norm_num at hle
    simp [hp, singletonFractionalColoring, hcard]
  · simp [hp]

/-- Singletons prove feasibility of the pair-constrained LP for `δ ≥ 0`. -/
theorem singleton_isPairConstrainedColoring (G : SimpleGraph V)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    IsPairConstrainedColoring G δ (singletonFractionalColoring G) := by
  refine ⟨singletonFractionalColoring_feasible G, ?_⟩
  intro p
  rw [pairLoad_singletonFractionalColoring]
  exact hδ

/-- The pair-constrained coloring LP, with vertex covering rows and negated
pair-load rows.  Its dual has a nonnegative vertex price and a nonnegative
pair penalty, exactly as in equation `eq:pairdual` of the paper. -/
noncomputable def pairProblem (G : SimpleGraph V) (δ : ℝ) :
    FiniteLP.Problem (V ⊕ NonedgePair G) (StableSet G) where
  A row S := match row with
    | Sum.inl v => if v ∈ S.1 then 1 else 0
    | Sum.inr p => if p.1 ⊆ S.1 then -1 else 0
  b row := match row with
    | Sum.inl _ => 1
    | Sum.inr _ => -δ
  c _ := 1

private theorem pairProblem_vertexRow (G : SimpleGraph V) (δ : ℝ)
    (x : StableSet G → ℝ) (v : V) :
    (∑ S, (pairProblem G δ).A (Sum.inl v) S * x S) = vertexLoad G x v := by
  classical
  simp [pairProblem, vertexLoad]

private theorem pairProblem_pairRow (G : SimpleGraph V) (δ : ℝ)
    (x : StableSet G → ℝ) (p : NonedgePair G) :
    (∑ S, (pairProblem G δ).A (Sum.inr p) S * x S) =
      -pairLoad G x p.1 := by
  classical
  simp only [pairProblem, pairLoad]
  calc
    (∑ S : StableSet G, (if p.1 ⊆ S.1 then (-1 : ℝ) else 0) * x S) =
        ∑ S : StableSet G, -(if p.1 ⊆ S.1 then x S else 0) := by
      apply Finset.sum_congr rfl
      intro S _
      split_ifs <;> ring
    _ = -(∑ S : StableSet G, if p.1 ⊆ S.1 then x S else 0) := by
      rw [Finset.sum_neg_distrib]

/-- The LP primal predicate is exactly the paper's pair-constrained
fractional-coloring predicate. -/
theorem pairProblem_primal_iff (G : SimpleGraph V) (δ : ℝ)
    (x : StableSet G → ℝ) :
    (pairProblem G δ).PrimalFeasible x ↔ IsPairConstrainedColoring G δ x := by
  constructor
  · intro hx
    refine ⟨⟨hx.1, ?_⟩, ?_⟩
    · intro v
      have h := hx.2 (Sum.inl v)
      change (1 : ℝ) ≤ ∑ S, (pairProblem G δ).A (Sum.inl v) S * x S at h
      rw [pairProblem_vertexRow] at h
      exact h
    · intro p
      have h := hx.2 (Sum.inr p)
      change -δ ≤ ∑ S, (pairProblem G δ).A (Sum.inr p) S * x S at h
      rw [pairProblem_pairRow] at h
      linarith
  · intro hx
    refine ⟨hx.1.1, ?_⟩
    intro row
    cases row with
    | inl v =>
        change (1 : ℝ) ≤ ∑ S, (pairProblem G δ).A (Sum.inl v) S * x S
        rw [pairProblem_vertexRow]
        exact hx.1.2 v
    | inr p =>
        change -δ ≤ ∑ S, (pairProblem G δ).A (Sum.inr p) S * x S
        rw [pairProblem_pairRow]
        linarith [hx.2 p]

theorem pairProblem_primalValue (G : SimpleGraph V) (δ : ℝ)
    (x : StableSet G → ℝ) :
    (pairProblem G δ).primalValue x = fractionalCost G x := by
  classical
  simp [FiniteLP.Problem.primalValue, pairProblem, fractionalCost]

/-- The paper's dual constraint: vertex prices are offset by penalties
for nonedge pairs contained in a stable set. -/
def IsPairDualFeasible (G : SimpleGraph V) (a : V → ℝ)
    (b : NonedgePair G → ℝ) : Prop :=
  (∀ v, 0 ≤ a v) ∧ (∀ p, 0 ≤ b p) ∧
    ∀ S : StableSet G,
      (∑ v ∈ S.1, a v) -
        (∑ p : NonedgePair G, if p.1 ⊆ S.1 then b p else 0) ≤ 1

/-- The objective in equation eq:pairdual, with δ = μ / 4. -/
noncomputable def pairDualValue (G : SimpleGraph V) (δ : ℝ)
    (a : V → ℝ) (b : NonedgePair G → ℝ) : ℝ :=
  (∑ v, a v) - δ * ∑ p, b p

private theorem pairProblem_dualColumn (G : SimpleGraph V) (δ : ℝ)
    (y : V ⊕ NonedgePair G → ℝ) (S : StableSet G) :
    (∑ row, (pairProblem G δ).A row S * y row) =
      (∑ v ∈ S.1, y (Sum.inl v)) -
        (∑ p : NonedgePair G, if p.1 ⊆ S.1 then y (Sum.inr p) else 0) := by
  classical
  rw [Fintype.sum_sum_type]
  simp [pairProblem, sub_eq_add_neg]
  calc
    (∑ p : NonedgePair G, if p.1 ⊆ S.1 then -y (Sum.inr p) else 0) =
        ∑ p : NonedgePair G, -(if p.1 ⊆ S.1 then y (Sum.inr p) else 0) := by
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring
    _ = -(∑ p : NonedgePair G,
        if p.1 ⊆ S.1 then y (Sum.inr p) else 0) := by
      rw [Finset.sum_neg_distrib]

/-- The generic LP dual predicate is exactly equation eq:pairdual. -/
theorem pairProblem_dual_iff (G : SimpleGraph V) (δ : ℝ)
    (y : V ⊕ NonedgePair G → ℝ) :
    (pairProblem G δ).DualFeasible y ↔
      IsPairDualFeasible G (fun v => y (Sum.inl v))
        (fun p => y (Sum.inr p)) := by
  constructor
  · intro hy
    refine ⟨fun v => hy.1 (Sum.inl v), fun p => hy.1 (Sum.inr p), ?_⟩
    intro S
    have h := hy.2 S
    rw [pairProblem_dualColumn] at h
    exact h
  · intro hy
    refine ⟨?_, ?_⟩
    · intro row
      cases row with
      | inl v => exact hy.1 v
      | inr p => exact hy.2.1 p
    · intro S
      rw [pairProblem_dualColumn]
      exact hy.2.2 S

theorem pairProblem_dualValue (G : SimpleGraph V) (δ : ℝ)
    (y : V ⊕ NonedgePair G → ℝ) :
    (pairProblem G δ).dualValue y =
      pairDualValue G δ (fun v => y (Sum.inl v))
        (fun p => y (Sum.inr p)) := by
  classical
  simp [FiniteLP.Problem.dualValue, pairProblem, pairDualValue,
    Fintype.sum_sum_type, Finset.mul_sum, Finset.sum_neg_distrib,
    sub_eq_add_neg]
/-- The pair-constrained coloring cost attains its minimum for `δ ≥ 0`. -/
theorem exists_pairConstrained_minimizer (G : SimpleGraph V)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ x, IsPairConstrainedColoring G δ x ∧
      ∀ y, IsPairConstrainedColoring G δ y →
        fractionalCost G x ≤ fractionalCost G y := by
  have hpositive : ∀ S : StableSet G, 0 < (pairProblem G δ).c S := by
    intro S
    change (0 : ℝ) < 1
    norm_num
  have hfeasible : (pairProblem G δ).PrimalFeasible
      (singletonFractionalColoring G) :=
    (pairProblem_primal_iff G δ _).2 (singleton_isPairConstrainedColoring G hδ)
  obtain ⟨x, hx, hmin⟩ :=
    (pairProblem G δ).exists_primal_minimizer hpositive hfeasible
  refine ⟨x, (pairProblem_primal_iff G δ x).1 hx, ?_⟩
  intro y hy
  have h := hmin y ((pairProblem_primal_iff G δ y).2 hy)
  simpa only [pairProblem_primalValue] using h

/-- Attained strong duality for the pair-constrained coloring LP.  This is
equations eq:pairlp and eq:pairdual with δ specialized later to μ / 4. -/
theorem exists_pairConstrained_primal_dual_optima (G : SimpleGraph V)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ x a b, IsPairConstrainedColoring G δ x ∧
      IsPairDualFeasible G a b ∧
      fractionalCost G x = pairDualValue G δ a b := by
  have hpositive : ∀ S : StableSet G, 0 < (pairProblem G δ).c S := by
    intro S
    change (0 : ℝ) < 1
    norm_num
  have hfeasible : (pairProblem G δ).PrimalFeasible
      (singletonFractionalColoring G) :=
    (pairProblem_primal_iff G δ _).2 (singleton_isPairConstrainedColoring G hδ)
  obtain ⟨x, y, hx, hy, heq⟩ :=
    (pairProblem G δ).exists_primal_dual_optima hpositive hfeasible
  refine ⟨x, (fun v => y (Sum.inl v)), (fun p => y (Sum.inr p)),
    (pairProblem_primal_iff G δ x).1 hx,
    (pairProblem_dual_iff G δ y).1 hy, ?_⟩
  calc
    fractionalCost G x = (pairProblem G δ).primalValue x :=
      (pairProblem_primalValue G δ x).symm
    _ = (pairProblem G δ).dualValue y := heq
    _ = pairDualValue G δ (fun v => y (Sum.inl v))
        (fun p => y (Sum.inr p)) := pairProblem_dualValue G δ y
end HadwigerLean
