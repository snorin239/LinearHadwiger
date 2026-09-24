import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

/-!
# Finite independent Bernoulli marking

An elementary finite probability space for independent marks indexed by an arbitrary finite type.
The index can be the edge-copy type of an indexed multihypergraph, so repeated edges remain
independent. Probabilities and expectations are finite real sums.
-/

namespace HadwigerLean.FiniteBernoulli

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Probability weight of one configuration of independent Bernoulli marks. -/
noncomputable def weight (p : ι → ℝ) (ω : ι → Bool) : ℝ :=
  ∏ i, if ω i then p i else 1 - p i

/-- Probability of an event in the finite Bernoulli product space. -/
noncomputable def prob (p : ι → ℝ) (A : Set (ι → Bool)) : ℝ := by
  classical
  exact ∑ ω, if ω ∈ A then weight p ω else 0

/-- Expectation in the finite Bernoulli product space. -/
noncomputable def expect (p : ι → ℝ) (X : (ι → Bool) → ℝ) : ℝ := by
  classical
  exact ∑ ω, weight p ω * X ω

theorem sum_weight (p : ι → ℝ) : (∑ ω : ι → Bool, weight p ω) = 1 := by
  classical
  calc
    (∑ ω : ι → Bool, weight p ω) =
        ∏ i, ∑ b : Bool, if b then p i else 1 - p i := by
      simpa only [weight] using
        (Fintype.prod_sum (fun i (b : Bool) => if b then p i else 1 - p i)).symm
    _ = 1 := by simp

omit [DecidableEq ι] in
theorem weight_nonneg (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (ω : ι → Bool) : 0 ≤ weight p ω := by
  classical
  apply Finset.prod_nonneg
  intro i hi
  split_ifs
  · exact (hp i).1
  · linarith [(hp i).2]

theorem prob_nonneg (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (A : Set (ι → Bool)) : 0 ≤ prob p A := by
  classical
  unfold prob
  apply Finset.sum_nonneg
  intro ω hω
  split_ifs with h
  · exact weight_nonneg p hp ω
  · exact le_rfl

/-- Exact factorization of an expectation of coordinate-wise factors. -/
theorem expect_prod (p : ι → ℝ) (f : ι → Bool → ℝ) :
    expect p (fun ω => ∏ i, f i (ω i)) =
      ∏ i, (p i * f i true + (1 - p i) * f i false) := by
  classical
  calc
    expect p (fun ω => ∏ i, f i (ω i)) =
        ∑ ω : ι → Bool, ∏ i, (if ω i then p i else 1 - p i) * f i (ω i) := by
      simp only [expect, weight, Finset.prod_mul_distrib]
    _ = ∏ i, ∑ b : Bool, (if b then p i else 1 - p i) * f i b := by
      simpa only using
        (Fintype.prod_sum
          (fun i (b : Bool) => (if b then p i else 1 - p i) * f i b)).symm
    _ = ∏ i, (p i * f i true + (1 - p i) * f i false) := by
      simp

/-- Probability that all marks in a specified finite set are absent. -/
theorem prob_all_false (p : ι → ℝ) (S : Finset ι) :
    prob p {ω | ∀ i ∈ S, ω i = false} = ∏ i ∈ S, (1 - p i) := by
  classical
  let f : ι → Bool → ℝ := fun i b => if i ∈ S then (if b then 0 else 1) else 1
  have hind (ω : ι → Bool) :
      (if (∀ i ∈ S, ω i = false) then (1 : ℝ) else 0) = ∏ i, f i (ω i) := by
    by_cases h : ∀ i ∈ S, ω i = false
    · rw [if_pos h]
      symm
      apply Finset.prod_eq_one
      intro i hi
      by_cases hS : i ∈ S
      · simp [f, hS, h i hS]
      · simp [f, hS]
    · obtain ⟨i, hi, hω⟩ : ∃ i ∈ S, ω i = true := by
        by_contra hx
        apply h
        intro j hj
        cases hjω : ω j
        · simp
        · exact False.elim (hx ⟨j, hj, hjω⟩)
      have hz : f i (ω i) = 0 := by simp [f, hi, hω]
      rw [if_neg h]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) hz).symm
  calc
    prob p {ω | ∀ i ∈ S, ω i = false} =
        expect p (fun ω => ∏ i, f i (ω i)) := by
      unfold prob expect
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : ∀ i ∈ S, ω i = false
      · have hf : (∏ i, f i (ω i)) = 1 := by rw [← hind ω, if_pos h]
        have hmem : ω ∈ {ω | ∀ i ∈ S, ω i = false} := h
        simp only [if_pos hmem, hf, mul_one]
      · have hf : (∏ i, f i (ω i)) = 0 := by rw [← hind ω, if_neg h]
        have hmem : ω ∉ {ω | ∀ i ∈ S, ω i = false} := h
        simp only [if_neg hmem, hf, mul_zero]
    _ = ∏ i, (p i * f i true + (1 - p i) * f i false) :=
      expect_prod p f
    _ = ∏ i, (if i ∈ S then 1 - p i else 1) := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hS : i ∈ S
      · simp [f, hS]
      · simp only [f, if_neg hS, mul_one]
        ring
    _ = ∏ i ∈ S, (1 - p i) := by simp [Finset.prod_ite_mem]

/-- Bernoulli mark probability with Poisson zero probability exp(-rate). -/
noncomputable def expMarkProbability (rate : ι → ℝ) (i : ι) : ℝ :=
  1 - Real.exp (-rate i)

omit [Fintype ι] [DecidableEq ι] in
theorem expMarkProbability_bounds (rate : ι → ℝ) (hrate : ∀ i, 0 ≤ rate i)
    (i : ι) : 0 ≤ expMarkProbability rate i ∧ expMarkProbability rate i ≤ 1 := by
  have h₁ : Real.exp (-rate i) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hrate i))
  have h₂ : 0 < Real.exp (-rate i) := Real.exp_pos _
  unfold expMarkProbability
  constructor <;> linarith

/-- Exact joint survival probability under Poisson-zero Bernoulli marks. -/
theorem prob_all_false_exp (rate : ι → ℝ) (S : Finset ι) :
    prob (expMarkProbability rate) {ω | ∀ i ∈ S, ω i = false} =
      Real.exp (-(∑ i ∈ S, rate i)) := by
  rw [prob_all_false]
  calc
    (∏ i ∈ S, (1 - expMarkProbability rate i)) =
        ∏ i ∈ S, Real.exp (-rate i) := by
      apply Finset.prod_congr rfl
      intro i hi
      unfold expMarkProbability
      ring
    _ = Real.exp (∑ i ∈ S, -rate i) := (Real.exp_sum S (fun i => -rate i)).symm
    _ = Real.exp (-(∑ i ∈ S, rate i)) := by rw [Finset.sum_neg_distrib]

/-- Number of present marks in a finite set, as a real number. -/
noncomputable def count (S : Finset ι) (ω : ι → Bool) : ℝ :=
  ∑ i ∈ S, if ω i then 1 else 0

/-- Mean number of present marks in a finite set. -/
noncomputable def mean (p : ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ i ∈ S, p i

/-- Expected value of a single Bernoulli mark. -/
theorem expect_mark (p : ι → ℝ) (i : ι) :
    expect p (fun ω => if ω i then 1 else 0) = p i := by
  classical
  let f : ι → Bool → ℝ := fun j b => if j = i then (if b then 1 else 0) else 1
  have hrepr (ω : ι → Bool) :
      (if ω i then (1 : ℝ) else 0) = ∏ j, f j (ω j) := by
    simp [f]
  calc
    expect p (fun ω => if ω i then 1 else 0) =
        expect p (fun ω => ∏ j, f j (ω j)) := by
      congr 1
      funext ω
      exact hrepr ω
    _ = ∏ j, (p j * f j true + (1 - p j) * f j false) := expect_prod p f
    _ = p i := by
      have hfactor (j : ι) :
          p j * f j true + (1 - p j) * f j false =
            if j = i then p i else 1 := by
        by_cases h : j = i
        · subst j
          simp [f]
        · simp only [f, if_neg h, mul_one]
          ring
      simp_rw [hfactor]
      simp [Finset.prod_ite_eq']

theorem expect_count (p : ι → ℝ) (S : Finset ι) :
    expect p (count S) = mean p S := by
  classical
  unfold expect count mean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [expect] using expect_mark p i

omit [Fintype ι] [DecidableEq ι] in
/-- Exponential of a sampled count is a product of coordinate factors. -/
theorem exp_mul_count (S : Finset ι) (t : ℝ) (ω : ι → Bool) :
    Real.exp (t * count S ω) =
      ∏ i ∈ S, (if ω i then Real.exp t else 1) := by
  calc
    Real.exp (t * count S ω) =
        Real.exp (∑ i ∈ S, t * (if ω i then (1 : ℝ) else 0)) := by
      simp only [count, Finset.mul_sum]
    _ = ∏ i ∈ S, Real.exp (t * (if ω i then (1 : ℝ) else 0)) :=
      Real.exp_sum S _
    _ = ∏ i ∈ S, (if ω i then Real.exp t else 1) := by
      apply Finset.prod_congr rfl
      intro i hi
      cases h : ω i <;> simp

/-- Exact moment-generating function of the sampled count. -/
theorem expect_exp_count (p : ι → ℝ) (S : Finset ι) (t : ℝ) :
    expect p (fun ω => Real.exp (t * count S ω)) =
      ∏ i ∈ S, (1 - p i + p i * Real.exp t) := by
  classical
  let f : ι → Bool → ℝ :=
    fun i b => if i ∈ S then (if b then Real.exp t else 1) else 1
  have hrepr (ω : ι → Bool) :
      Real.exp (t * count S ω) = ∏ i, f i (ω i) := by
    rw [exp_mul_count]
    simp [f, Finset.prod_ite_mem]
  calc
    expect p (fun ω => Real.exp (t * count S ω)) =
        expect p (fun ω => ∏ i, f i (ω i)) := by
      congr 1
      funext ω
      exact hrepr ω
    _ = ∏ i, (p i * f i true + (1 - p i) * f i false) := expect_prod p f
    _ = ∏ i, (if i ∈ S then 1 - p i + p i * Real.exp t else 1) := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hS : i ∈ S
      · simp only [f, if_pos hS, Bool.false_eq_true, ↓reduceIte, mul_one]
        ring
      · simp only [f, if_neg hS, mul_one]
        ring
    _ = ∏ i ∈ S, (1 - p i + p i * Real.exp t) := by
      simp [Finset.prod_ite_mem]

/-- A mean-sensitive MGF bound for a finite Bernoulli sum. -/
theorem expect_exp_count_le (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset ι) (t : ℝ) :
    expect p (fun ω => Real.exp (t * count S ω)) ≤
      Real.exp (mean p S * (Real.exp t - 1)) := by
  rw [expect_exp_count]
  calc
    (∏ i ∈ S, (1 - p i + p i * Real.exp t)) =
        ∏ i ∈ S, (1 + p i * (Real.exp t - 1)) := by
      apply Finset.prod_congr rfl
      intro i hi
      ring
    _ ≤ ∏ i ∈ S, Real.exp (p i * (Real.exp t - 1)) := by
      apply Finset.prod_le_prod
      · intro i hi
        have h₁ : 0 ≤ 1 - p i := by linarith [(hp i).2]
        have h₂ : 0 ≤ p i * Real.exp t :=
          mul_nonneg (hp i).1 (Real.exp_pos t).le
        convert add_nonneg h₁ h₂ using 1; ring
      · intro i hi
        simpa [add_comm] using Real.add_one_le_exp (p i * (Real.exp t - 1))
    _ = Real.exp (∑ i ∈ S, p i * (Real.exp t - 1)) :=
      (Real.exp_sum S (fun i => p i * (Real.exp t - 1))).symm
    _ = Real.exp (mean p S * (Real.exp t - 1)) := by
      congr 1
      simp [mean, Finset.sum_mul]

/-- Finite weighted Markov inequality for an event and a nonnegative witness. -/
theorem prob_le_expect (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (A : Set (ι → Bool)) (X : (ι → Bool) → ℝ)
    (hX : ∀ ω, 0 ≤ X ω) (hA : ∀ ω ∈ A, 1 ≤ X ω) :
    prob p A ≤ expect p X := by
  classical
  unfold prob expect
  apply Finset.sum_le_sum
  intro ω hω
  by_cases h : ω ∈ A
  · simp only [if_pos h]
    have hw := weight_nonneg p hp ω
    have hx := hA ω h
    nlinarith
  · simp only [if_neg h]
    exact mul_nonneg (weight_nonneg p hp ω) (hX ω)

/-- Mean-sensitive Chernoff bound, with either tail selected by the sign of `t`. -/
theorem prob_count_chernoff (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset ι) (t threshold : ℝ) :
    prob p {ω | t * threshold ≤ t * count S ω} ≤
      Real.exp (-t * threshold + mean p S * (Real.exp t - 1)) := by
  let X : (ι → Bool) → ℝ :=
    fun ω => Real.exp (-t * threshold) * Real.exp (t * count S ω)
  have hX (ω : ι → Bool) : 0 ≤ X ω :=
    mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hA (ω : ι → Bool)
      (hω : ω ∈ {ω | t * threshold ≤ t * count S ω}) : 1 ≤ X ω := by
    have harg : 0 ≤ -t * threshold + t * count S ω := by
      dsimp at hω
      linarith
    calc
      (1 : ℝ) ≤ Real.exp (-t * threshold + t * count S ω) :=
        Real.one_le_exp harg
      _ = X ω := by rw [Real.exp_add]
  calc
    prob p {ω | t * threshold ≤ t * count S ω} ≤ expect p X :=
      prob_le_expect p hp _ X hX hA
    _ = Real.exp (-t * threshold) *
        expect p (fun ω => Real.exp (t * count S ω)) := by
      unfold expect X
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω hω
      ring
    _ ≤ Real.exp (-t * threshold) *
        Real.exp (mean p S * (Real.exp t - 1)) :=
      mul_le_mul_of_nonneg_left (expect_exp_count_le p hp S t) (Real.exp_pos _).le
    _ = Real.exp (-t * threshold + mean p S * (Real.exp t - 1)) := by
      rw [Real.exp_add]

theorem prob_mono (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    {A B : Set (ι → Bool)} (hAB : A ⊆ B) : prob p A ≤ prob p B := by
  classical
  unfold prob
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : ω ∈ A
  · have hB : ω ∈ B := hAB hA
    simp [hA, hB]
  · by_cases hB : ω ∈ B
    · simp only [if_neg hA, if_pos hB]
      exact weight_nonneg p hp ω
    · simp [hA, hB]

/-- Upper-tail Chernoff bound with a positive exponential parameter. -/
theorem prob_count_ge_chernoff (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset ι) (t threshold : ℝ) (ht : 0 ≤ t) :
    prob p {ω | threshold ≤ count S ω} ≤
      Real.exp (-t * threshold + mean p S * (Real.exp t - 1)) := by
  apply (prob_mono p hp ?_).trans (prob_count_chernoff p hp S t threshold)
  intro ω hω
  exact mul_le_mul_of_nonneg_left hω ht

/-- Lower-tail Chernoff bound with a negative exponential parameter. -/
theorem prob_count_le_chernoff (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset ι) (t threshold : ℝ) (ht : t ≤ 0) :
    prob p {ω | count S ω ≤ threshold} ≤
      Real.exp (-t * threshold + mean p S * (Real.exp t - 1)) := by
  apply (prob_mono p hp ?_).trans (prob_count_chernoff p hp S t threshold)
  intro ω hω
  exact mul_le_mul_of_nonpos_left hω ht

omit [Fintype ι] [DecidableEq ι] in
theorem mean_nonneg (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset ι) : 0 ≤ mean p S := by
  unfold mean
  exact Finset.sum_nonneg (fun i hi => (hp i).1)

/-- Quadratic Chernoff form for |t| ≤ 1. The exponent scales with the mean,
not the number of possible marks. -/
theorem prob_count_chernoff_quadratic (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (S : Finset ι)
    (t threshold : ℝ) (ht : |t| ≤ 1) :
    prob p {ω | t * threshold ≤ t * count S ω} ≤
      Real.exp (-t * threshold + mean p S * (t + t ^ 2)) := by
  have hTaylor := Real.abs_exp_sub_one_sub_id_le ht
  have hExp : Real.exp t - 1 ≤ t + t ^ 2 := by
    have h := (abs_le.mp hTaylor).2
    linarith
  have harg :
      -t * threshold + mean p S * (Real.exp t - 1) ≤
        -t * threshold + mean p S * (t + t ^ 2) := by
    linarith [mul_le_mul_of_nonneg_left hExp (mean_nonneg p hp S)]
  exact (prob_count_chernoff p hp S t threshold).trans
    (Real.exp_le_exp.mpr harg)

theorem prob_univ (p : ι → ℝ) : prob p Set.univ = 1 := by
  classical
  simpa [prob] using sum_weight p

theorem prob_union_le (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (A B : Set (ι → Bool)) :
    prob p (A ∪ B) ≤ prob p A + prob p B := by
  classical
  unfold prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;>
    simp [hA, hB]; nlinarith [weight_nonneg p hp ω]

/-- Union bound over a finite family of bad events. -/
theorem prob_biUnion_le {κ : Type*} (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (s : Finset κ) (A : κ → Set (ι → Bool)) :
    prob p (⋃ j ∈ s, A j) ≤ ∑ j ∈ s, prob p (A j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [prob]
  | @insert j s hjs ih =>
      have hset : (⋃ k ∈ insert j s, A k) = A j ∪ ⋃ k ∈ s, A k := by
        ext ω
        simp
      rw [hset, Finset.sum_insert hjs]
      have hUnion := prob_union_le p hp (A j) (⋃ k ∈ s, A k)
      linarith

/-- If a bad event has probability less than one, some configuration avoids it. -/
theorem exists_not_mem_of_prob_lt_one (p : ι → ℝ)
    (A : Set (ι → Bool)) (hA : prob p A < 1) :
    ∃ ω, ω ∉ A := by
  by_contra h
  have hfull : A = Set.univ := by
    ext ω
    simp only [Set.mem_univ, iff_true]
    by_contra hω
    exact h ⟨ω, hω⟩
  rw [hfull, prob_univ] at hA
  exact (lt_irrefl (1 : ℝ)) hA

/-- Real indicator of an event in the finite sample space. -/
noncomputable def eventIndicator (A : Set (ι → Bool)) (ω : ι → Bool) : ℝ := by
  classical
  exact if ω ∈ A then 1 else 0

theorem expect_eventIndicator (p : ι → ℝ) (A : Set (ι → Bool)) :
    expect p (eventIndicator A) = prob p A := by
  classical
  unfold expect prob eventIndicator
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases h : ω ∈ A <;> simp [h]

/-- Finite linearity of expectation. -/
theorem expect_sum {κ : Type*} (p : ι → ℝ) (s : Finset κ)
    (X : κ → (ι → Bool) → ℝ) :
    expect p (fun ω => ∑ j ∈ s, X j ω) =
      ∑ j ∈ s, expect p (X j) := by
  classical
  unfold expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Probability that every mark in a finite set is present. -/
theorem prob_all_true (p : ι → ℝ) (S : Finset ι) :
    prob p {ω | ∀ i ∈ S, ω i = true} = ∏ i ∈ S, p i := by
  classical
  let f : ι → Bool → ℝ := fun i b => if i ∈ S then (if b then 1 else 0) else 1
  have hind (ω : ι → Bool) :
      (if (∀ i ∈ S, ω i = true) then (1 : ℝ) else 0) = ∏ i, f i (ω i) := by
    by_cases h : ∀ i ∈ S, ω i = true
    · rw [if_pos h]
      symm
      apply Finset.prod_eq_one
      intro i hi
      by_cases hS : i ∈ S
      · simp [f, hS, h i hS]
      · simp [f, hS]
    · obtain ⟨i, hi, hω⟩ : ∃ i ∈ S, ω i = false := by
        by_contra hx
        apply h
        intro j hj
        cases hjω : ω j
        · exact False.elim (hx ⟨j, hj, hjω⟩)
        · simp
      have hz : f i (ω i) = 0 := by simp [f, hi, hω]
      rw [if_neg h]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) hz).symm
  calc
    prob p {ω | ∀ i ∈ S, ω i = true} =
        expect p (fun ω => ∏ i, f i (ω i)) := by
      unfold prob expect
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : ∀ i ∈ S, ω i = true
      · have hf : (∏ i, f i (ω i)) = 1 := by rw [← hind ω, if_pos h]
        have hmem : ω ∈ {ω | ∀ i ∈ S, ω i = true} := h
        simp only [if_pos hmem, hf, mul_one]
      · have hf : (∏ i, f i (ω i)) = 0 := by rw [← hind ω, if_neg h]
        have hmem : ω ∉ {ω | ∀ i ∈ S, ω i = true} := h
        simp only [if_neg hmem, hf, mul_zero]
    _ = ∏ i, (p i * f i true + (1 - p i) * f i false) :=
      expect_prod p f
    _ = ∏ i, (if i ∈ S then p i else 1) := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hS : i ∈ S
      · simp [f, hS]
      · simp only [f, if_neg hS, mul_one]
        ring
    _ = ∏ i ∈ S, p i := by simp [Finset.prod_ite_mem]

/-- Two distinct marks occur jointly with the product of their probabilities. -/
theorem prob_two_true (p : ι → ℝ) {i j : ι} (hij : i ≠ j) :
    prob p {ω | ω i = true ∧ ω j = true} = p i * p j := by
  classical
  have hset :
      {ω : ι → Bool | ω i = true ∧ ω j = true} =
        {ω | ∀ k ∈ ({i, j} : Finset ι), ω k = true} := by
    ext ω
    simp
  rw [hset, prob_all_true]
  simp [hij]

end HadwigerLean.FiniteBernoulli
























namespace HadwigerLean.FiniteBernoulli

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Finite weighted Cauchy–Schwarz: the mean absolute value is bounded by
the square root of the second moment. -/
theorem expect_abs_le_sqrt_expect_sq (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (X : (ι → Bool) → ℝ) :
    expect p (fun ω => |X ω|) ≤
      Real.sqrt (expect p (fun ω => (X ω)^2)) := by
  classical
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := (Finset.univ : Finset (ι → Bool)))
    (r := fun ω => weight p ω * |X ω|)
    (f := fun ω => weight p ω)
    (g := fun ω => weight p ω * (X ω)^2)
    (fun ω hω => weight_nonneg p hp ω)
    (fun ω hω => mul_nonneg (weight_nonneg p hp ω) (sq_nonneg _))
    (fun ω hω => by rw [mul_pow, sq_abs]; nlinarith)
  have hsq : (expect p (fun ω => |X ω|))^2 ≤
      expect p (fun ω => (X ω)^2) := by
    change (∑ ω : ι → Bool, weight p ω * |X ω|)^2 ≤
      ∑ ω : ι → Bool, weight p ω * (X ω)^2
    simpa only [sum_weight p, one_mul] using hcs
  have hnonneg : 0 ≤ expect p (fun ω => |X ω|) := by
    unfold expect
    exact Finset.sum_nonneg (fun ω hω =>
      mul_nonneg (weight_nonneg p hp ω) (abs_nonneg _))
  have hsqrt := Real.sqrt_le_sqrt hsq
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg] using hsqrt

end HadwigerLean.FiniteBernoulli




namespace HadwigerLean.FiniteBernoulli

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A centered upper-tail bound using a cap on the mean. -/
theorem prob_count_ge_mean_add (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (S : Finset ι)
    (D s : ℝ) (hD : 0 < D) (hs : 0 ≤ s) (hsD : s ≤ 2 * D)
    (hmean : mean p S ≤ D) :
    prob p {ω | mean p S + s ≤ count S ω} ≤
      Real.exp (-(s ^ 2) / (4 * D)) := by
  let t := s / (2 * D)
  have ht : 0 ≤ t := div_nonneg hs (by positivity)
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < 2 * D)).2
    linarith
  have htAbs : |t| ≤ 1 := by simpa [abs_of_nonneg ht] using ht1
  have hbase := prob_count_chernoff_quadratic p hp S t (mean p S + s) htAbs
  have hsubset :
      {ω | mean p S + s ≤ count S ω} ⊆
        {ω | t * (mean p S + s) ≤ t * count S ω} := by
    intro ω hω
    exact mul_le_mul_of_nonneg_left hω ht
  have hfirst := (prob_mono p hp hsubset).trans hbase
  have harg :
      -t * (mean p S + s) + mean p S * (t + t ^ 2) ≤
        -(s ^ 2) / (4 * D) := by
    have hsq := mul_le_mul_of_nonneg_right hmean (sq_nonneg t)
    have hid :
        -t * (mean p S + s) + mean p S * (t + t ^ 2) =
          -t * s + mean p S * t ^ 2 := by ring
    have hcalc : -t * s + D * t ^ 2 = -(s ^ 2) / (4 * D) := by
      dsimp [t]
      field_simp
      ring
    rw [hid]
    rw [← hcalc]
    linarith
  exact hfirst.trans (Real.exp_le_exp.mpr harg)

end HadwigerLean.FiniteBernoulli
namespace HadwigerLean.FiniteBernoulli

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A centered lower-tail bound using a cap on the mean. -/
theorem prob_count_le_mean_sub (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (S : Finset ι)
    (D s : ℝ) (hD : 0 < D) (hs : 0 ≤ s) (hsD : s ≤ 2 * D)
    (hmean : mean p S ≤ D) :
    prob p {ω | count S ω ≤ mean p S - s} ≤
      Real.exp (-(s ^ 2) / (4 * D)) := by
  let t := -(s / (2 * D))
  have ht : t ≤ 0 := by
    dsimp [t]
    exact neg_nonpos.mpr (div_nonneg hs (by positivity))
  have htAbs : |t| ≤ 1 := by
    have hbound : s / (2 * D) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * D)).2
      linarith
    change |-(s / (2 * D))| ≤ 1
    rw [abs_neg, abs_of_nonneg (div_nonneg hs (by positivity))]
    exact hbound
  have hbase := prob_count_chernoff_quadratic p hp S t (mean p S - s) htAbs
  have hsubset :
      {ω | count S ω ≤ mean p S - s} ⊆
        {ω | t * (mean p S - s) ≤ t * count S ω} := by
    intro ω hω
    exact mul_le_mul_of_nonpos_left hω ht
  have hfirst := (prob_mono p hp hsubset).trans hbase
  have harg :
      -t * (mean p S - s) + mean p S * (t + t ^ 2) ≤
        -(s ^ 2) / (4 * D) := by
    have hsq := mul_le_mul_of_nonneg_right hmean (sq_nonneg t)
    have hid :
        -t * (mean p S - s) + mean p S * (t + t ^ 2) =
          t * s + mean p S * t ^ 2 := by ring
    have hcalc : t * s + D * t ^ 2 = -(s ^ 2) / (4 * D) := by
      dsimp [t]
      field_simp
      ring
    rw [hid]
    rw [← hcalc]
    linarith
  exact hfirst.trans (Real.exp_le_exp.mpr harg)

end HadwigerLean.FiniteBernoulli

namespace HadwigerLean.FiniteBernoulli

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If the mean is at most half the threshold, a fixed exponential tilt
gives an exponentially small upper tail. -/
theorem prob_count_ge_of_mean_le_half (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (S : Finset ι)
    (C : ℝ) (hmean : mean p S ≤ C / 2) :
    prob p {ω | C ≤ count S ω} ≤ Real.exp (-C / 8) := by
  have hbase := prob_count_chernoff_quadratic p hp S (1 / 2) C (by norm_num)
  have hsubset :
      {ω | C ≤ count S ω} ⊆
        {ω | (1 / 2 : ℝ) * C ≤ (1 / 2 : ℝ) * count S ω} := by
    intro ω hω
    change C ≤ count S ω at hω
    exact mul_le_mul_of_nonneg_left hω (by norm_num)
  have hfirst := (prob_mono p hp hsubset).trans hbase
  have harg :
      -(1 / 2 : ℝ) * C + mean p S * ((1 / 2 : ℝ) + (1 / 2 : ℝ) ^ 2) ≤
        -C / 8 := by
    linarith
  exact hfirst.trans (Real.exp_le_exp.mpr harg)

end HadwigerLean.FiniteBernoulli
