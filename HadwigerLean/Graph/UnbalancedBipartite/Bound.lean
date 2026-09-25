import HadwigerLean.Graph.UnbalancedBipartite.NearComplete
import HadwigerLean.Graph.CliqueDensity.Theorem
import HadwigerLean.Graph.DensityBasic
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# The unbalanced bipartite clique-minor bound

Appendix C's edge estimate is proved by a minimal-counterexample argument.
This file collects the quantitative ingredients and the final statement.
-/

namespace HadwigerLean

/-- The contrapositive form of the checked coefficient-30 density theorem. -/
theorem edgeCount_lt_kt_threshold_of_no_clique_minor
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : ℕ) (ht : 2 ≤ t) (hminor : ¬ HasCliqueMinor G t)
    (hcard : 0 < Fintype.card V) :
    (edgeCount G : ℝ) <
      30 * (t : ℝ) * Real.sqrt (Real.log (t : ℝ)) *
        (Fintype.card V : ℝ) := by
  have hdensity : edgeDensity G <
      30 * (t : ℝ) * Real.sqrt (Real.log (t : ℝ)) := by
    by_contra h
    exact hminor (hasCliqueMinor_of_edgeDensity_ge G t ht (le_of_not_gt h))
  have hpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast hcard
  have h := mul_lt_mul_of_pos_right hdensity hpos
  rw [edgeDensity, div_mul_cancel₀ _ (ne_of_gt hpos)] at h
  simpa [mul_assoc] using h


/-- Every edge of a bipartite graph is counted once by a left-side degree. -/
theorem edgeCount_eq_sum_degrees_left
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hG : G.IsBipartiteWith (A : Set V) (B : Set V)) :
    edgeCount G = ∑ v ∈ A, G.degree v := by
  simpa only [edgeCount_eq_card_edgeFinset] using
    (G.isBipartiteWith_sum_degrees_eq_card_edges
      (s := A) (t := B) hG).symm

/-- A bipartite graph has at most the complete bipartite edge count. -/
theorem edgeCount_le_card_mul_card_bipartite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hG : G.IsBipartiteWith (A : Set V) (B : Set V)) :
    edgeCount G ≤ A.card * B.card := by
  rw [edgeCount_eq_sum_degrees_left G A B hG]
  calc
    (∑ v ∈ A, G.degree v) ≤ ∑ _v ∈ A, B.card := by
      apply Finset.sum_le_sum
      intro v hv
      exact G.isBipartiteWith_degree_le hG hv
    _ = A.card * B.card := by simp

/-- Strictly sub-average degree occurs on the left whenever the total edge
count lies below a proposed left-side degree threshold. -/
theorem exists_left_degree_lt_of_edgeCount_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hA : A.Nonempty) (d : ℝ)
    (hedges : (edgeCount G : ℝ) < (A.card : ℝ) * d) :
    ∃ v ∈ A, (G.degree v : ℝ) < d := by
  have hsum : (∑ v ∈ A, (G.degree v : ℝ)) = (edgeCount G : ℝ) := by
    exact_mod_cast (edgeCount_eq_sum_degrees_left G A B hG).symm
  have hlt : (∑ v ∈ A, (G.degree v : ℝ)) < ∑ _v ∈ A, d := by
    rw [hsum]
    simpa using hedges
  exact Finset.exists_lt_of_sum_lt hlt

/-- The square-root decrement used when removing a vertex from the larger
bipartition class. -/
theorem sqrt_product_sub_one_lower
    (a b : ℝ) (ha : 1 ≤ a) (hb : 0 < b) :
    b / (2 * Real.sqrt (a * b)) ≤
      Real.sqrt (a * b) - Real.sqrt ((a - 1) * b) := by
  have hab : 0 < a * b := mul_pos (by linarith) hb
  have hsub : 0 ≤ (a - 1) * b := mul_nonneg (by linarith) hb.le
  have hx : 0 < Real.sqrt (a * b) := Real.sqrt_pos.2 hab
  have hy : 0 ≤ Real.sqrt ((a - 1) * b) := Real.sqrt_nonneg _
  have hyle : Real.sqrt ((a - 1) * b) ≤ Real.sqrt (a * b) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hxsq := Real.sq_sqrt hab.le
  have hysq := Real.sq_sqrt hsub
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (a * b))).2
  nlinarith

/-- If the expected number of absent pairs is at least one, the
exponential pair-failure estimate forces `s ≤ n log n`. -/
theorem mass_from_exponential_pair_failure
    (n s : ℝ) (hn : 0 < n)
    (hfail : 1 ≤ n ^ 2 * Real.exp (-(2 * s / n))) :
    s ≤ n * Real.log n := by
  have hexp : 0 < Real.exp (2 * s / n) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_right hfail hexp.le
  have hexple : Real.exp (2 * s / n) ≤ n ^ 2 := by
    rw [Real.exp_neg] at hmul
    simpa [mul_assoc, inv_mul_cancel₀ hexp.ne'] using hmul
  have hlog : 2 * s / n ≤ Real.log (n ^ 2) :=
    (Real.le_log_iff_exp_le (by positivity)).2 hexple
  rw [Real.log_pow] at hlog
  have hmul' := mul_le_mul_of_nonneg_right hlog hn.le
  have hcancel : (2 * s / n) * n = 2 * s := by field_simp
  rw [hcancel] at hmul'
  nlinarith

/-- The unbalanced estimate is immediate when the smaller class has at
most `t-2` vertices. -/
theorem edgeCount_le_linear_term_of_small_right
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (t : ℕ) (hB : B.card ≤ t - 2) :
    edgeCount G ≤ (t - 2) * (A.card + B.card) := by
  have hbasic := edgeCount_le_card_mul_card_bipartite G A B hG
  have hmul := Nat.mul_le_mul_left A.card hB
  nlinarith

/-- A convenient exponential criterion for the power condition in the
near-complete auxiliary lemma. -/
theorem near_complete_power_bound_of_exponential_criteria
    (t ℓ : ℕ) (ht : 3 ≤ t) (s n : ℝ) (hn : 0 < n)
    (h100 : (100 : ℝ) ≤ Real.exp (s / n))
    (hlog : 3 * Real.log (t : ℝ) ≤
      s * ((ℓ : ℝ) ^ 2) / n) :
    6 * (t : ℝ) *
      (100 * Real.exp (-(2 * s / n))) ^ (ℓ ^ 2) ≤ 1 := by
  have htR : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have htPos : (0 : ℝ) < t := by linarith
  have hbase : 100 * Real.exp (-(2 * s / n)) ≤
      Real.exp (-(s / n)) := by
    calc
      100 * Real.exp (-(2 * s / n)) ≤
          Real.exp (s / n) * Real.exp (-(2 * s / n)) := by
        exact mul_le_mul_of_nonneg_right h100 (Real.exp_pos _).le
      _ = Real.exp (-(s / n)) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hpow : (100 * Real.exp (-(2 * s / n))) ^ (ℓ ^ 2) ≤
      (Real.exp (-(s / n))) ^ (ℓ ^ 2) :=
    pow_le_pow_left₀ (by positivity) hbase _
  have hExp : (Real.exp (-(s / n))) ^ (ℓ ^ 2) ≤
      Real.exp (-(3 * Real.log (t : ℝ))) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h : 3 * Real.log (t : ℝ) ≤
        s * ((ℓ ^ 2 : ℕ) : ℝ) / n := by simpa using hlog
    calc
      (ℓ ^ 2 : ℕ) * -(s / n) = -(s * ((ℓ ^ 2 : ℕ) : ℝ) / n) := by ring
      _ ≤ -(3 * Real.log (t : ℝ)) := neg_le_neg h
  have hfinal : 6 * (t : ℝ) *
      Real.exp (-(3 * Real.log (t : ℝ))) ≤ 1 := by
    have hident : Real.exp (-(3 * Real.log (t : ℝ))) =
        ((t : ℝ) ^ 3)⁻¹ := by
      rw [show -(3 * Real.log (t : ℝ)) =
        -(Real.log ((t : ℝ) ^ 3)) by rw [Real.log_pow]; ring,
        Real.exp_neg, Real.exp_log (by positivity : 0 < (t : ℝ) ^ 3)]
    rw [hident]
    apply (mul_inv_le_iff₀ (by positivity : 0 < (t : ℝ) ^ 3)).mpr
    nlinarith [sq_nonneg ((t : ℝ) - 3)]
  have hmul := mul_le_mul_of_nonneg_left (hpow.trans hExp)
    (by positivity : 0 ≤ 6 * (t : ℝ))
  exact hmul.trans hfinal

/-- The nontrivial pair-failure branch forces the contracted graph to
have enough vertices for the near-complete auxiliary lemma. -/
theorem nine_mul_t_le_of_exponential_failure
    (t : ℕ) (ht : 3 ≤ t) (n s : ℝ) (hn : 1 ≤ n)
    (hfail : 1 ≤ n ^ 2 * Real.exp (-(2 * s / n)))
    (hmass : 1600 * (t : ℝ) ^ 2 * Real.log (t : ℝ) ≤ s * n) :
    9 * (t : ℝ) ≤ n := by
  have htR : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have htPos : (0 : ℝ) < t := by linarith
  have hlogt : 1 ≤ Real.log (t : ℝ) := by
    have hlog3 : (1 : ℝ) < Real.log 3 := by
      simpa using (Real.log_lt_log (Real.exp_pos 1)
        Real.exp_one_lt_three)
    exact (le_of_lt hlog3).trans (Real.log_le_log (by norm_num) htR)
  have hs : s ≤ n * Real.log n :=
    mass_from_exponential_pair_failure n s (by linarith) hfail
  have hmassUpper : s * n ≤ n ^ 2 * Real.log n := by
    nlinarith [mul_le_mul_of_nonneg_right hs (by linarith : 0 ≤ n)]
  by_contra h
  have hnlt : n < 9 * (t : ℝ) := lt_of_not_ge h
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hlog9 : Real.log (9 : ℝ) ≤ 8 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
    norm_num at this ⊢
    exact this
  have hlogUpper : Real.log n ≤ 8 + Real.log (t : ℝ) := by
    calc
      Real.log n ≤ Real.log (9 * (t : ℝ)) :=
        Real.log_le_log (by linarith) hnlt.le
      _ = Real.log 9 + Real.log (t : ℝ) :=
        Real.log_mul (by norm_num) (by positivity)
      _ ≤ 8 + Real.log (t : ℝ) := by linarith
  have hnSq : n ^ 2 < 81 * (t : ℝ) ^ 2 := by nlinarith
  have hUpper : n ^ 2 * Real.log n <
      81 * (t : ℝ) ^ 2 * (8 + Real.log (t : ℝ)) := by
    calc
      n ^ 2 * Real.log n ≤ n ^ 2 * (8 + Real.log (t : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogUpper (sq_nonneg _)
      _ < 81 * (t : ℝ) ^ 2 * (8 + Real.log (t : ℝ)) :=
        mul_lt_mul_of_pos_right hnSq (by linarith)
  have hLast : 81 * (t : ℝ) ^ 2 * (8 + Real.log (t : ℝ)) <
      1600 * (t : ℝ) ^ 2 * Real.log (t : ℝ) := by
    nlinarith [sq_pos_of_pos htPos]
  linarith

/-- A mass lower bound together with block size at least `n/(18t)`
verifies the near-complete power condition. -/
theorem near_complete_power_bound_of_mass
    (t ℓ : ℕ) (ht : 3 ≤ t) (n s : ℝ) (hn : 0 < n)
    (hblock : n ≤ 18 * (t : ℝ) * (ℓ : ℝ))
    (hratio : 800 ≤ s / n)
    (hmass : 1600 * (t : ℝ) ^ 2 * Real.log (t : ℝ) ≤ s * n) :
    6 * (t : ℝ) *
      (100 * Real.exp (-(2 * s / n))) ^ (ℓ ^ 2) ≤ 1 := by
  have hlog : 0 ≤ Real.log (t : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ t from by omega)
  have h100 : (100 : ℝ) ≤ Real.exp (s / n) := by
    have := Real.add_one_le_exp (s / n)
    linarith
  have hsq : n ^ 2 ≤ 324 * (t : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 := by
    have hnonneg : 0 ≤ 18 * (t : ℝ) * (ℓ : ℝ) := by positivity
    have hh := (sq_le_sq₀ hn.le hnonneg).mpr hblock
    nlinarith
  have hscale : 3 * Real.log (t : ℝ) * n ^ 2 ≤
      972 * (t : ℝ) ^ 2 * Real.log (t : ℝ) * (ℓ : ℝ) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hsq
      (by positivity : 0 ≤ 3 * Real.log (t : ℝ))
    nlinarith
  have hmassScale : 1600 * (t : ℝ) ^ 2 * Real.log (t : ℝ) *
      (ℓ : ℝ) ^ 2 ≤ s * n * (ℓ : ℝ) ^ 2 := by
    exact mul_le_mul_of_nonneg_right hmass (sq_nonneg _)
  have hmiddle : 972 * (t : ℝ) ^ 2 * Real.log (t : ℝ) * (ℓ : ℝ) ^ 2 ≤
      1600 * (t : ℝ) ^ 2 * Real.log (t : ℝ) * (ℓ : ℝ) ^ 2 := by
    have hh : 0 ≤ (t : ℝ) ^ 2 * Real.log (t : ℝ) * (ℓ : ℝ) ^ 2 :=
      by positivity
    nlinarith
  have hcombined : 3 * Real.log (t : ℝ) * n ^ 2 ≤
      s * n * (ℓ : ℝ) ^ 2 :=
    hscale.trans (hmiddle.trans hmassScale)
  have hlogNeeded : 3 * Real.log (t : ℝ) ≤
      s * (ℓ : ℝ) ^ 2 / n := by
    apply (le_div_iff₀ hn).mpr
    have hh : (3 * Real.log (t : ℝ) * n) * n ≤
        (s * (ℓ : ℝ) ^ 2) * n := by nlinarith [hcombined]
    exact (mul_le_mul_iff_of_pos_right hn).mp hh
  exact near_complete_power_bound_of_exponential_criteria t ℓ ht s n hn
    h100 hlogNeeded

/-- The block size `⌊n/(9t)⌋` is at least `n/(18t)` once `n ≥ 9t`. -/
theorem order_le_eighteen_mul_t_mul_floor
    (t n : ℕ) (ht : 0 < t) (hn : 9 * t ≤ n) :
    n ≤ 18 * t * (n / (9 * t)) := by
  have hd : 0 < 9 * t := by omega
  have hℓ : 1 ≤ n / (9 * t) := by
    apply (Nat.le_div_iff_mul_le hd).2
    simpa using hn
  have hmod := Nat.mod_lt n hd
  have hident := Nat.mod_add_div n (9 * t)
  nlinarith

/-- Removing one vertex from each nonempty class decreases the square-root
product by at least half the large-to-small aspect ratio. -/
theorem sqrt_double_decrement_lower
    (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a / (2 * Real.sqrt (a * b)) ≤
      Real.sqrt (a * b) - Real.sqrt ((a - 1) * (b - 1)) := by
  have hfirst := sqrt_product_sub_one_lower b a hb (by linarith : 0 < a)
  have hnonneg : 0 ≤ (a - 1) * (b - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hcomp : (a - 1) * (b - 1) ≤ (b - 1) * a := by
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hcomp
  rw [mul_comm b a] at hfirst
  linarith

/-- The algebraic C.5 step: minimality after contracting a two-edge path
forces a large common neighborhood of its endpoints. -/
theorem common_neighbor_lower_of_path_contraction
    (a b τ κ eG eH degree common : ℝ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hτ : 0 ≤ τ) (hκ : 0 ≤ κ)
    (hcounter : 6400 * τ * Real.sqrt (a * b) + κ * (a + b) < eG)
    (hsmaller : eH ≤ 6400 * τ * Real.sqrt ((a - 1) * (b - 1)) +
      κ * ((a - 1) + (b - 1)))
    (hloss : eH + degree + common = eG)
    (hdegree : degree ≤ 1600 * τ * a / Real.sqrt (a * b)) :
    1600 * τ * a / Real.sqrt (a * b) < common := by
  have hroot : 0 < Real.sqrt (a * b) := by
    apply Real.sqrt_pos.mpr
    nlinarith
  have hdecrement := sqrt_double_decrement_lower a b ha hb
  have hscaled := mul_le_mul_of_nonneg_left hdecrement
    (by positivity : 0 ≤ 6400 * τ)
  have hrewrite :
      (6400 * τ) * (a / (2 * Real.sqrt (a * b))) =
        3200 * τ * a / Real.sqrt (a * b) := by ring
  rw [hrewrite] at hscaled
  have hdrop : 6400 * τ * (Real.sqrt (a * b) -
      Real.sqrt ((a - 1) * (b - 1))) + 2 * κ < degree + common := by
    linarith [hcounter, hsmaller, hloss]
  have hsum : 3200 * τ * a / Real.sqrt (a * b) < degree + common := by
    linarith
  have htwice : 3200 * τ * a / Real.sqrt (a * b) =
      2 * (1600 * τ * a / Real.sqrt (a * b)) := by ring
  rw [htwice] at hsum
  linarith

/-- The C.4 degree lower bound obtained by deleting a vertex from the
first bipartition class of a minimal counterexample. -/
theorem degree_lower_of_vertex_deletion
    (a b τ κ eG eDelete degree : ℝ)
    (ha : 1 ≤ a) (hb : 0 < b) (hτ : 0 ≤ τ)
    (hcounter : 6400 * τ * Real.sqrt (a * b) + κ * (a + b) < eG)
    (hsmaller : eDelete ≤ 6400 * τ * Real.sqrt ((a - 1) * b) +
      κ * ((a - 1) + b))
    (hloss : eDelete + degree = eG) :
    3200 * τ * b / Real.sqrt (a * b) + κ < degree := by
  have hdecrement := sqrt_product_sub_one_lower a b ha hb
  have hscaled := mul_le_mul_of_nonneg_left hdecrement
    (by positivity : 0 ≤ 6400 * τ)
  have hrewrite : (6400 * τ) * (b / (2 * Real.sqrt (a * b))) =
      3200 * τ * b / Real.sqrt (a * b) := by ring
  rw [hrewrite] at hscaled
  have hdrop : 6400 * τ * (Real.sqrt (a * b) -
      Real.sqrt ((a - 1) * b)) + κ < degree := by
    linarith [hcounter, hsmaller, hloss]
  linarith

/-- Convert the C.5 common-neighbor lower bound and the chosen sample size
into the two numerical inputs for C.7 and C.8. -/
theorem mass_and_ratio_of_sample_bounds
    (τ α n s : ℝ) (hτ : 0 < τ) (hα : 1 ≤ α)
    (hnlow : τ / α ≤ n) (hnup : n ≤ 2 * τ)
    (hs : 1600 * α * τ ≤ s) :
    800 ≤ s / n ∧ 1600 * τ ^ 2 ≤ s * n := by
  have hαpos : 0 < α := by linarith
  have hnpos : 0 < n := by
    have := div_pos hτ hαpos
    linarith
  have hspos : 0 ≤ s := by nlinarith
  have hratio : 800 ≤ s / n := by
    apply (le_div_iff₀ hnpos).mpr
    have hmid : 800 * n ≤ 1600 * τ := by linarith
    have hmid' : 1600 * τ ≤ 1600 * α * τ := by nlinarith
    linarith
  have hmass : 1600 * τ ^ 2 ≤ s * n := by
    have hlow : 0 ≤ τ / α := (div_pos hτ hαpos).le
    calc
      1600 * τ ^ 2 = (1600 * α * τ) * (τ / α) := by
        field_simp
      _ ≤ s * (τ / α) := mul_le_mul_of_nonneg_right hs hlow
      _ ≤ s * n := mul_le_mul_of_nonneg_left hnlow hspos
  exact ⟨hratio, hmass⟩

/-- The combined numerical conclusion of Appendix C: either the expected
missing-pair count is below one, or the near-complete power condition holds. -/
theorem near_complete_power_of_sample_failure
    (t n : ℕ) (ht : 3 ≤ t) (hn : 1 ≤ n)
    (τ α s : ℝ) (hτ : 0 < τ) (hα : 1 ≤ α)
    (hτsq : τ ^ 2 = (t : ℝ) ^ 2 * Real.log (t : ℝ))
    (hnlow : τ / α ≤ (n : ℝ)) (hnup : (n : ℝ) ≤ 2 * τ)
    (hs : 1600 * α * τ ≤ s)
    (hfail : 1 ≤ (n : ℝ) ^ 2 * Real.exp (-(2 * s / (n : ℝ)))) :
    9 * t ≤ n ∧
      6 * (t : ℝ) *
        (100 * Real.exp (-(2 * s / (n : ℝ)))) ^ ((n / (9 * t)) ^ 2) ≤ 1 := by
  obtain ⟨hratio, hmassτ⟩ :=
    mass_and_ratio_of_sample_bounds τ α (n : ℝ) s hτ hα hnlow hnup hs
  have hmass : 1600 * (t : ℝ) ^ 2 * Real.log (t : ℝ) ≤ s * (n : ℝ) := by
    calc
      1600 * (t : ℝ) ^ 2 * Real.log (t : ℝ) = 1600 * τ ^ 2 := by
        rw [hτsq]
        ring
      _ ≤ s * (n : ℝ) := hmassτ
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn9R := nine_mul_t_le_of_exponential_failure
    t ht (n : ℝ) s hnR hfail hmass
  have hn9 : 9 * t ≤ n := by exact_mod_cast hn9R
  have hblockNat := order_le_eighteen_mul_t_mul_floor
    t n (by omega) hn9
  have hblock : (n : ℝ) ≤ 18 * (t : ℝ) * (n / (9 * t) : ℕ) := by
    exact_mod_cast hblockNat
  refine ⟨hn9, ?_⟩
  exact near_complete_power_bound_of_mass t (n / (9 * t)) ht
    (n : ℝ) s (by exact_mod_cast hn) hblock hratio hmass

/-- Transfer the contraction's missing-edge count estimate to its
missing-edge fraction in the near-complete criterion. -/
theorem near_complete_power_of_missing_count_bound
    (t n ℓ m : ℕ) (hn : 2 ≤ n) (s : ℝ)
    (hmissing : (m : ℝ) ≤ (n.choose 2 : ℝ) *
      Real.exp (-(2 * s / (n : ℝ))))
    (hpower : 6 * (t : ℝ) *
      (100 * Real.exp (-(2 * s / (n : ℝ)))) ^ (ℓ ^ 2) ≤ 1) :
    6 * (t : ℝ) *
      (100 * ((m : ℝ) / (n.choose 2 : ℝ))) ^ (ℓ ^ 2) ≤ 1 := by
  have hchoose : (0 : ℝ) < n.choose 2 := by
    exact_mod_cast Nat.choose_pos hn
  have hq : (m : ℝ) / (n.choose 2 : ℝ) ≤
      Real.exp (-(2 * s / (n : ℝ))) := by
    apply (div_le_iff₀ hchoose).mpr
    simpa [mul_comm] using hmissing
  have hbase : 100 * ((m : ℝ) / (n.choose 2 : ℝ)) ≤
      100 * Real.exp (-(2 * s / (n : ℝ))) := by nlinarith
  have hpow := pow_le_pow_left₀ (by positivity) hbase (ℓ ^ 2)
  exact (mul_le_mul_of_nonneg_left hpow (by positivity)).trans hpower

/-- The ceiling sample size in Appendix C is large enough for the
complete-outcome contradiction and at most twice the KT scale. -/
theorem sample_size_ceiling_bounds
    (t : ℕ) (ht : 2 ≤ t) (τ α : ℝ)
    (hτ : (t : ℝ) ≤ τ) (hα : 1 ≤ α) :
    let n := Nat.ceil (τ / α + (t : ℝ) - 2)
    t - 1 ≤ n ∧ τ / α ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * τ := by
  have hαpos : 0 < α := by linarith
  have hτpos : 0 < τ := by
    have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have hratio : 0 < τ / α := div_pos hτpos hαpos
  let x := τ / α + (t : ℝ) - 2
  let n := Nat.ceil x
  have hx0 : 0 ≤ x := by
    have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
    dsimp [x]
    linarith
  have hceil : x ≤ (n : ℝ) := Nat.le_ceil x
  have hceilUpper : (n : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hNatLower : t - 1 ≤ n := by
    have htR : (t : ℝ) - 2 < (n : ℝ) := by
      dsimp [x] at hceil
      linarith
    have hNat : t - 2 < n := by
      have hsub : ((t - 2 : ℕ) : ℝ) = (t : ℝ) - 2 := by
        exact Nat.cast_sub ht
      exact_mod_cast (hsub ▸ htR)
    omega
  have hτlower : τ / α ≤ (n : ℝ) := by
    dsimp [x] at hceil
    have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have hτupper : (n : ℝ) ≤ 2 * τ := by
    have hratioUpper : τ / α ≤ τ :=
      (div_le_iff₀ hαpos).mpr (by nlinarith)
    dsimp [x] at hceilUpper
    have htR : (t : ℝ) ≤ τ := hτ
    linarith
  exact ⟨hNatLower, hτlower, hτupper⟩

/-- For `t ≥ 3`, the Kostochka--Thomason scale dominates `t` and
its square has the expected exact form. -/
theorem kt_scale_ge_order_and_square (t : ℕ) (ht : 3 ≤ t) :
    (t : ℝ) ≤ (t : ℝ) * Real.sqrt (Real.log (t : ℝ)) ∧
      ((t : ℝ) * Real.sqrt (Real.log (t : ℝ))) ^ 2 =
        (t : ℝ) ^ 2 * Real.log (t : ℝ) := by
  have htR : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have hlog : 1 ≤ Real.log (t : ℝ) := by
    have hlog3 : (1 : ℝ) < Real.log 3 := by
      simpa using (Real.log_lt_log (Real.exp_pos 1)
        Real.exp_one_lt_three)
    exact (le_of_lt hlog3).trans (Real.log_le_log (by norm_num) htR)
  have hsqrt : 1 ≤ Real.sqrt (Real.log (t : ℝ)) := by
    have := Real.sqrt_le_sqrt hlog
    simpa using this
  have hlog0 : 0 ≤ Real.log (t : ℝ) := by linarith
  constructor
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ t)
      (by linarith : 0 ≤ Real.sqrt (Real.log (t : ℝ)) - 1)]
  · rw [mul_pow, Real.sq_sqrt hlog0]

/-- The large-to-small aspect ratio may be represented as `a / √(ab)`,
which avoids a second square root in the vertex-deletion inequalities. -/
theorem aspect_ratio_ge_one
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    1 ≤ a / Real.sqrt (a * b) := by
  have hab : 0 < a * b := mul_pos ha hb
  have hroot : 0 < Real.sqrt (a * b) := Real.sqrt_pos.mpr hab
  have hsq : Real.sqrt (a * b) ≤ a := by
    have hprod : a * b ≤ a ^ 2 := by nlinarith
    have h := Real.sqrt_le_sqrt hprod
    simpa [Real.sqrt_sq_eq_abs, abs_of_pos ha] using h
  exact (le_div_iff₀ hroot).mpr (by linarith)

/-- The two class-aspect factors are reciprocal. -/
theorem aspect_ratio_mul_reciprocal
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a / Real.sqrt (a * b)) * (b / Real.sqrt (a * b)) = 1 := by
  have hab : 0 ≤ a * b := (mul_pos ha hb).le
  have hroot : 0 < Real.sqrt (a * b) := Real.sqrt_pos.mpr (mul_pos ha hb)
  have hsq := Real.sq_sqrt hab
  field_simp
  nlinarith
end HadwigerLean
