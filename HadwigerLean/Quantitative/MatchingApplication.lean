import HadwigerLean.Hypergraph.AlmostPerfectMatching
import HadwigerLean.Quantitative.MatchingConstants

/-!
# The paper's finite matching schedule

The constant estimates are combined here with the checked finite
hypergraph iteration. The sampled hypergraph is supplied separately by
the rounding development.
-/

namespace HadwigerLean.Theorem2

open MatchingRound

/-- The paper's floor schedule satisfies every condition of the finite
matching iteration once the initial maximum codegree is small. -/
theorem matchingSchedule_paper
    {D₀ B r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hBmin : 1 ≤ B)
    (hBmax : (B : ℝ) ≤ matchingMu r ξ * (D₀ : ℝ)) :
    MatchingRound.MatchingSchedule r B (matchingT r ξ)
      (matchingD D₀ r ξ) (matchingA r ξ) (matchingDelta r ξ) := by
  have ha0 := (matchingA_pos hr hξ hξ1).le
  have har : (r : ℝ) * matchingA r ξ ≤ 1 / 100 := by
    simpa only [mul_comm] using matchingA_mul_r_le hr hξ hξ1
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have ha1 : matchingA r ξ ≤ 1 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (r : ℝ) - 1) ha0]
  have hb0 := (matchingB_pos hr hξ).le
  have hb1 : matchingB r ξ ≤ 1 := by
    have hb := matchingB_le_a_quarter hr hξ hξ1
    linarith
  apply MatchingRound.matchingSchedule_of_floor_bounds
    hr hBmin ha0 har hb0 hb1
  · simpa only [mul_assoc] using matching_small hr hξ hξ1
  · exact le_refl _
  · intro i hi
    exact matchingD_positive hr hξ hξ1 hBmin hBmax hi
  · intro i hi
    exact matchingD_codegree_ratio hr hξ hξ1 hBmin hBmax hi.le
  · intro i hi
    exact matchingD_large hr hξ hξ1 hBmin hBmax hi.le
  · intro i hi
    have h := matchingD_next_lt_add_one
      (D₀ := D₀) (r := r) (i := i) (ξ := ξ)
    rw [matchingLambda_eq_exp hr] at h
    simpa only [mul_comm] using h
  · intro i hi
    simpa only [matchingQ, neg_mul] using
      (matchingD_next_le_exp (D₀ := D₀) (r := r) (i := i) (ξ := ξ) hr)

/-- The numerical potential budget for the sampled hypergraph. -/
theorem matching_initial_potential_budget
    {V E : Type*} [DecidableEq V]
    (H : IndexedHypergraph V E)
    {D₀ r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hDeficit :
      (H.degreeDeficit D₀ : ℝ) / (D₀ : ℝ) ≤
        matchingMu r ξ * (H.vertices.card : ℝ)) :
    lossPotentialA (Real.exp (-matchingA r ξ))
        (matchingDelta r ξ) (matchingA r ξ)
        ((r : ℝ) * matchingA r ξ ^ 2)
        (matchingT r ξ) 0 * (H.vertices.card : ℝ) +
      lossPotentialB (matchingA r ξ) (matchingT r ξ) 0 *
        ((H.degreeDeficit D₀ : ℝ) / (D₀ : ℝ)) ≤
      ξ * (H.vertices.card : ℝ) := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hmu : 0 ≤ matchingMu r ξ := by
    unfold matchingMu
    positivity
  have h := MatchingRound.initial_potential_budget
    (matchingT r ξ) (H.vertices.card : ℝ)
    ((H.degreeDeficit D₀ : ℝ) / (D₀ : ℝ))
    (matchingQ r ξ) (matchingDelta r ξ)
    (matchingA r ξ)
    ((r : ℝ) * matchingA r ξ ^ 2)
    (matchingL ξ) (matchingMu r ξ) ξ
    (Nat.cast_nonneg _) hmu
    (matchingQ_pos.le) (matchingQ_le_one hr hξ hξ1)
    (matchingDelta_nonneg r ξ) (matchingA_pos hr hξ hξ1).le
    (by positivity)
    (matchingQ_pow_T_le hr hξ hξ1)
    (matching_total_error_budget hr hξ hξ1)
    hDeficit
    (matchingA_mul_T_bounds hr hξ hξ1).2
    (matching_initial_mu_budget hr hξ hξ1)
  simpa only [matchingQ] using h

/-- The paper's matching bound for a uniform indexed hypergraph with the
specified initial degree, codegree, and deficit caps. -/
theorem exists_almostPerfectMatching_paper
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (H : IndexedHypergraph V E)
    {D₀ B r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hBmin : 1 ≤ B)
    (hBmax : (B : ℝ) ≤ matchingMu r ξ * (D₀ : ℝ))
    (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D₀)
    (hB : H.maxCodegree ≤ B)
    (hDeficit :
      (H.degreeDeficit D₀ : ℝ) / (D₀ : ℝ) ≤
        matchingMu r ξ * (H.vertices.card : ℝ)) :
    ∃ M : Finset E, H.IsMatching M ∧
      (1 - ξ) * (H.vertices.card : ℝ) ≤ (H.covered M).card := by
  have hsched :=
    matchingSchedule_paper hr hξ hξ1 hBmin hBmax
  have hpot :=
    matching_initial_potential_budget H hr hξ hξ1 hDeficit
  exact MatchingRound.exists_almostPerfectMatching_of_schedule H
    hsched hunif
    (by simpa only [matchingD] using hcap)
    hB
    (by simpa only [matchingD] using hpot)
/-- A minimum-degree hypothesis supplies the normalized initial deficit
used by the almost-perfect matching theorem. -/
theorem exists_almostPerfectMatching_of_degree_bounds
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (H : IndexedHypergraph V E)
    {D₀ B r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hD₀ : 0 < D₀)
    (hBmin : 1 ≤ B)
    (hBmax : (B : ℝ) ≤ matchingMu r ξ * (D₀ : ℝ))
    (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D₀)
    (hmin : ∀ v ∈ H.vertices,
      (1 - matchingMu r ξ) * (D₀ : ℝ) ≤ (H.degree v : ℝ))
    (hB : H.maxCodegree ≤ B) :
    ∃ M : Finset E, H.IsMatching M ∧
      (1 - ξ) * (H.vertices.card : ℝ) ≤ (H.covered M).card := by
  apply exists_almostPerfectMatching_paper H hr hξ hξ1
    hBmin hBmax hunif hcap hB
  exact MatchingRound.normalized_degreeDeficit_le H hD₀ hcap hmin
end HadwigerLean.Theorem2