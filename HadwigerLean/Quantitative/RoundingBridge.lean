import HadwigerLean.Coloring.LowCodegreeRounding
import HadwigerLean.Quantitative.Constants
import HadwigerLean.Quantitative.MatchingApplication
import HadwigerLean.Quantitative.MatchingParameterBridge

/-!
# Quantitative low-codegree rounding bridge

The finite token/dummy sample is passed to the quantitative matching theorem.
-/

namespace HadwigerLean.LowCodegreeRounding

section MatchingOfPaperSample

variable {W E : Type*} [Fintype W] [Fintype E]
  [DecidableEq W] [DecidableEq E]

/-- The matching theorem applies directly to a good Bernoulli sample;
its matching is then lifted to the unsampled indexed hypergraph. -/
theorem matching_of_paper_sample
    (H : IndexedHypergraph W E) (ω : E → Bool)
    (r : ℕ) (ξ μ n m : ℝ)
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hμeq : μ = Theorem2.matchingMu r ξ)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hn : 0 < n)
    (hverts : H.vertices.Nonempty)
    (hunif : H.IsUniform r)
    (hsmall : 8 * m ≤ μ * n)
    (hdegree : ∀ v ∈ H.vertices,
      n - m - μ * n / 8 < ((sampledHypergraph H ω).degree v : ℝ) ∧
        ((sampledHypergraph H ω).degree v : ℝ) < n + μ * n / 8)
    (hcodegree : ∀ u ∈ H.vertices, ∀ v ∈ H.vertices,
      u ≠ v →
        ((sampledHypergraph H ω).codegree u v : ℝ) < μ * n / 2) :
    ∃ M : Finset E, H.IsMatching M ∧
      (1 - ξ) * (H.vertices.card : ℝ) ≤ (H.covered M).card := by
  classical
  let K := sampledHypergraph H ω
  obtain ⟨hDposR, hminR, hBmaxR⟩ :=
    sampled_paper_bounds_imply_matching_hypotheses
      H ω n m μ hn hμ hμ1 hverts hsmall hdegree hcodegree
  have hDpos : 0 < K.maxDegree := by exact_mod_cast hDposR
  have hKunif : K.IsUniform r := sampled_uniform H ω hunif
  have hBmin : 1 ≤ K.maxCodegree :=
    K.maxCodegree_pos_of_maxDegree_pos hr hKunif hDpos
  have hBmax : (K.maxCodegree : ℝ) ≤
      Theorem2.matchingMu r ξ * (K.maxDegree : ℝ) := by
    simpa only [← hμeq] using hBmaxR
  have hmin : ∀ v ∈ K.vertices,
      (1 - Theorem2.matchingMu r ξ) * (K.maxDegree : ℝ) ≤
        (K.degree v : ℝ) := by
    simpa only [← hμeq] using hminR
  obtain ⟨M, hM, hcover⟩ :=
    Theorem2.exists_almostPerfectMatching_of_degree_bounds K
      hr hξ hξ1 hDpos hBmin hBmax hKunif
      (by intro v hv; exact K.degree_le_maxDegree hv)
      hmin le_rfl
  refine ⟨M, sampled_matching_lift H ω M hM, ?_⟩
  change (1 - ξ) * (H.vertices.card : ℝ) ≤
    (((sampledHypergraph H ω).covered M).card : ℝ) at hcover
  rw [sampled_covered_eq] at hcover
  exact hcover

end MatchingOfPaperSample

end HadwigerLean.LowCodegreeRounding



namespace HadwigerLean.LowCodegreeRounding

section TokenDummyMatchingBridge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The quantitative matching theorem discharges the token/dummy
matching hypothesis when the rounded counts and sample scale hold. -/
theorem tokenDummy_matchingHypothesis_of_parameter_bounds
    (G : SimpleGraph V) (m p z : ℕ)
    (hm : 1 ≤ m) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (hload : ∀ v, vertexLoad G x v = 1)
    (hTlower : fractionalCost G x ≤ (p : ℝ))
    (hTupper : (p : ℝ) ≤ fractionalCost G x + 1)
    (hZlower : ((m + 1 : ℕ) : ℝ) * fractionalCost G x -
      (Fintype.card V : ℝ) ≤ (z : ℝ))
    (hZupper : (z : ℝ) ≤
      ((m + 1 : ℕ) : ℝ) * fractionalCost G x -
        (Fintype.card V : ℝ) + 1)
    (ξ μ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hμeq : μ = Theorem2.matchingMu (m + 2) ξ)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hx : IsPairConstrainedColoring G (μ / 4) x)
    (hscale : 1000000 * (((m + 2 : ℕ) : ℝ) ^ 4) ≤
      μ ^ 4 * (Fintype.card V : ℝ)) :
    MatchingHypothesis G m p z ξ := by
  classical
  let H := tokenDummyHypergraph G m p z
  let n : ℝ := Fintype.card V
  obtain ⟨ω, hdegree, hcodegree⟩ :=
    exists_tokenDummy_good_sample G m p z hm hp hz x hstable hload
      hTlower hTupper hZlower hZupper μ hμ hμ1 hx hscale
  have hscales := paper_scale_implies_rounding_scales m n μ hm hμ hμ1 hscale
  have hn : 0 < n := by linarith [hscales.2.2.1]
  have hverts : H.vertices.Nonempty := by
    refine ⟨Sum.inr (Sum.inl (⟨0, hp⟩ : Fin p)), ?_⟩
    simp [H, tokenDummyHypergraph]
  have hr : 2 ≤ m + 2 := by omega
  obtain ⟨M, hM, hcovered⟩ :=
    matching_of_paper_sample H ω (m + 2) ξ μ n (m : ℝ)
      hr hξ hξ1 hμeq hμ hμ1 hn hverts
      (tokenDummy_uniform G m p z) hscales.2.1 hdegree hcodegree
  exact ⟨M, hM, hcovered⟩

end TokenDummyMatchingBridge

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section RoundedCounts

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Choose the paper's token and dummy counts by natural ceilings.
The sample-size bound makes the dummy count large enough for every edge. -/
theorem exists_rounded_token_dummy_counts (G : SimpleGraph V)
    (m : ℕ) (hm : 1 ≤ m)
    (x : StableSet G → ℝ) (hx : ∀ S, 0 ≤ x S)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (hload : ∀ v, vertexLoad G x v = 1)
    (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hscale : 1000000 * (((m + 2 : ℕ) : ℝ) ^ 4) ≤
      μ ^ 4 * (Fintype.card V : ℝ)) :
    ∃ p z : ℕ, 0 < p ∧ m + 1 ≤ z ∧
      fractionalCost G x ≤ (p : ℝ) ∧
      (p : ℝ) ≤ fractionalCost G x + 1 ∧
      ((m + 1 : ℕ) : ℝ) * fractionalCost G x -
        (Fintype.card V : ℝ) ≤ (z : ℝ) ∧
      (z : ℝ) ≤
        ((m + 1 : ℕ) : ℝ) * fractionalCost G x -
          (Fintype.card V : ℝ) + 1 := by
  let n : ℝ := Fintype.card V
  let τ := fractionalCost G x
  let A := ((m + 1 : ℕ) : ℝ) * τ - n
  let p := ⌈τ⌉₊
  let z := ⌈A⌉₊
  have hscales := paper_scale_implies_rounding_scales m n μ hm hμ hμ1 hscale
  have hnpos : 0 < n := by linarith [hscales.2.2.1]
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmn : n ≤ (m : ℝ) * τ :=
    card_le_m_mul_fractionalCost G m x hx hstable hload
  have hτpos : 0 < τ := by
    by_contra h
    have hτnonpos : τ ≤ 0 := le_of_not_gt h
    have hprod : (m : ℝ) * τ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hmR.le hτnonpos
    linarith
  have hTA : τ ≤ A := by
    dsimp [A]
    push_cast
    nlinarith [hmn]
  have hApos : 0 < A := lt_of_lt_of_le hτpos hTA
  have hμn : μ * n ≤ n :=
    (mul_le_mul_of_nonneg_right hμ1 hnpos.le).trans_eq (one_mul n)
  have h4mn : 4 * (m : ℝ) ^ 2 ≤ n := hscales.1.trans hμn
  have hτ4 : 4 * (m : ℝ) ≤ τ := by
    apply (mul_le_mul_iff_of_pos_left hmR).mp
    calc
      (m : ℝ) * (4 * (m : ℝ)) = 4 * (m : ℝ) ^ 2 := by ring
      _ ≤ n := h4mn
      _ ≤ (m : ℝ) * τ := hmn
  have hAlarge : (((m + 1 : ℕ) : ℝ)) ≤ A := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    dsimp [A]
    push_cast
    nlinarith [hTA, hτ4]
  have hTlower : τ ≤ (p : ℝ) := Nat.le_ceil τ
  have hTupper : (p : ℝ) ≤ τ + 1 :=
    (Nat.ceil_lt_add_one hτpos.le).le
  have hZlower : A ≤ (z : ℝ) := Nat.le_ceil A
  have hZupper : (z : ℝ) ≤ A + 1 :=
    (Nat.ceil_lt_add_one hApos.le).le
  have hp : 0 < p := by
    have hpr : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le hτpos hTlower
    exact_mod_cast hpr
  have hz : m + 1 ≤ z := by
    have hzr : (((m + 1 : ℕ) : ℝ)) ≤ (z : ℝ) := hAlarge.trans hZlower
    exact_mod_cast hzr
  exact ⟨p, z, hp, hz, hTlower, hTupper, hZlower, hZupper⟩

end RoundedCounts

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.Theorem2

section PaperRounding

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Low-codegree rounding at the exact parameters used by Theorem 2.
A pair-constrained fractional coloring with unit vertex loads rounds to
an ordinary coloring with the stated additive loss. -/
theorem low_codegree_rounding (G : SimpleGraph V)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hα : independenceNumber G ≤ m ε)
    (hn : n0 ε ≤ Fintype.card V)
    (x : StableSet G → ℝ)
    (hx : IsPairConstrainedColoring G (mu ε / 4) x)
    (hload : ∀ v, vertexLoad G x v = 1) :
    (chromatic G : ℝ) ≤ fractionalCost G x +
      gamma ε * (Fintype.card V : ℝ) := by
  classical
  let k := m ε
  let μ := mu ε
  let ξ := matchingXi ε
  have hk : 1 ≤ k := by
    have hk2 := m_ge_two hε hε1
    dsimp [k]
    omega
  have hstable : ∀ S : StableSet G, S.1.card ≤ k := by
    intro S
    exact (stable_card_le_independenceNumber G S.2.2).trans hα
  have hμpos : 0 < μ := mu_pos hε
  have hμ1 : μ ≤ 1 := mu_le_one hε hε1
  have hscale : 1000000 * (((k + 2 : ℕ) : ℝ) ^ 4) ≤
      μ ^ 4 * (Fintype.card V : ℝ) :=
    n0_implies_sampling_scale hε hn
  obtain ⟨p, z, hp, hz, hTlower, hTupper, hZlower, hZupper⟩ :=
    LowCodegreeRounding.exists_rounded_token_dummy_counts G
      k hk x hx.1.1 hstable hload μ hμpos hμ1 hscale
  have hξpos : 0 < ξ := matchingXi_pos hε hε1
  have hξ1 : ξ ≤ 1 := matchingXi_le_one hε hε1
  have hμeq : μ = matchingMu (k + 2) ξ :=
    mu_eq_matchingMu hε hε1
  have hmatch : LowCodegreeRounding.MatchingHypothesis G k p z ξ :=
    LowCodegreeRounding.tokenDummy_matchingHypothesis_of_parameter_bounds
      G k p z hk hp hz x hstable hload
      hTlower hTupper hZlower hZupper
      ξ μ hξpos hξ1 hμeq hμpos hμ1 hx hscale
  have hscales := LowCodegreeRounding.paper_scale_implies_rounding_scales
    k (Fintype.card V : ℝ) μ hk hμpos hμ1 hscale
  have hn1R : (1 : ℝ) ≤ (Fintype.card V : ℝ) := hscales.2.2.1
  have hn1 : 1 ≤ Fintype.card V := by exact_mod_cast hn1R
  have hN := LowCodegreeRounding.tokenDummy_vertex_count_le
    G k p z x hx.1.1 hload hTupper hZupper
  have hsize : ξ *
      ((LowCodegreeRounding.tokenDummyHypergraph G k p z).vertices.card : ℝ) ≤
        gamma ε * (Fintype.card V : ℝ) / 2 :=
    matchingXi_card_budget hε hε1 hn1 hN
  have hlarge : 2 ≤ gamma ε * (Fintype.card V : ℝ) :=
    n0_implies_gamma_n_ge_two hε hn
  exact LowCodegreeRounding.chromatic_le_of_MatchingHypothesis
    G k p z ξ (gamma ε) x hmatch hTupper hsize hlarge

end PaperRounding

end HadwigerLean.Theorem2
