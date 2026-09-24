import HadwigerLean.Coloring.Augmentation
import HadwigerLean.Quantitative.Peeling
import Mathlib.Tactic

/-!
# Constants for Theorem 2

These definitions follow the explicit choices in the paper's proof of the
quantitative theorem. The final exponent bound remains a separate target.
-/

namespace HadwigerLean.Theorem2

/-- The independence-number threshold. -/
noncomputable def m (ε : ℝ) : ℕ := ⌈2 / ε⌉₊

/-- Uniformity in the rounding hypergraph. -/
noncomputable def r (ε : ℝ) : ℕ := m ε + 2

/-- Allowed rounding and augmentation error. -/
noncomputable def gamma (ε : ℝ) : ℝ := ε / 6

/-- The paper's low-pair-load parameter. -/
noncomputable def mu (ε : ℝ) : ℝ :=
  (ε / (2400 * (r ε : ℝ) ^ 2)) ^ (20 * r ε)

/-- Order threshold for low-codegree rounding. -/
noncomputable def n0 (ε : ℝ) : ℕ :=
  ⌈1000000 * (r ε : ℝ) ^ 4 * ((mu ε)⁻¹) ^ 4 + 12 / ε⌉₊

/-- Maximum degree of the added nonedge graph. -/
noncomputable def d (ε : ℝ) : ℕ :=
  ⌈288 * (Nat.choose (m ε) 2 : ℝ) /
    (mu ε * ε ^ 2)⌉₊

/-- The robust bound's additive term. -/
noncomputable def robustAdditive (ε : ℝ) : ℕ :=
  2 * m ε * (1 + ∑ j ∈ Finset.range (2 * m ε), (d ε + 1) ^ j)

/-- The additive term before the final explicit exponential estimate. -/
noncomputable def A (ε : ℝ) : ℕ :=
  max (n0 ε) (robustAdditive ε)

/-- The explicit additive term in Theorem 2. -/
noncomputable def Aepsilon (ε : ℝ) : ℝ :=
  (100 / ε) ^ (2000 / ε ^ 2)

theorem gamma_pos {ε : ℝ} (hε : 0 < ε) : 0 < gamma ε := by
  unfold gamma
  positivity

theorem three_gamma (ε : ℝ) : 3 * gamma ε = ε / 2 := by
  unfold gamma
  ring

theorem m_ge_two {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    2 ≤ m ε := by
  have hfrac : (2 : ℝ) ≤ 2 / ε := by
    apply (le_div_iff₀ hε).2
    nlinarith
  have hceil : (2 : ℝ) ≤ (m ε : ℝ) :=
    hfrac.trans (Nat.le_ceil (2 / ε))
  exact_mod_cast hceil

theorem r_ge_four {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    4 ≤ r ε := by
  have hm : 2 ≤ m ε := m_ge_two hε hε1
  unfold r
  omega

theorem mu_pos {ε : ℝ} (hε : 0 < ε) : 0 < mu ε := by
  have hr : 0 < (r ε : ℝ) := by
    unfold r
    exact_mod_cast Nat.zero_lt_succ (m ε + 1)
  unfold mu
  positivity


theorem mu_le_one {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    mu ε ≤ 1 := by
  have hr : (4 : ℝ) ≤ (r ε : ℝ) := by
    exact_mod_cast r_ge_four hε hε1
  have hr2 : (1 : ℝ) ≤ (r ε : ℝ) ^ 2 := by
    nlinarith
  have hden : 0 < 2400 * (r ε : ℝ) ^ 2 := by
    nlinarith
  have hbase : ε / (2400 * (r ε : ℝ) ^ 2) ≤ 1 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  unfold mu
  exact pow_le_one₀ (div_pos hε hden).le hbase
/-- Substituting δ=μ/4 and γ=ε/6 gives precisely the argument of d's ceiling. -/
theorem augmentation_degree_ratio (ε μ : ℝ) (m : ℕ)
    (hε : 0 < ε) (hμ : 0 < μ) (hm : 2 ≤ m) :
    (2 / ((μ / 4) * (ε / 6))) /
        ((ε / 6) / (Nat.choose m 2 : ℝ)) =
      288 * (Nat.choose m 2 : ℝ) / (μ * ε ^ 2) := by
  have hC : (Nat.choose m 2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hm).ne'
  field_simp
  ring


theorem m_le_three_div {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (m ε : ℝ) ≤ 3 / ε := by
  have hceil : (m ε : ℝ) < 2 / ε + 1 := by
    unfold m
    exact Nat.ceil_lt_add_one (div_nonneg (by norm_num) hε.le)
  have hone : (1 : ℝ) ≤ 1 / ε := by
    apply (le_div_iff₀ hε).2
    simpa using hε1
  calc
    (m ε : ℝ) ≤ 2 / ε + 1 := hceil.le
    _ ≤ 2 / ε + 1 / ε := by linarith
    _ = 3 / ε := by ring

theorem r_le_five_div {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (r ε : ℝ) ≤ 5 / ε := by
  have hm := m_le_three_div hε hε1
  have htwo : (2 : ℝ) ≤ 2 / ε := by
    apply (le_div_iff₀ hε).2
    nlinarith
  calc
    (r ε : ℝ) = (m ε : ℝ) + 2 := by simp [r]
    _ ≤ 3 / ε + 2 := by linarith
    _ ≤ 3 / ε + 2 / ε := by linarith
    _ = 5 / ε := by ring

/-- The augmentation lemma with the paper's choices of μ, γ, and d.
The remaining assumption is the exact low-pair-load rounding theorem. -/
theorem exists_augmentation_at_theorem2_parameters
    (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hα : independenceNumber G ≤ m ε)
    (hround : ∀ x : StableSet G → ℝ,
      IsPairConstrainedColoring G (mu ε / 4) x →
      (∀ v, vertexLoad G x v = 1) →
      (chromatic G : ℝ) ≤ fractionalCost G x +
        gamma ε * (Fintype.card V : ℝ)) :
    ∃ F : SimpleGraph V,
      F ≤ Gᶜ ∧
      (letI : DecidableRel F.Adj := Classical.decRel F.Adj
       F.maxDegree) ≤ d ε ∧
      (chromatic G : ℝ) ≤
        fractionalChromaticNumber (G ⊔ F) +
          ε * (Fintype.card V : ℝ) / 2 := by
  classical
  have hμ : 0 < mu ε := mu_pos hε
  have hδ : 0 < mu ε / 4 := by positivity
  have hγ : 0 < gamma ε := gamma_pos hε
  have hm2 : 2 ≤ m ε := m_ge_two hε hε1
  obtain ⟨F, hF, hdegree, hchi⟩ :=
    exists_boundedDegree_augmentation_from_rounding
      G (mu ε / 4) (gamma ε) (m ε)
      hδ hγ hα hm2 hround
  refine ⟨F, hF, ?_, ?_⟩
  · have hratio :
        (2 / ((mu ε / 4) * gamma ε)) /
          (gamma ε / (Nat.choose (m ε) 2 : ℝ)) =
        288 * (Nat.choose (m ε) 2 : ℝ) /
          (mu ε * ε ^ 2) := by
      unfold gamma
      exact augmentation_degree_ratio ε (mu ε) (m ε)
        hε hμ hm2
    simpa only [hratio, d] using hdegree
  · rw [three_gamma] at hchi
    nlinarith

/-- The final Theorem 2 statement follows from the bounded-independence
case on induced subgraphs. This keeps the final peeling argument separate
from matching, rounding, and robust fractional coloring. -/
theorem quantitative_bound_of_bounded_induced
    (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    (ε : ℝ) (hε : 0 < ε) (_hε1 : ε ≤ 1)
    (hsmall : ∀ J : Finset V,
      independenceNumber (G.induce (J : Set V)) ≤ m ε →
      (chromatic (G.induce (J : Set V)) : ℝ) ≤
        4 * (cliqueMinorNumber (G.induce (J : Set V)) : ℝ) +
          ε * (J.card : ℝ) / 2 + Aepsilon ε) :
    (chromatic G : ℝ) ≤
      4 * (cliqueMinorNumber G : ℝ) +
        ε * (Fintype.card V : ℝ) + Aepsilon ε := by
  have hm : 2 / ε ≤ (m ε + 1 : ℕ) := by
    have hceil : 2 / ε ≤ (m ε : ℝ) := Nat.le_ceil (2 / ε)
    exact hceil.trans (by exact_mod_cast Nat.le_succ (m ε))
  exact chromatic_bound_of_bounded_induced
    G (m ε) ε (Aepsilon ε) hε hm hsmall

/-- The bounded-independence portion of Theorem 2, conditional on the
rounding and robust-fractional statements still being developed. Small
graphs are handled by the n0 term in A. -/
theorem bounded_independence_from_rounding_and_robust
    (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hα : independenceNumber G ≤ m ε)
    (hround :
      n0 ε ≤ Fintype.card V →
      ∀ x : StableSet G → ℝ,
        IsPairConstrainedColoring G (mu ε / 4) x →
        (∀ v, vertexLoad G x v = 1) →
        (chromatic G : ℝ) ≤ fractionalCost G x +
          gamma ε * (Fintype.card V : ℝ))
    (hrobust : ∀ F : SimpleGraph V,
      F ≤ Gᶜ →
      (letI : DecidableRel F.Adj := Classical.decRel F.Adj
       F.maxDegree) ≤ d ε →
      fractionalChromaticNumber (G ⊔ F) ≤
        4 * (cliqueMinorNumber G : ℝ) +
          (robustAdditive ε : ℝ)) :
    (chromatic G : ℝ) ≤
      4 * (cliqueMinorNumber G : ℝ) +
        ε * (Fintype.card V : ℝ) / 2 + (A ε : ℝ) := by
  classical
  by_cases hn : n0 ε ≤ Fintype.card V
  · obtain ⟨F, hF, hdegree, hchi⟩ :=
      exists_augmentation_at_theorem2_parameters
        G ε hε hε1 hα (hround hn)
    have hrob := hrobust F hF hdegree
    have hK : (robustAdditive ε : ℝ) ≤ (A ε : ℝ) := by
      exact_mod_cast (le_max_right (n0 ε) (robustAdditive ε))
    nlinarith
  · have hn' : Fintype.card V < n0 ε := Nat.lt_of_not_ge hn
    have hcolor : (chromatic G : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast chromatic_le_card G
    have hA : (n0 ε : ℝ) ≤ (A ε : ℝ) := by
      exact_mod_cast (le_max_left (n0 ε) (robustAdditive ε))
    have hminor : 0 ≤ (cliqueMinorNumber G : ℝ) := Nat.cast_nonneg _
    have hn0 : 0 ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
    have hεn : 0 ≤ ε * (Fintype.card V : ℝ) :=
      mul_nonneg hε.le hn0
    have hn'R : (Fintype.card V : ℝ) ≤ (n0 ε : ℝ) := by
      exact_mod_cast hn'.le
    nlinarith

/-- It suffices to establish the bounded-independence estimate with the
intermediate additive constant A, then prove the standalone numerical
estimate A ≤ Aepsilon. -/
theorem quantitative_bound_of_bounded_induced_A
    (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : ∀ J : Finset V,
      independenceNumber (G.induce (J : Set V)) ≤ m ε →
      (chromatic (G.induce (J : Set V)) : ℝ) ≤
        4 * (cliqueMinorNumber (G.induce (J : Set V)) : ℝ) +
          ε * (J.card : ℝ) / 2 + (A ε : ℝ))
    (hA : (A ε : ℝ) ≤ Aepsilon ε) :
    (chromatic G : ℝ) ≤
      4 * (cliqueMinorNumber G : ℝ) +
        ε * (Fintype.card V : ℝ) + Aepsilon ε := by
  apply quantitative_bound_of_bounded_induced G ε hε hε1
  intro J hα
  have hJ := hsmall J hα
  linarith

/-- A coarse geometric-sum estimate, useful for the robust additive term. -/
theorem sum_powers_le_card_mul_pow (D k : ℕ) (hD : 1 ≤ D) :
    (∑ j ∈ Finset.range k, D ^ j) ≤ k * D ^ k := by
  calc
    (∑ j ∈ Finset.range k, D ^ j) ≤
        ∑ _j ∈ Finset.range k, D ^ k := by
      apply Finset.sum_le_sum
      intro j hj
      exact pow_le_pow_right₀ hD (Nat.le_of_lt (Finset.mem_range.mp hj))
    _ = k * D ^ k := by simp

theorem robustAdditive_le_simple (ε : ℝ) :
    robustAdditive ε ≤
      (2 * m ε + (2 * m ε) ^ 2) *
        (d ε + 1) ^ (2 * m ε) := by
  let k := 2 * m ε
  let D := d ε + 1
  have hD : 1 ≤ D := by omega
  have hsum := sum_powers_le_card_mul_pow D k hD
  have hpow : 1 ≤ D ^ k := one_le_pow₀ hD
  have hk : k ≤ k * D ^ k := by nlinarith
  change k * (1 + ∑ j ∈ Finset.range k, D ^ j) ≤
    (k + k ^ 2) * D ^ k
  calc
    k * (1 + ∑ j ∈ Finset.range k, D ^ j) ≤
        k * (1 + k * D ^ k) := by
      exact Nat.mul_le_mul_left k (Nat.add_le_add_left hsum 1)
    _ = k + k ^ 2 * D ^ k := by ring
    _ ≤ k * D ^ k + k ^ 2 * D ^ k := by omega
    _ = (k + k ^ 2) * D ^ k := by ring

theorem choose_m_le_square (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    (Nat.choose (m ε) 2 : ℝ) ≤
      (3 / ε) ^ 2 / 2 := by
  have hchoose :
      (Nat.choose (m ε) 2 : ℝ) ≤ (m ε : ℝ) ^ 2 / 2 := by
    simpa using
      (Nat.choose_le_pow_div (α := ℝ) 2 (m ε))
  have hm := m_le_three_div hε hε1
  have hm0 : 0 ≤ (m ε : ℝ) := Nat.cast_nonneg _
  have hsq : (m ε : ℝ) ^ 2 ≤ (3 / ε) ^ 2 := by
    gcongr
  nlinarith

/-- The paper's convenient coarse cap for d+1; exact ceilings disappear
after this estimate. -/
theorem d_add_one_le_coarse {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (d ε + 1 : ℕ) ≤ (1298 : ℝ) / (mu ε * ε ^ 4) := by
  have hμ : 0 < mu ε := mu_pos hε
  have hμ1 : mu ε ≤ 1 := mu_le_one hε hε1
  have hε4 : 0 < ε ^ 4 := pow_pos hε _
  have hε4le : ε ^ 4 ≤ (1 : ℝ) :=
    pow_le_one₀ hε.le hε1
  have hden : 0 < mu ε * ε ^ 4 := mul_pos hμ hε4
  have hdenle : mu ε * ε ^ 4 ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_right hμ1 hε4.le
    nlinarith
  have hC := choose_m_le_square ε hε hε1
  have hCnum :
      (Nat.choose (m ε) 2 : ℝ) * ε ^ 2 ≤ 9 / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hC (sq_nonneg ε)
    have hsimp : ((3 / ε) ^ 2 / 2) * ε ^ 2 = (9 : ℝ) / 2 := by
      field_simp
      ring
    rw [hsimp] at hmul
    exact hmul
  have hbase :
      288 * (Nat.choose (m ε) 2 : ℝ) * ε ^ 2 ≤ 1296 := by
    nlinarith [hCnum]
  have harg :
      288 * (Nat.choose (m ε) 2 : ℝ) / (mu ε * ε ^ 2) ≤
        1296 / (mu ε * ε ^ 4) := by
    have heq :
        288 * (Nat.choose (m ε) 2 : ℝ) / (mu ε * ε ^ 2) =
          (288 * (Nat.choose (m ε) 2 : ℝ) * ε ^ 2) /
            (mu ε * ε ^ 4) := by
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right hbase hden.le
  have harg0 :
      0 ≤ 288 * (Nat.choose (m ε) 2 : ℝ) /
        (mu ε * ε ^ 2) := by positivity
  have hceil :
      (d ε : ℝ) <
        288 * (Nat.choose (m ε) 2 : ℝ) /
          (mu ε * ε ^ 2) + 1 := by
    unfold d
    exact Nat.ceil_lt_add_one harg0
  have htwo : (2 : ℝ) ≤ 2 / (mu ε * ε ^ 4) := by
    apply (le_div_iff₀ hden).2
    nlinarith [hdenle]
  have hsum :
      1296 / (mu ε * ε ^ 4) +
        2 / (mu ε * ε ^ 4) =
          1298 / (mu ε * ε ^ 4) := by ring
  push_cast
  linarith [harg, hceil, htwo, hsum]

/-- The reciprocal of the rounding parameter is bounded by a power of
`100 / ε`; this is the main exponential estimate for the final constant. -/
theorem mu_inv_le_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (mu ε)⁻¹ ≤ (100 / ε) ^ (300 / ε) := by
  let R : ℝ := 100 / ε
  have hR1 : 1 ≤ R := by
    dsimp [R]
    apply (le_div_iff₀ hε).2
    nlinarith
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR1
  have hr := r_le_five_div hε hε1
  have hbase :
      2400 * (r ε : ℝ) ^ 2 / ε ≤ R ^ 3 := by
    calc
      2400 * (r ε : ℝ) ^ 2 / ε ≤
          2400 * (5 / ε) ^ 2 / ε := by gcongr
      _ = 60000 / ε ^ 3 := by ring
      _ ≤ R ^ 3 := by
        dsimp [R]
        rw [show (100 / ε) ^ 3 = 1000000 / ε ^ 3 by ring]
        exact div_le_div_of_nonneg_right (by norm_num) (pow_nonneg hε.le _)
  have hinv :
      (mu ε)⁻¹ =
        (2400 * (r ε : ℝ) ^ 2 / ε) ^ (20 * r ε) := by
    simp only [mu]
    rw [← inv_pow, inv_div]
  have hexp0 : 60 * (r ε : ℝ) ≤ 300 / ε := by
    calc
      60 * (r ε : ℝ) ≤ 60 * (5 / ε) :=
        mul_le_mul_of_nonneg_left hr (by norm_num)
      _ = 300 / ε := by ring
  have hexp : (3 : ℝ) * (20 * r ε : ℕ) ≤ 300 / ε := by
    convert hexp0 using 1; push_cast; ring
  calc
    (mu ε)⁻¹ =
        (2400 * (r ε : ℝ) ^ 2 / ε) ^ (20 * r ε) := hinv
    _ ≤ (R ^ 3) ^ (20 * r ε) := pow_le_pow_left₀ (by positivity) hbase _
    _ = R ^ ((3 : ℝ) * (20 * r ε : ℕ)) := by
      calc
        (R ^ 3) ^ (20 * r ε) =
            (R ^ 3) ^ ((20 * r ε : ℕ) : ℝ) :=
          (Real.rpow_natCast (R ^ 3) (20 * r ε)).symm
        _ = R ^ (((3 : ℕ) : ℝ) * ((20 * r ε : ℕ) : ℝ)) :=
          (Real.rpow_natCast_mul hR0 3 _).symm
        _ = R ^ ((3 : ℝ) * (20 * r ε : ℕ)) := by norm_num
    _ ≤ R ^ (300 / ε) := Real.rpow_le_rpow_of_exponent_le hR1 hexp
    _ = (100 / ε) ^ (300 / ε) := rfl

/-- A convenient power bound for the augmentation degree cap. -/
theorem d_add_one_le_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (d ε + 1 : ℕ) ≤ (100 / ε) ^ (304 / ε) := by
  let R : ℝ := 100 / ε
  have hR1 : 1 ≤ R := by
    dsimp [R]
    apply (le_div_iff₀ hε).2
    nlinarith
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR1
  have hpoly : 1298 / ε ^ 4 ≤ R ^ 4 := by
    dsimp [R]
    rw [show (100 / ε) ^ 4 = 100000000 / ε ^ 4 by ring]
    exact div_le_div_of_nonneg_right (by norm_num) (pow_nonneg hε.le _)
  have hμ : 0 < mu ε := mu_pos hε
  have hμinv : (mu ε)⁻¹ ≤ R ^ (300 / ε) :=
    mu_inv_le_power hε hε1
  have hexp : 4 + 300 / ε ≤ 304 / ε := by
    have hfour : (4 : ℝ) ≤ 4 / ε := by
      apply (le_div_iff₀ hε).2
      nlinarith
    calc
      4 + 300 / ε ≤ 4 / ε + 300 / ε := by
        simpa only [add_comm] using add_le_add_right hfour (300 / ε)
      _ = 304 / ε := by ring
  calc
    (d ε + 1 : ℕ) ≤ 1298 / (mu ε * ε ^ 4) :=
      d_add_one_le_coarse hε hε1
    _ = (1298 / ε ^ 4) * (mu ε)⁻¹ := by field_simp
    _ ≤ R ^ 4 * R ^ (300 / ε) := by gcongr
    _ = R ^ (4 + 300 / ε) := by
      calc
        R ^ 4 * R ^ (300 / ε) =
            R ^ (300 / ε) * R ^ 4 := mul_comm _ _
        _ = R ^ (300 / ε + 4) :=
          (Real.rpow_add_natCast hRpos.ne' (300 / ε) 4).symm
        _ = R ^ (4 + 300 / ε) := by rw [add_comm]
    _ ≤ R ^ (304 / ε) := Real.rpow_le_rpow_of_exponent_le hR1 hexp
    _ = (100 / ε) ^ (304 / ε) := rfl

/-- The robust fractional-coloring additive term fits well below the final
explicit exponential allowance. -/
theorem robustAdditive_le_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (robustAdditive ε : ℝ) ≤ (100 / ε) ^ (1826 / ε ^ 2) := by
  let R : ℝ := 100 / ε
  let k : ℕ := 2 * m ε
  let D : ℕ := d ε + 1
  have hR1 : 1 ≤ R := by
    dsimp [R]
    apply (le_div_iff₀ hε).2
    nlinarith
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR1
  have hR0 : 0 ≤ R := hRpos.le
  have hk : (k : ℝ) ≤ 6 / ε := by
    calc
      (k : ℝ) = 2 * (m ε : ℝ) := by simp [k]
      _ ≤ 2 * (3 / ε) :=
        mul_le_mul_of_nonneg_left (m_le_three_div hε hε1) (by norm_num)
      _ = 6 / ε := by ring
  have hD : (D : ℝ) ≤ R ^ (304 / ε) :=
    d_add_one_le_power hε hε1
  have hexp : (304 / ε) * (k : ℝ) ≤ 1824 / ε ^ 2 := by
    calc
      (304 / ε) * (k : ℝ) ≤ (304 / ε) * (6 / ε) :=
        mul_le_mul_of_nonneg_left hk (by positivity)
      _ = 1824 / ε ^ 2 := by ring
  have hDpow : (D : ℝ) ^ k ≤ R ^ (1824 / ε ^ 2) := by
    calc
      (D : ℝ) ^ k ≤ (R ^ (304 / ε)) ^ k := by gcongr
      _ = R ^ ((304 / ε) * (k : ℝ)) :=
        (Real.rpow_mul_natCast hR0 (304 / ε) k).symm
      _ ≤ R ^ (1824 / ε ^ 2) :=
        Real.rpow_le_rpow_of_exponent_le hR1 hexp
  have ht1 : (1 : ℝ) ≤ 1 / ε := by
    apply (le_div_iff₀ hε).2
    simpa using hε1
  have ht0 : (0 : ℝ) ≤ 1 / ε := by positivity
  have ht2 : 1 / ε ≤ (1 / ε) ^ 2 := by
    calc
      1 / ε = (1 / ε) * 1 := by ring
      _ ≤ (1 / ε) * (1 / ε) := mul_le_mul_of_nonneg_left ht1 ht0
      _ = (1 / ε) ^ 2 := by ring
  have hkt : (k : ℝ) ≤ 6 * (1 / ε) := by
    calc
      (k : ℝ) ≤ 6 / ε := hk
      _ = 6 * (1 / ε) := by ring
  have hkt2 : (k : ℝ) ^ 2 ≤ (6 * (1 / ε)) ^ 2 := by gcongr
  have hkterm : (k : ℝ) ≤ 6 * (1 / ε) ^ 2 := by
    calc
      (k : ℝ) ≤ 6 * (1 / ε) := hkt
      _ ≤ 6 * (1 / ε) ^ 2 :=
        mul_le_mul_of_nonneg_left ht2 (by norm_num)
  have hcoef : ((k + k ^ 2 : ℕ) : ℝ) ≤ R ^ 2 := by
    have hRt : R ^ 2 = 10000 * (1 / ε) ^ 2 := by
      dsimp [R]
      ring
    rw [hRt]
    push_cast
    nlinarith [hkt2, hkterm, sq_nonneg (1 / ε)]
  have hsimple :
      (robustAdditive ε : ℝ) ≤
        ((k + k ^ 2 : ℕ) : ℝ) * (D : ℝ) ^ k := by
    exact_mod_cast robustAdditive_le_simple ε
  have hε2le : ε ^ 2 ≤ (1 : ℝ) := pow_le_one₀ hε.le hε1
  have htwo : (2 : ℝ) ≤ 2 / ε ^ 2 := by
    apply (le_div_iff₀ (pow_pos hε _)).2
    nlinarith
  have hfinalexp : 1824 / ε ^ 2 + 2 ≤ 1826 / ε ^ 2 := by
    calc
      1824 / ε ^ 2 + 2 ≤ 1824 / ε ^ 2 + 2 / ε ^ 2 :=
        by simpa only [add_comm] using add_le_add_left htwo (1824 / ε ^ 2)
      _ = 1826 / ε ^ 2 := by ring
  calc
    (robustAdditive ε : ℝ) ≤
        ((k + k ^ 2 : ℕ) : ℝ) * (D : ℝ) ^ k := hsimple
    _ ≤ R ^ 2 * R ^ (1824 / ε ^ 2) := by gcongr
    _ = R ^ (1824 / ε ^ 2 + 2) := by
      calc
        R ^ 2 * R ^ (1824 / ε ^ 2) =
            R ^ (1824 / ε ^ 2) * R ^ 2 := mul_comm _ _
        _ = R ^ (1824 / ε ^ 2 + 2) :=
          (Real.rpow_add_natCast hRpos.ne' (1824 / ε ^ 2) 2).symm
    _ ≤ R ^ (1826 / ε ^ 2) :=
      Real.rpow_le_rpow_of_exponent_le hR1 hfinalexp
    _ = (100 / ε) ^ (1826 / ε ^ 2) := rfl

/-- The small-order threshold is dominated by a much smaller power than
the allowance in Theorem 2. -/
theorem n0_le_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (n0 ε : ℝ) ≤ (100 / ε) ^ (1208 / ε ^ 2) := by
  let R : ℝ := 100 / ε
  have hR1 : 1 ≤ R := by
    dsimp [R]
    apply (le_div_iff₀ hε).2
    nlinarith
  have hR100 : (100 : ℝ) ≤ R := by
    dsimp [R]
    apply (le_div_iff₀ hε).2
    nlinarith
  have hR2 : (2 : ℝ) ≤ R := by linarith
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR1
  have hR0 : 0 ≤ R := hRpos.le
  have hrR : (r ε : ℝ) ≤ R := by
    calc
      (r ε : ℝ) ≤ 5 / ε := r_le_five_div hε hε1
      _ ≤ 100 / ε :=
        div_le_div_of_nonneg_right (by norm_num) hε.le
      _ = R := rfl
  have hR3 : (1000000 : ℝ) ≤ R ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) hR100 3
    norm_num at h
    exact h
  have hlead : 1000000 * (r ε : ℝ) ^ 4 ≤ R ^ 7 := by
    have hr4 : (r ε : ℝ) ^ 4 ≤ R ^ 4 := by gcongr
    calc
      1000000 * (r ε : ℝ) ^ 4 ≤ R ^ 3 * R ^ 4 := by gcongr
      _ = R ^ 7 := by ring
  have hμ : 0 < mu ε := mu_pos hε
  have hμinv1 : 1 ≤ (mu ε)⁻¹ :=
    (one_le_inv₀ hμ).2 (mu_le_one hε hε1)
  have hμinv4 : 1 ≤ ((mu ε)⁻¹) ^ 4 := one_le_pow₀ hμinv1
  have h12 : 12 / ε ≤ R := by
    dsimp [R]
    exact div_le_div_of_nonneg_right (by norm_num) hε.le
  have harg0 :
      0 ≤ 1000000 * (r ε : ℝ) ^ 4 * ((mu ε)⁻¹) ^ 4 + 12 / ε := by
    positivity
  have hceil :
      (n0 ε : ℝ) <
        1000000 * (r ε : ℝ) ^ 4 * ((mu ε)⁻¹) ^ 4 +
          12 / ε + 1 := by
    unfold n0
    exact Nat.ceil_lt_add_one harg0
  have hfirst :
      1000000 * (r ε : ℝ) ^ 4 * ((mu ε)⁻¹) ^ 4 ≤
        R ^ 7 * ((mu ε)⁻¹) ^ 4 :=
    mul_le_mul_of_nonneg_right hlead (pow_nonneg (inv_nonneg.mpr hμ.le) _)
  have hR2sq : 2 * R ≤ R ^ 2 := by
    calc
      2 * R ≤ R * R := mul_le_mul_of_nonneg_right hR2 hR0
      _ = R ^ 2 := by ring
  have hR2pow : R ^ 2 ≤ R ^ 7 :=
    pow_le_pow_right₀ hR1 (by norm_num)
  have htail : 12 / ε + 1 ≤ R ^ 7 * ((mu ε)⁻¹) ^ 4 := by
    calc
      12 / ε + 1 ≤ 2 * R := by linarith
      _ ≤ R ^ 2 := hR2sq
      _ ≤ R ^ 7 := hR2pow
      _ = R ^ 7 * 1 := by ring
      _ ≤ R ^ 7 * ((mu ε)⁻¹) ^ 4 :=
        mul_le_mul_of_nonneg_left hμinv4 (pow_nonneg hR0 _)
  have hR8 : 2 * R ^ 7 ≤ R ^ 8 := by
    calc
      2 * R ^ 7 ≤ R * R ^ 7 :=
        mul_le_mul_of_nonneg_right hR2 (pow_nonneg hR0 _)
      _ = R ^ 8 := by ring
  have hrough : (n0 ε : ℝ) ≤ R ^ 8 * ((mu ε)⁻¹) ^ 4 := by
    have hmid :
        (n0 ε : ℝ) ≤ 2 * (R ^ 7 * ((mu ε)⁻¹) ^ 4) := by
      linarith [hceil, hfirst, htail]
    calc
      (n0 ε : ℝ) ≤ 2 * (R ^ 7 * ((mu ε)⁻¹) ^ 4) := hmid
      _ = (2 * R ^ 7) * ((mu ε)⁻¹) ^ 4 := by ring
      _ ≤ R ^ 8 * ((mu ε)⁻¹) ^ 4 :=
        mul_le_mul_of_nonneg_right hR8 (pow_nonneg (inv_nonneg.mpr hμ.le) _)
  have hμpow : ((mu ε)⁻¹) ^ 4 ≤ R ^ (1200 / ε) := by
    calc
      ((mu ε)⁻¹) ^ 4 ≤ (R ^ (300 / ε)) ^ 4 := by
        gcongr
        exact mu_inv_le_power hε hε1
      _ = R ^ ((300 / ε) * 4) :=
        (Real.rpow_mul_natCast hR0 (300 / ε) 4).symm
      _ = R ^ (1200 / ε) := by congr 1; ring
  have hε2le : ε ^ 2 ≤ (1 : ℝ) := pow_le_one₀ hε.le hε1
  have hε2leε : ε ^ 2 ≤ ε := by
    nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hε1)]
  have h1200 : 1200 / ε ≤ 1200 / ε ^ 2 := by
    apply (div_le_div_iff₀ hε (pow_pos hε _)).2
    nlinarith
  have h8 : (8 : ℝ) ≤ 8 / ε ^ 2 := by
    apply (le_div_iff₀ (pow_pos hε _)).2
    nlinarith
  have hexp : 1200 / ε + 8 ≤ 1208 / ε ^ 2 := by
    calc
      1200 / ε + 8 ≤ 1200 / ε ^ 2 + 8 / ε ^ 2 :=
        add_le_add h1200 h8
      _ = 1208 / ε ^ 2 := by ring
  calc
    (n0 ε : ℝ) ≤ R ^ 8 * ((mu ε)⁻¹) ^ 4 := hrough
    _ ≤ R ^ 8 * R ^ (1200 / ε) := by gcongr
    _ = R ^ (1200 / ε + 8) := by
      calc
        R ^ 8 * R ^ (1200 / ε) =
            R ^ (1200 / ε) * R ^ 8 := mul_comm _ _
        _ = R ^ (1200 / ε + 8) :=
          (Real.rpow_add_natCast hRpos.ne' (1200 / ε) 8).symm
    _ ≤ R ^ (1208 / ε ^ 2) :=
      Real.rpow_le_rpow_of_exponent_le hR1 hexp
    _ = (100 / ε) ^ (1208 / ε ^ 2) := rfl

/-- The explicit constant chosen in the paper dominates both intermediate
additive terms. -/
theorem A_le_Aepsilon {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (A ε : ℝ) ≤ Aepsilon ε := by
  have hR1 : (1 : ℝ) ≤ 100 / ε := by
    apply (le_div_iff₀ hε).2
    nlinarith
  have hε2 : 0 ≤ ε ^ 2 := pow_nonneg hε.le _
  have hnexp : 1208 / ε ^ 2 ≤ 2000 / ε ^ 2 :=
    div_le_div_of_nonneg_right (by norm_num) hε2
  have hrexp : 1826 / ε ^ 2 ≤ 2000 / ε ^ 2 :=
    div_le_div_of_nonneg_right (by norm_num) hε2
  have hn := (n0_le_power hε hε1).trans
    (Real.rpow_le_rpow_of_exponent_le hR1 hnexp)
  have hr := (robustAdditive_le_power hε hε1).trans
    (Real.rpow_le_rpow_of_exponent_le hR1 hrexp)
  unfold A Aepsilon
  rw [Nat.cast_max]
  exact max_le hn hr
end HadwigerLean.Theorem2