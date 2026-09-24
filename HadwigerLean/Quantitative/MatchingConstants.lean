import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Numerical parameters for the almost-perfect matching iteration

The paper's logarithmic schedule is kept here, separate from the
combinatorial and probabilistic hypergraph lemmas. Intermediate bounds may
be weakened whenever the final covering error still fits.
-/

namespace HadwigerLean.Theorem2

noncomputable def matchingL (ξ : ℝ) : ℝ := Real.log (4 / ξ)
noncomputable def matchingA (r : ℕ) (ξ : ℝ) : ℝ :=
  ξ / (100 * (r : ℝ) * matchingL ξ)
noncomputable def matchingQ (r : ℕ) (ξ : ℝ) : ℝ :=
  Real.exp (-matchingA r ξ)
noncomputable def matchingT (r : ℕ) (ξ : ℝ) : ℕ :=
  ⌈matchingL ξ / matchingA r ξ⌉₊
noncomputable def matchingMu (r : ℕ) (ξ : ℝ) : ℝ :=
  (ξ / (100 * (r : ℝ))) ^ (20 * r)
noncomputable def matchingB (r : ℕ) (ξ : ℝ) : ℝ :=
  2 * matchingMu r ξ * (4 / ξ) ^ (2 * r)

theorem matchingL_ge_one {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    1 ≤ matchingL ξ := by
  have hfour : (4 : ℝ) ≤ 4 / ξ := by
    apply (le_div_iff₀ hξ).2
    nlinarith
  have harg : 0 < 4 / ξ := div_pos (by norm_num) hξ
  unfold matchingL
  apply (Real.le_log_iff_exp_le harg).2
  exact (Real.exp_one_lt_three.le.trans (by norm_num : (3 : ℝ) ≤ 4)).trans hfour

theorem matchingL_le_four_div {ξ : ℝ} (hξ : 0 < ξ) :
    matchingL ξ ≤ 4 / ξ := by
  unfold matchingL
  exact Real.log_le_self (div_nonneg (by norm_num) hξ.le)

theorem matchingA_pos {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    0 < matchingA r ξ := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hL : 0 < matchingL ξ := lt_of_lt_of_le zero_lt_one (matchingL_ge_one hξ hξ1)
  unfold matchingA
  positivity

theorem matchingA_mul_r_le {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingA r ξ * (r : ℝ) ≤ 1 / 100 := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hL := matchingL_ge_one hξ hξ1
  have hLpos : 0 < matchingL ξ := lt_of_lt_of_le zero_lt_one hL
  have hξL : ξ ≤ matchingL ξ := hξ1.trans hL
  unfold matchingA
  have heq :
      ξ / (100 * (r : ℝ) * matchingL ξ) * (r : ℝ) =
        ξ / (100 * matchingL ξ) := by
    field_simp
  rw [heq]
  apply (div_le_iff₀ (by positivity : 0 < 100 * matchingL ξ)).2
  nlinarith [hξL]

theorem matchingA_le_L {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingA r ξ ≤ matchingL ξ := by
  have ha := matchingA_mul_r_le hr hξ hξ1
  have ha0 := (matchingA_pos hr hξ hξ1).le
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
  have hsmall : matchingA r ξ ≤ matchingA r ξ * (r : ℝ) := by
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hr1)]
  have hL := matchingL_ge_one hξ hξ1
  linarith

theorem matchingQ_pos {r : ℕ} {ξ : ℝ} :
    0 < matchingQ r ξ := by unfold matchingQ; positivity

theorem matchingQ_le_one {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingQ r ξ ≤ 1 := by
  unfold matchingQ
  have ha := matchingA_pos hr hξ hξ1
  simpa using (Real.exp_le_exp.mpr (show -matchingA r ξ ≤ 0 by linarith))

theorem matchingA_mul_T_bounds {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingL ξ ≤ matchingA r ξ * (matchingT r ξ : ℝ) ∧
      matchingA r ξ * (matchingT r ξ : ℝ) ≤ 2 * matchingL ξ := by
  have ha := matchingA_pos hr hξ hξ1
  have hL := matchingL_ge_one hξ hξ1
  have hquot : 0 ≤ matchingL ξ / matchingA r ξ :=
    div_nonneg (by linarith) ha.le
  have hceil :
      matchingL ξ / matchingA r ξ ≤ (matchingT r ξ : ℝ) := by
    unfold matchingT
    exact Nat.le_ceil _
  have hceilUpper :
      (matchingT r ξ : ℝ) < matchingL ξ / matchingA r ξ + 1 := by
    unfold matchingT
    exact Nat.ceil_lt_add_one hquot
  have hlow := mul_le_mul_of_nonneg_left hceil ha.le
  have hupp := mul_lt_mul_of_pos_left hceilUpper ha
  have hident :
      matchingA r ξ * (matchingL ξ / matchingA r ξ) = matchingL ξ := by
    field_simp
  constructor
  · nlinarith [hlow]
  · have haL := matchingA_le_L hr hξ hξ1
    nlinarith [hupp]

theorem matchingQ_pow_T_le {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingQ r ξ ^ matchingT r ξ ≤ ξ / 4 := by
  have hLT := (matchingA_mul_T_bounds hr hξ hξ1).1
  have hξ4 : 0 < 4 / ξ := div_pos (by norm_num) hξ
  have hqpow :
      matchingQ r ξ ^ matchingT r ξ =
        Real.exp (-(matchingA r ξ * (matchingT r ξ : ℝ))) := by
    unfold matchingQ
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hqpow]
  calc
    Real.exp (-(matchingA r ξ * (matchingT r ξ : ℝ))) ≤
        Real.exp (-matchingL ξ) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = ξ / 4 := by
      unfold matchingL
      rw [Real.exp_neg, Real.exp_log hξ4]
      field_simp


/-- A direct small-base estimate for the paper's codegree error. -/
theorem matchingB_le_base_pow_ten {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingB r ξ ≤ (ξ / (100 * (r : ℝ))) ^ 10 := by
  let t : ℝ := ξ / (100 * (r : ℝ))
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : 0 < (r : ℝ) := by linarith
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have htHalf : t ≤ 1 / 2 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < 100 * (r : ℝ))).2
    nlinarith
  have hpair : t * (4 / ξ) ≤ 1 := by
    have heq : t * (4 / ξ) = 4 / (100 * (r : ℝ)) := by
      dsimp [t]
      field_simp
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < 100 * (r : ℝ))).2
    nlinarith
  have hpairpow : (t * (4 / ξ)) ^ (2 * r) ≤ 1 :=
    pow_le_one₀ (mul_nonneg ht0 (div_nonneg (by norm_num) hξ.le)) hpair
  have hfactor :
      matchingB r ξ = 2 * t ^ (18 * r) * (t * (4 / ξ)) ^ (2 * r) := by
    change 2 * t ^ (20 * r) * (4 / ξ) ^ (2 * r) =
      2 * t ^ (18 * r) * (t * (4 / ξ)) ^ (2 * r)
    have hexp : 20 * r = 18 * r + 2 * r := by omega
    rw [hexp, pow_add, mul_pow]
    ring
  have hpow : t ^ (18 * r) ≤ t ^ 11 :=
    pow_le_pow_of_le_one ht0 (by linarith : t ≤ 1) (by omega : 11 ≤ 18 * r)
  have htwo : 2 * t ≤ 1 := by linarith [htHalf]
  calc
    matchingB r ξ = 2 * t ^ (18 * r) * (t * (4 / ξ)) ^ (2 * r) := hfactor
    _ ≤ 2 * t ^ (18 * r) := by
      nlinarith [mul_le_mul_of_nonneg_left hpairpow (by positivity : 0 ≤ 2 * t ^ (18 * r))]
    _ ≤ 2 * t ^ 11 := by gcongr
    _ = t ^ 10 * (2 * t) := by ring
    _ ≤ t ^ 10 := by
      nlinarith [mul_le_mul_of_nonneg_left htwo (pow_nonneg ht0 10)]
    _ = (ξ / (100 * (r : ℝ))) ^ 10 := rfl

theorem matchingB_sqrt_le {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    Real.sqrt (matchingB r ξ) ≤ ξ ^ 5 / (100000000 * (r : ℝ) ^ 3) := by
  let t : ℝ := ξ / (100 * (r : ℝ))
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : 0 < (r : ℝ) := by linarith
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hB := matchingB_le_base_pow_ten hr hξ hξ1
  have hsqrt : Real.sqrt (matchingB r ξ) ≤ t ^ 5 := by
    have h := Real.sqrt_le_sqrt hB
    have heq : Real.sqrt (t ^ 10) = t ^ 5 := by
      calc
        Real.sqrt (t ^ 10) = Real.sqrt ((t ^ 5) ^ 2) := by congr 1; ring
        _ = |t ^ 5| := Real.sqrt_sq_eq_abs _
        _ = t ^ 5 := abs_of_nonneg (pow_nonneg ht0 _)
    rwa [heq] at h
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by linarith
  have hr2 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := one_le_pow₀ hr1
  have hden :
      100000000 * (r : ℝ) ^ 3 ≤ (100 * (r : ℝ)) ^ 5 := by
    have hmul := mul_le_mul_of_nonneg_left hr2
      (by positivity : 0 ≤ 10000000000 * (r : ℝ) ^ 3)
    nlinarith [hmul]
  have hdenpos : 0 < 100000000 * (r : ℝ) ^ 3 := by positivity
  calc
    Real.sqrt (matchingB r ξ) ≤ t ^ 5 := hsqrt
    _ = ξ ^ 5 / (100 * (r : ℝ)) ^ 5 := by dsimp [t]; ring
    _ ≤ ξ ^ 5 / (100000000 * (r : ℝ) ^ 3) :=
      div_le_div_of_nonneg_left (pow_nonneg hξ.le _) hdenpos hden

theorem matchingA_ge_quadratic {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    ξ ^ 2 / (400 * (r : ℝ)) ≤ matchingA r ξ := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hLpos : 0 < matchingL ξ :=
    lt_of_lt_of_le zero_lt_one (matchingL_ge_one hξ hξ1)
  have hLbound := matchingL_le_four_div hξ
  have hξL : ξ * matchingL ξ ≤ 4 := by
    have h := mul_le_mul_of_nonneg_left hLbound hξ.le
    have heq : ξ * (4 / ξ) = 4 := by field_simp
    rw [heq] at h
    exact h
  have hfactor : ξ / 4 ≤ 1 / matchingL ξ := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) hLpos).2
    nlinarith [hξL]
  have hnum : 0 ≤ ξ / (100 * (r : ℝ)) := by positivity
  calc
    ξ ^ 2 / (400 * (r : ℝ)) =
        (ξ / (100 * (r : ℝ))) * (ξ / 4) := by ring
    _ ≤ (ξ / (100 * (r : ℝ))) * (1 / matchingL ξ) :=
      mul_le_mul_of_nonneg_left hfactor hnum
    _ = matchingA r ξ := by unfold matchingA; field_simp

theorem matchingMu_le_quadratic {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingMu r ξ ≤ ξ ^ 2 / 800 := by
  let t : ℝ := ξ / (100 * (r : ℝ))
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : 0 < (r : ℝ) := by linarith
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < 100 * (r : ℝ))).2
    nlinarith
  have hpow : matchingMu r ξ ≤ t ^ 2 := by
    unfold matchingMu
    exact pow_le_pow_of_le_one ht0 ht1 (by omega : 2 ≤ 20 * r)
  have hden : (800 : ℝ) ≤ (100 * (r : ℝ)) ^ 2 := by
    have hbase : (200 : ℝ) ≤ 100 * (r : ℝ) := by nlinarith
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 200) hbase 2
    nlinarith [hsq]
  calc
    matchingMu r ξ ≤ t ^ 2 := hpow
    _ = ξ ^ 2 / (100 * (r : ℝ)) ^ 2 := by dsimp [t]; ring
    _ ≤ ξ ^ 2 / 800 :=
      div_le_div_of_nonneg_left (sq_nonneg ξ) (by norm_num) hden

theorem matchingB_le_a_quarter {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingB r ξ ≤ matchingA r ξ / 4 := by
  let t : ℝ := ξ / (100 * (r : ℝ))
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < 100 * (r : ℝ))).2
    nlinarith
  have hden : (1600 * (r : ℝ)) ≤ (100 * (r : ℝ)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrR) (by norm_num : (0 : ℝ) ≤ 10000 * (r : ℝ))]
  have hsmall : t ^ 2 ≤ ξ ^ 2 / (1600 * (r : ℝ)) := by
    calc
      t ^ 2 = ξ ^ 2 / (100 * (r : ℝ)) ^ 2 := by dsimp [t]; ring
      _ ≤ ξ ^ 2 / (1600 * (r : ℝ)) :=
        div_le_div_of_nonneg_left (sq_nonneg ξ)
          (by positivity) hden
  calc
    matchingB r ξ ≤ t ^ 10 := matchingB_le_base_pow_ten hr hξ hξ1
    _ ≤ t ^ 2 := pow_le_pow_of_le_one ht0 ht1 (by norm_num)
    _ ≤ ξ ^ 2 / (1600 * (r : ℝ)) := hsmall
    _ = (ξ ^ 2 / (400 * (r : ℝ))) / 4 := by ring
    _ ≤ matchingA r ξ / 4 := by
      gcongr
      exact matchingA_ge_quadratic hr hξ hξ1

/-- Multiplicative degree decay before taking integer floors. -/
noncomputable def matchingLambda (r : ℕ) (ξ : ℝ) : ℝ :=
  matchingQ r ξ ^ (r - 1)

/-- Recursive integer degree caps, exactly as in the paper. -/
noncomputable def matchingD (D₀ r : ℕ) (ξ : ℝ) : ℕ → ℕ
  | 0 => D₀
  | i + 1 => ⌊matchingLambda r ξ * (matchingD D₀ r ξ i : ℝ)⌋₊

theorem matchingLambda_pos (r : ℕ) (ξ : ℝ) :
    0 < matchingLambda r ξ := by
  unfold matchingLambda
  exact pow_pos matchingQ_pos _

theorem matchingLambda_le_one {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingLambda r ξ ≤ 1 := by
  unfold matchingLambda
  exact pow_le_one₀ (matchingQ_pos.le) (matchingQ_le_one hr hξ hξ1)

theorem matchingLambda_eq_exp {r : ℕ} {ξ : ℝ} (hr : 2 ≤ r) :
    matchingLambda r ξ =
      Real.exp ((1 - (r : ℝ)) * matchingA r ξ) := by
  unfold matchingLambda matchingQ
  rw [← Real.exp_nat_mul]
  congr 1
  have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r)]
    norm_num
  rw [hcast]
  ring

theorem matchingLambda_mul_q_eq_exp {r : ℕ} {ξ : ℝ} (hr : 2 ≤ r) :
    matchingLambda r ξ * matchingQ r ξ =
      Real.exp (-(r : ℝ) * matchingA r ξ) := by
  have hsub : r - 1 + 1 = r := Nat.sub_add_cancel (by omega : 1 ≤ r)
  unfold matchingLambda matchingQ
  rw [← pow_succ, hsub, ← Real.exp_nat_mul]
  congr 1
  ring

theorem matchingD_next_le {D₀ r i : ℕ} {ξ : ℝ} :
    (matchingD D₀ r ξ (i + 1) : ℝ) ≤
      matchingLambda r ξ * (matchingD D₀ r ξ i : ℝ) := by
  simp only [matchingD]
  exact Nat.floor_le (mul_nonneg (matchingLambda_pos r ξ).le (Nat.cast_nonneg _))

theorem matchingD_next_lt_add_one {D₀ r i : ℕ} {ξ : ℝ} :
    matchingLambda r ξ * (matchingD D₀ r ξ i : ℝ) <
      (matchingD D₀ r ξ (i + 1) : ℝ) + 1 := by
  simp only [matchingD]
  exact Nat.lt_floor_add_one _

theorem matchingD_next_le_exp {D₀ r i : ℕ} {ξ : ℝ} (hr : 2 ≤ r) :
    (matchingD D₀ r ξ (i + 1) : ℝ) * matchingQ r ξ ≤
      (matchingD D₀ r ξ i : ℝ) *
        Real.exp (-(r : ℝ) * matchingA r ξ) := by
  have hq : 0 < matchingQ r ξ := matchingQ_pos
  calc
    (matchingD D₀ r ξ (i + 1) : ℝ) * matchingQ r ξ ≤
        (matchingLambda r ξ * (matchingD D₀ r ξ i : ℝ)) * matchingQ r ξ :=
      mul_le_mul_of_nonneg_right matchingD_next_le hq.le
    _ = (matchingD D₀ r ξ i : ℝ) *
          (matchingLambda r ξ * matchingQ r ξ) := by ring
    _ = (matchingD D₀ r ξ i : ℝ) *
          Real.exp (-(r : ℝ) * matchingA r ξ) := by
      rw [matchingLambda_mul_q_eq_exp hr]
theorem matchingD_rounding_loss {D₀ r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (i : ℕ) :
    matchingLambda r ξ ^ i * (D₀ : ℝ) ≤
      (matchingD D₀ r ξ i : ℝ) + (i : ℝ) := by
  induction i with
  | zero => simp [matchingD]
  | succ i ih =>
      have hLambda0 := (matchingLambda_pos r ξ).le
      have hLambda1 := matchingLambda_le_one hr hξ hξ1
      have hstep := matchingD_next_lt_add_one (D₀ := D₀) (r := r) (i := i) (ξ := ξ)
      calc
        matchingLambda r ξ ^ (i + 1) * (D₀ : ℝ) =
            matchingLambda r ξ * (matchingLambda r ξ ^ i * (D₀ : ℝ)) := by ring
        _ ≤ matchingLambda r ξ * ((matchingD D₀ r ξ i : ℝ) + (i : ℝ)) :=
          mul_le_mul_of_nonneg_left ih hLambda0
        _ ≤ matchingLambda r ξ * (matchingD D₀ r ξ i : ℝ) + (i : ℝ) := by
          have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg _
          nlinarith [mul_le_mul_of_nonneg_right hLambda1 hi0]
        _ ≤ (matchingD D₀ r ξ (i + 1) : ℝ) + ((i + 1 : ℕ) : ℝ) := by
          push_cast
          linarith
theorem matchingT_cubic_bound {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    (matchingT r ξ : ℝ) * ξ ^ 3 ≤ 3200 * (r : ℝ) := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hT0 : 0 ≤ (matchingT r ξ : ℝ) := Nat.cast_nonneg _
  have hLbound := matchingL_le_four_div hξ
  have hLxi : ξ * matchingL ξ ≤ 4 := by
    have h := mul_le_mul_of_nonneg_left hLbound hξ.le
    have heq : ξ * (4 / ξ) = 4 := by field_simp
    rw [heq] at h
    exact h
  have haT := (matchingA_mul_T_bounds hr hξ hξ1).2
  have hTxi : matchingA r ξ * (matchingT r ξ : ℝ) * ξ ≤ 8 := by
    have h := mul_le_mul_of_nonneg_right haT hξ.le
    nlinarith [hLxi]
  have ha2 : ξ ^ 2 ≤ 400 * (r : ℝ) * matchingA r ξ := by
    have h := matchingA_ge_quadratic hr hξ hξ1
    apply (div_le_iff₀ (by positivity : 0 < 400 * (r : ℝ))).1 at h
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right ha2 hT0
  have hmulxi := mul_le_mul_of_nonneg_right hmul hξ.le
  have hbound := mul_le_mul_of_nonneg_left hTxi
    (by positivity : 0 ≤ 400 * (r : ℝ))
  nlinarith [hmulxi, hbound]
theorem matchingB_le_cubic {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingB r ξ ≤ ξ ^ 3 / (10000 * (r : ℝ)) := by
  let t : ℝ := ξ / (100 * (r : ℝ))
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : 0 < (r : ℝ) := by linarith
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < 100 * (r : ℝ))).2
    nlinarith
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by linarith
  have hr2 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := one_le_pow₀ hr1
  have hpow := mul_le_mul_of_nonneg_left hr2 hrpos.le
  have hden : 10000 * (r : ℝ) ≤ (100 * (r : ℝ)) ^ 3 := by
    nlinarith [hpow]
  calc
    matchingB r ξ ≤ t ^ 10 := matchingB_le_base_pow_ten hr hξ hξ1
    _ ≤ t ^ 3 := pow_le_pow_of_le_one ht0 ht1 (by norm_num)
    _ = ξ ^ 3 / (100 * (r : ℝ)) ^ 3 := by dsimp [t]; ring
    _ ≤ ξ ^ 3 / (10000 * (r : ℝ)) :=
      div_le_div_of_nonneg_left (pow_nonneg hξ.le _) (by positivity) hden

theorem matchingB_mul_T_le_one {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingB r ξ * (matchingT r ξ : ℝ) ≤ 1 := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hT0 : 0 ≤ (matchingT r ξ : ℝ) := Nat.cast_nonneg _
  have hb := matchingB_le_cubic hr hξ hξ1
  have hbT := mul_le_mul_of_nonneg_right hb hT0
  have hT := matchingT_cubic_bound hr hξ hξ1
  have hscaled := mul_le_mul_of_nonneg_right hbT
    (by positivity : 0 ≤ 10000 * (r : ℝ))
  have heq :
      ξ ^ 3 / (10000 * (r : ℝ)) *
        (matchingT r ξ : ℝ) * (10000 * (r : ℝ)) =
      (matchingT r ξ : ℝ) * ξ ^ 3 := by field_simp
  rw [heq] at hscaled
  by_contra hnot
  have hgt : 1 < matchingB r ξ * (matchingT r ξ : ℝ) := lt_of_not_ge hnot
  have hprod : 0 < (matchingB r ξ * (matchingT r ξ : ℝ) - 1) * (r : ℝ) :=
    mul_pos (by linarith) hrpos
  nlinarith [hscaled, hT, hprod]
theorem matchingLambda_pow_lower {r i : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hi : i ≤ matchingT r ξ) :
    (ξ / 4) ^ (2 * r) ≤ matchingLambda r ξ ^ i := by
  have ha0 := (matchingA_pos hr hξ hξ1).le
  have hL0 : 0 ≤ matchingL ξ :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (matchingL_ge_one hξ hξ1)
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hiReal : (i : ℝ) ≤ (matchingT r ξ : ℝ) := by exact_mod_cast hi
  have hai : matchingA r ξ * (i : ℝ) ≤ 2 * matchingL ξ := by
    have h := mul_le_mul_of_nonneg_left hiReal ha0
    have hT := (matchingA_mul_T_bounds hr hξ hξ1).2
    linarith
  have hri : 0 ≤ (r : ℝ) - 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hai hri
  have hexpArg :
      -(2 * (r : ℝ) * matchingL ξ) ≤
        ((1 - (r : ℝ)) * matchingA r ξ) * (i : ℝ) := by
    nlinarith [hmul]
  have hpow :
      matchingLambda r ξ ^ i =
        Real.exp (((1 - (r : ℝ)) * matchingA r ξ) * (i : ℝ)) := by
    rw [matchingLambda_eq_exp hr, ← Real.exp_nat_mul]
    congr 1
    ring
  have hleft :
      Real.exp (-(2 * (r : ℝ) * matchingL ξ)) =
        (ξ / 4) ^ (2 * r) := by
    have hξ4 : 0 < 4 / ξ := div_pos (by norm_num) hξ
    have hbase : Real.exp (-matchingL ξ) = ξ / 4 := by
      unfold matchingL
      rw [Real.exp_neg, Real.exp_log hξ4]
      field_simp
    calc
      Real.exp (-(2 * (r : ℝ) * matchingL ξ)) =
          Real.exp (-matchingL ξ) ^ (2 * r) := by
            rw [← Real.exp_nat_mul]
            congr 1
            push_cast
            ring
      _ = (ξ / 4) ^ (2 * r) := by rw [hbase]
  rw [← hleft, hpow]
  exact Real.exp_le_exp.mpr hexpArg
theorem matchingB_mul_decay_base {r : ℕ} {ξ : ℝ}
    (hξ : 0 < ξ) :
    matchingB r ξ * (ξ / 4) ^ (2 * r) =
      2 * matchingMu r ξ := by
  have hcancel : (4 / ξ) * (ξ / 4) = 1 := by field_simp
  calc
    matchingB r ξ * (ξ / 4) ^ (2 * r) =
        2 * matchingMu r ξ *
          ((4 / ξ) * (ξ / 4)) ^ (2 * r) := by
            unfold matchingB
            rw [mul_pow]
            ring
    _ = 2 * matchingMu r ξ := by rw [hcancel]; simp

theorem matchingB_pos {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) : 0 < matchingB r ξ := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  unfold matchingB matchingMu
  positivity

/-- The initial codegree cap absorbs every floor loss in the schedule. -/
theorem matchingD_codegree_invariant {D₀ B r i : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hBmin : 1 ≤ B)
    (hBmax : (B : ℝ) ≤ matchingMu r ξ * (D₀ : ℝ))
    (hi : i ≤ matchingT r ξ) :
    (B : ℝ) ≤ matchingB r ξ * (matchingD D₀ r ξ i : ℝ) := by
  have hb0 := (matchingB_pos (r := r) hr hξ).le
  have hiReal : (i : ℝ) ≤ (matchingT r ξ : ℝ) := by exact_mod_cast hi
  have hround := matchingD_rounding_loss (D₀ := D₀) hr hξ hξ1 i
  have hdecay := matchingLambda_pow_lower hr hξ hξ1 hi
  have hD0 : 0 ≤ (D₀ : ℝ) := Nat.cast_nonneg _
  have hbulk :
      (ξ / 4) ^ (2 * r) * (D₀ : ℝ) ≤
        (matchingD D₀ r ξ i : ℝ) + (i : ℝ) :=
    (mul_le_mul_of_nonneg_right hdecay hD0).trans hround
  have hscaled := mul_le_mul_of_nonneg_left hbulk hb0
  have hscaleeq :
      matchingB r ξ * ((ξ / 4) ^ (2 * r) * (D₀ : ℝ)) =
        2 * matchingMu r ξ * (D₀ : ℝ) := by
    rw [← mul_assoc, matchingB_mul_decay_base hξ]
  rw [hscaleeq] at hscaled
  have hbi : matchingB r ξ * (i : ℝ) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hiReal hb0).trans
      (matchingB_mul_T_le_one hr hξ hξ1)
  have hBminR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hBmin
  nlinarith [hscaled, hbi]

theorem matchingD_positive {D₀ B r i : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hBmin : 1 ≤ B)
    (hBmax : (B : ℝ) ≤ matchingMu r ξ * (D₀ : ℝ))
    (hi : i ≤ matchingT r ξ) :
    0 < matchingD D₀ r ξ i := by
  have h := matchingD_codegree_invariant hr hξ hξ1 hBmin hBmax hi
  by_contra hnot
  have hz : matchingD D₀ r ξ i = 0 := by omega
  simp [hz] at h
  have hBminR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hBmin
  linarith
theorem matchingD_large {D₀ B r i : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hBmin : 1 ≤ B)
    (hBmax : (B : ℝ) ≤ matchingMu r ξ * (D₀ : ℝ))
    (hi : i ≤ matchingT r ξ) :
    4 ≤ matchingA r ξ * (matchingD D₀ r ξ i : ℝ) := by
  have hinv := matchingD_codegree_invariant hr hξ hξ1 hBmin hBmax hi
  have hBminR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hBmin
  have hb := matchingB_le_a_quarter hr hξ hξ1
  have hD0 : 0 ≤ (matchingD D₀ r ξ i : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_right
    (show 4 * matchingB r ξ ≤ matchingA r ξ by linarith) hD0
  nlinarith [hinv, hmul]

theorem matchingD_codegree_ratio {D₀ B r i : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hBmin : 1 ≤ B)
    (hBmax : (B : ℝ) ≤ matchingMu r ξ * (D₀ : ℝ))
    (hi : i ≤ matchingT r ξ) :
    (B : ℝ) / (matchingD D₀ r ξ i : ℝ) ≤ matchingB r ξ := by
  have hinv := matchingD_codegree_invariant hr hξ hξ1 hBmin hBmax hi
  have hDpos : 0 < (matchingD D₀ r ξ i : ℝ) := by
    exact_mod_cast matchingD_positive hr hξ hξ1 hBmin hBmax hi
  exact (div_le_iff₀ hDpos).2 hinv

theorem matching_small {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
      (matchingA r ξ * matchingB r ξ) ≤ 1 := by
  have hNat : 2 * r - 1 ≤ 2 * r := by omega
  have hcast : (((2 * r - 1 : ℕ) : ℝ)) ≤ 2 * (r : ℝ) := by
    exact_mod_cast hNat
  have hsquare :
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) ≤ (2 * (r : ℝ)) ^ 2 := by
    gcongr
  have ha0 := (matchingA_pos hr hξ hξ1).le
  have hb0 := (matchingB_pos hr hξ).le
  have hb := matchingB_le_a_quarter hr hξ hξ1
  have har := matchingA_mul_r_le hr hξ hξ1
  have hfirst := mul_le_mul_of_nonneg_right hsquare
    (mul_nonneg ha0 hb0)
  have hsecond := mul_le_mul_of_nonneg_left hb
    (mul_nonneg (sq_nonneg (2 * (r : ℝ))) ha0)
  have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
  have hsq := pow_le_pow_left₀ (mul_nonneg ha0 hr0) har 2
  calc
    (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
        (matchingA r ξ * matchingB r ξ) ≤
      (2 * (r : ℝ)) ^ 2 * (matchingA r ξ * matchingB r ξ) := hfirst
    _ = ((2 * (r : ℝ)) ^ 2 * matchingA r ξ) * matchingB r ξ := by ring
    _ ≤ ((2 * (r : ℝ)) ^ 2 * matchingA r ξ) *
          (matchingA r ξ / 4) := hsecond
    _ = (matchingA r ξ * (r : ℝ)) ^ 2 := by ring
    _ ≤ (1 / 100 : ℝ) ^ 2 := hsq
    _ ≤ 1 := by norm_num
noncomputable def matchingDelta (r : ℕ) (ξ : ℝ) : ℝ :=
  8 * (r : ℝ) ^ 2 * Real.sqrt (matchingB r ξ)

theorem matchingDelta_nonneg (r : ℕ) (ξ : ℝ) :
    0 ≤ matchingDelta r ξ := by
  unfold matchingDelta
  positivity

theorem matchingDelta_le_quintic {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingDelta r ξ ≤
      ξ ^ 5 / (12500000 * (r : ℝ)) := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hsqrt := matchingB_sqrt_le hr hξ hξ1
  have hmul := mul_le_mul_of_nonneg_left hsqrt
    (by positivity : 0 ≤ 8 * (r : ℝ) ^ 2)
  have heq :
      8 * (r : ℝ) ^ 2 *
        (ξ ^ 5 / (100000000 * (r : ℝ) ^ 3)) =
      ξ ^ 5 / (12500000 * (r : ℝ)) := by field_simp; ring
  unfold matchingDelta
  rw [heq] at hmul
  exact hmul
theorem matching_round_error_budget {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingDelta r ξ * matchingA r ξ *
        (matchingT r ξ : ℝ) ^ 2 ≤ ξ / 100 := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hδ := matchingDelta_le_quintic hr hξ hξ1
  have ha0 := (matchingA_pos hr hξ hξ1).le
  have hT0 : 0 ≤ (matchingT r ξ : ℝ) := Nat.cast_nonneg _
  have hAT : matchingA r ξ * (matchingT r ξ : ℝ) ≤ 8 / ξ := by
    calc
      matchingA r ξ * (matchingT r ξ : ℝ) ≤ 2 * matchingL ξ :=
        (matchingA_mul_T_bounds hr hξ hξ1).2
      _ ≤ 2 * (4 / ξ) := by gcongr; exact matchingL_le_four_div hξ
      _ = 8 / ξ := by ring
  have hT : (matchingT r ξ : ℝ) ≤
      3200 * (r : ℝ) / ξ ^ 3 := by
    exact (le_div_iff₀ (pow_pos hξ 3)).2 (matchingT_cubic_bound hr hξ hξ1)
  calc
    matchingDelta r ξ * matchingA r ξ *
        (matchingT r ξ : ℝ) ^ 2 =
      matchingDelta r ξ *
        (matchingA r ξ * (matchingT r ξ : ℝ)) *
        (matchingT r ξ : ℝ) := by ring
    _ ≤ (ξ ^ 5 / (12500000 * (r : ℝ))) *
        (matchingA r ξ * (matchingT r ξ : ℝ)) *
        (matchingT r ξ : ℝ) := by
          gcongr
    _ ≤ (ξ ^ 5 / (12500000 * (r : ℝ))) *
        (8 / ξ) * (matchingT r ξ : ℝ) := by
          gcongr
    _ ≤ (ξ ^ 5 / (12500000 * (r : ℝ))) *
        (8 / ξ) * (3200 * (r : ℝ) / ξ ^ 3) := by
          gcongr
    _ ≤ ξ / 100 := by
      field_simp
      nlinarith [hξ.le]
theorem matching_quadratic_rate_budget {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    (r : ℝ) * matchingA r ξ ^ 2 * (matchingT r ξ : ℝ) ≤
      ξ / 50 := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hLpos : 0 < matchingL ξ :=
    lt_of_lt_of_le zero_lt_one (matchingL_ge_one hξ hξ1)
  have ha0 := (matchingA_pos hr hξ hξ1).le
  have hmul := mul_le_mul_of_nonneg_left
    (matchingA_mul_T_bounds hr hξ hξ1).2
    (mul_nonneg hrpos.le ha0)
  have hcancel :
      (r : ℝ) * matchingA r ξ * matchingL ξ = ξ / 100 := by
    unfold matchingA
    field_simp
  nlinarith [hmul]

theorem matching_initial_mu_budget {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    2 * matchingL ξ * matchingMu r ξ ≤ ξ / 4 := by
  have hmu0 : 0 ≤ matchingMu r ξ := by unfold matchingMu; positivity
  have hL0 : 0 ≤ matchingL ξ :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (matchingL_ge_one hξ hξ1)
  calc
    2 * matchingL ξ * matchingMu r ξ ≤
        2 * (4 / ξ) * matchingMu r ξ := by
          gcongr
          exact matchingL_le_four_div hξ
    _ ≤ 2 * (4 / ξ) * (ξ ^ 2 / 800) := by
      gcongr
      exact matchingMu_le_quadratic hr hξ hξ1
    _ = ξ / 100 := by field_simp; ring
    _ ≤ ξ / 4 := by nlinarith
theorem matching_total_error_budget {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingDelta r ξ * matchingA r ξ *
        (matchingT r ξ : ℝ) ^ 2 +
      ((r : ℝ) * matchingA r ξ ^ 2) *
        (matchingT r ξ : ℝ) ≤ ξ / 2 := by
  have hround := matching_round_error_budget hr hξ hξ1
  have hrate := matching_quadratic_rate_budget hr hξ hξ1
  linarith [hξ]
end HadwigerLean.Theorem2