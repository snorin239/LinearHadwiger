import HadwigerLean.Inseparability.SharpWovenBudget
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Elementary ceiling estimates for the sequential CI parameters. -/

namespace HadwigerLean.Inseparability

noncomputable def stageCount (t : ℕ) : ℕ :=
  Nat.ceil (Real.sqrt (Real.log (t : ℝ)))

noncomputable def stageBlockSize (t : ℕ) : ℕ :=
  Nat.ceil ((t : ℝ) / Real.sqrt (Real.log (t : ℝ)))

private theorem one_le_log (t : ℕ) (ht : 3 ≤ t) :
    (1 : ℝ) ≤ Real.log (t : ℝ) := by
  have h3 : Real.log (3 : ℝ) ≤ Real.log (t : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast ht)
  linarith [Real.log_three_gt_d9]

private theorem sqrt_log_bounds (t : ℕ) (ht : 3 ≤ t) :
    1 ≤ Real.sqrt (Real.log (t : ℝ)) ∧
      2 * Real.sqrt (Real.log (t : ℝ)) ≤ (t : ℝ) := by
  let s := Real.sqrt (Real.log (t : ℝ))
  have hL : 1 ≤ Real.log (t : ℝ) := one_le_log t ht
  have hL0 : 0 ≤ Real.log (t : ℝ) := by linarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = Real.log (t : ℝ) := Real.sq_sqrt hL0
  have htR : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have hlog : Real.log (t : ℝ) ≤ (t : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hsq : 0 ≤ ((t : ℝ) - 2)^2 := sq_nonneg _
  constructor
  · nlinarith
  · nlinarith

private theorem stageBlockSize_mul_sqrt_le
    (t : ℕ) (ht : 3 ≤ t) :
    (stageBlockSize t : ℝ) *
      Real.sqrt (Real.log (t : ℝ)) ≤
        (3 / 2 : ℝ) * t := by
  let s := Real.sqrt (Real.log (t : ℝ))
  let x := stageBlockSize t
  have hs1 := (sqrt_log_bounds t ht).1
  have hs2 := (sqrt_log_bounds t ht).2
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hspos : 0 < s := by dsimp [s] at hs1 ⊢; linarith
  have htR : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hdiv0 : 0 ≤ (t : ℝ) / s := le_of_lt (div_pos htR hspos)
  have hceil : (x : ℝ) < (t : ℝ) / s + 1 := by
    simpa [x, stageBlockSize, s] using Nat.ceil_lt_add_one hdiv0
  have hprod : (x : ℝ) * s ≤ ((t : ℝ) / s + 1) * s :=
    mul_le_mul_of_nonneg_right hceil.le hs0
  have hcancel : ((t : ℝ) / s) * s = t := div_mul_cancel₀ _ hspos.ne'
  dsimp [x, s] at hprod ⊢
  nlinarith

theorem stageBlockSize_le (t : ℕ) (ht : 3 ≤ t) :
    stageBlockSize t ≤ t := by
  let s := Real.sqrt (Real.log (t : ℝ))
  have hs1 := (sqrt_log_bounds t ht).1
  have hspos : 0 < s := by dsimp [s] at hs1 ⊢; linarith
  have htR : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  apply Nat.ceil_le.mpr
  change (t : ℝ) / s ≤ t
  apply (div_le_iff₀ hspos).2
  nlinarith

theorem stageCount_sub_one_mul_block_le
    (t : ℕ) (ht : 3 ≤ t) :
    (stageCount t - 1) * stageBlockSize t ≤ 2 * t := by
  let s := Real.sqrt (Real.log (t : ℝ))
  let r := stageCount t
  let x := stageBlockSize t
  have hs1 := (sqrt_log_bounds t ht).1
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hrceil : (r : ℝ) < s + 1 := by
    simpa [r, stageCount, s] using Nat.ceil_lt_add_one hs0
  have hrle : s ≤ (r : ℝ) := by
    simpa [r, stageCount, s] using Nat.le_ceil s
  have hr1 : 1 ≤ r := by
    have hreal : (1 : ℝ) ≤ r := by linarith
    exact_mod_cast hreal
  have hrsub : ((r - 1 : ℕ) : ℝ) ≤ s := by
    have hsub : r - 1 + 1 = r := Nat.sub_add_cancel hr1
    have hsubR := congrArg (fun n : ℕ => (n : ℝ)) hsub
    push_cast at hsubR
    linarith
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  have hprod : ((r - 1 : ℕ) : ℝ) * x ≤ s * x :=
    mul_le_mul_of_nonneg_right hrsub hx0
  have hxs := stageBlockSize_mul_sqrt_le t ht
  have hreal : (((r - 1) * x : ℕ) : ℝ) ≤ 2 * (t : ℝ) := by
    push_cast
    dsimp [r, x, s] at hprod hxs
    nlinarith
  exact_mod_cast hreal

theorem stageIndex_mul_block_le
    (t p : ℕ) (ht : 3 ≤ t) (hp : p < stageCount t) :
    p * stageBlockSize t ≤ 2 * t := by
  have h1 : p ≤ stageCount t - 1 := by omega
  have h2 := Nat.mul_le_mul_right (stageBlockSize t) h1
  have h3 := stageCount_sub_one_mul_block_le t ht
  omega

private theorem log_two_le_two_thirds_log
    (t : ℕ) (ht : 3 ≤ t) :
    Real.log (2 : ℝ) ≤ (2 / 3 : ℝ) * Real.log (t : ℝ) := by
  have h3 : Real.log (3 : ℝ) ≤ Real.log (t : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast ht)
  nlinarith [Real.log_two_lt_d9, Real.log_three_gt_d9]

theorem stageBlockSize_root_log_bound
    (t : ℕ) (ht : 3 ≤ t) :
    (((2 * stageBlockSize t : ℕ) : ℝ) *
      Real.sqrt (Real.log (((2 * stageBlockSize t : ℕ) : ℝ)))) ≤
        4 * (t : ℝ) := by
  let x := stageBlockSize t
  let s := Real.sqrt (Real.log (t : ℝ))
  let z := Real.log (((2 * x : ℕ) : ℝ))
  have hxle : x ≤ t := stageBlockSize_le t ht
  have hs1 := (sqrt_log_bounds t ht).1
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs2 : s ^ 2 = Real.log (t : ℝ) :=
    Real.sq_sqrt (by have h := one_le_log t ht; linarith)
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  have htR : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hdiv : (0 : ℝ) < (t : ℝ) / s :=
    div_pos htR (by dsimp [s] at hs1 ⊢; linarith)
  have hxpos : (0 : ℝ) < x := by
    have hceil : (t : ℝ) / s ≤ x := by
      simpa [x, stageBlockSize, s] using
        (Nat.le_ceil ((t : ℝ) / s))
    linarith
  have hz0 : 0 ≤ z := by
    apply Real.log_nonneg
    have hxposNat : 1 ≤ x := by exact_mod_cast hxpos
    exact_mod_cast (by omega : 1 ≤ 2 * x)
  have hz2 : (Real.sqrt z)^2 = z := Real.sq_sqrt hz0
  have hlog2x : z ≤ (5 / 3 : ℝ) * Real.log (t : ℝ) := by
    have hxt : (((2 * x : ℕ) : ℝ)) ≤ 2 * (t : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left 2 hxle
    have hlog : z ≤ Real.log (2 * (t : ℝ)) := by
      apply Real.log_le_log
      · push_cast
        nlinarith
      · simpa [z] using hxt
    have hlogmul :
        Real.log (2 * (t : ℝ)) =
          Real.log 2 + Real.log (t : ℝ) :=
      Real.log_mul (by norm_num) (by positivity)
    have h2 := log_two_le_two_thirds_log t ht
    rw [hlogmul] at hlog
    linarith
  have hzroot : Real.sqrt z ≤ (4 / 3 : ℝ) * s := by
    have hzroot0 := Real.sqrt_nonneg z
    nlinarith
  have hxs := stageBlockSize_mul_sqrt_le t ht
  have hprod : (x : ℝ) * Real.sqrt z ≤
      (x : ℝ) * ((4 / 3 : ℝ) * s) :=
    mul_le_mul_of_nonneg_left hzroot hx0
  dsimp [x, z] at hprod ⊢
  push_cast at hprod ⊢
  nlinarith

theorem stageCount_pos (t : ℕ) (ht : 3 ≤ t) :
    0 < stageCount t := by
  have hs := (sqrt_log_bounds t ht).1
  have hceil : Real.sqrt (Real.log (t : ℝ)) ≤
      (stageCount t : ℝ) := by
    simpa [stageCount] using
      (Nat.le_ceil (Real.sqrt (Real.log (t : ℝ))))
  have hreal : (0 : ℝ) < stageCount t := by linarith
  exact_mod_cast hreal

theorem stageCount_mul_block_ge (t : ℕ) (ht : 3 ≤ t) :
    t ≤ stageCount t * stageBlockSize t := by
  let s := Real.sqrt (Real.log (t : ℝ))
  let r := stageCount t
  let x := stageBlockSize t
  have hs1 := (sqrt_log_bounds t ht).1
  have hspos : 0 < s := by dsimp [s] at hs1 ⊢; linarith
  have hs0 : 0 ≤ s := hspos.le
  have hr : s ≤ (r : ℝ) := by
    simpa [r, stageCount, s] using Nat.le_ceil s
  have hx : (t : ℝ) / s ≤ (x : ℝ) := by
    simpa [x, stageBlockSize, s] using
      (Nat.le_ceil ((t : ℝ) / s))
  have hfirst : (t : ℝ) ≤ (x : ℝ) * s := by
    have hmul := mul_le_mul_of_nonneg_right hx hs0
    rw [div_mul_cancel₀ _ hspos.ne'] at hmul
    exact hmul
  have hsecond : (x : ℝ) * s ≤ (x : ℝ) * (r : ℝ) :=
    mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg _)
  have hreal : (t : ℝ) ≤ ((r * x : ℕ) : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast hreal

theorem stageCount_le_two_sqrt_log
    (t : ℕ) (ht : 3 ≤ t) :
    (stageCount t : ℝ) ≤
      2 * Real.sqrt (Real.log (t : ℝ)) := by
  have hs := (sqrt_log_bounds t ht).1
  have hceil :
      (stageCount t : ℝ) <
        Real.sqrt (Real.log (t : ℝ)) + 1 := by
    simpa [stageCount] using
      (Nat.ceil_lt_add_one
        (Real.sqrt_nonneg (Real.log (t : ℝ))))
  linarith

theorem stageCount_mul_block_le_three
    (t : ℕ) (ht : 3 ≤ t) :
    stageCount t * stageBlockSize t ≤ 3 * t := by
  have hr : stageCount t - 1 + 1 = stageCount t :=
    Nat.sub_add_cancel (stageCount_pos t ht)
  calc
    stageCount t * stageBlockSize t =
        (stageCount t - 1 + 1) * stageBlockSize t := by rw [hr]
    _ = (stageCount t - 1) * stageBlockSize t +
        stageBlockSize t := by ring
    _ ≤ 2 * t + t :=
      Nat.add_le_add (stageCount_sub_one_mul_block_le t ht)
        (stageBlockSize_le t ht)
    _ = 3 * t := by omega

theorem stageCount_le_two_log
    (t : ℕ) (ht : 3 ≤ t) :
    (stageCount t : ℝ) ≤
      2 * Real.log (t : ℝ) := by
  have hL := one_le_log t ht
  have hs := (sqrt_log_bounds t ht).1
  have hs2 := Real.sq_sqrt
    (by linarith : 0 ≤ Real.log (t : ℝ))
  have hr := stageCount_le_two_sqrt_log t ht
  nlinarith

theorem stageBlockSize_pos (t : ℕ) (ht : 3 ≤ t) :
    0 < stageBlockSize t := by
  let s := Real.sqrt (Real.log (t : ℝ))
  have hs := (sqrt_log_bounds t ht).1
  have hspos : 0 < s := by dsimp [s] at hs ⊢; linarith
  have htpos : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hdiv : (0 : ℝ) < (t : ℝ) / s := div_pos htpos hspos
  have hceil : (t : ℝ) / s ≤ (stageBlockSize t : ℝ) := by
    simpa [stageBlockSize, s] using Nat.le_ceil ((t : ℝ) / s)
  have hreal : (0 : ℝ) < stageBlockSize t := lt_of_lt_of_le hdiv hceil
  exact_mod_cast hreal

end HadwigerLean.Inseparability
