import HadwigerLean.Bootstrap.Packing
import HadwigerLean.Bootstrap.SeparationFromPath
import HadwigerLean.Deduction.BootstrapParameters
import HadwigerLean.Deduction.PowerThree
import HadwigerLean.Deduction.ExternalInputs
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Assemble packing, chromatic separation, and paper Corollary 24. -/

namespace HadwigerLean.Bootstrap

open HadwigerLean.Deduction

universe u

/-- Every integer outer scale is at most its initial scale. -/
theorem outerScale_le {T a : ℕ} (h : IsOuterScale T a) : a ≤ T := by
  obtain ⟨i, hi⟩ := h
  have hpow : 2 ^ i ≤ 3 ^ i := Nat.pow_le_pow_left (by omega) i
  have hp : 0 < 3 ^ i := by positivity
  by_contra hnot
  have hlt : T < a := Nat.lt_of_not_ge hnot
  have hmul : 3 ^ i * T < 3 ^ i * a :=
    Nat.mul_lt_mul_of_pos_left hlt hp
  have hmul' : 2 ^ i * T ≤ 3 ^ i * T :=
    Nat.mul_le_mul_right T hpow
  omega

/-- One exponent-bootstrap step, conditional on the path-localization lemma.
The only external mathematical input is the explicit Corollary 24 hypothesis. -/
theorem local_linear_bound_step_of_path
    (h24 : Corollary24Statement.{u})
    (hpath : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) (k q : ℕ), PathLocalizationStatement H k q)
    (α : ℝ) (hα : 0 < α) (hold : LocalLinearBound.{u} α) :
    LocalLinearBound.{u} (4 * α / 3) := by
  classical
  obtain ⟨D, t₀, hD, ht₀, hlocal⟩ := hold
  obtain ⟨N, hN, hparams⟩ := eventual_bootstrap_parameters hα t₀
  let D' : ℕ := 2 * D + 3 * (10 ^ 6 * (D + 1) + 62000)
  let N' : ℕ := max 100 (max N t₀)
  refine ⟨D', N', by dsimp [D']; omega, by dsimp [N']; omega, ?_⟩
  intro V _ G t ht hminor horder
  have ht100 : 100 ≤ t := (Nat.le_max_left _ _).trans ht
  have htN : N ≤ t := (Nat.le_max_left _ _).trans
    ((Nat.le_max_right 100 (max N t₀)).trans ht)
  have htt₀ : t₀ ≤ t := (Nat.le_max_right N t₀).trans
    ((Nat.le_max_right 100 (max N t₀)).trans ht)
  have ht3 : 3 ≤ t := by omega
  have hlog : 0 < Real.log (t : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < t))
  let x : ℝ := Real.log (t : ℝ)
  let k : ℕ := ⌈x ^ (α / 3)⌉₊
  let T : ℕ := 3 ^ Nat.clog 3 t
  have hTspec : IsLeastPowerOfThreeAtLeast t T :=
    least_power_of_three_spec t
  have htT : t ≤ T := hTspec.2.1
  have hk3 : 3 ≤ k := by
    have hTreal : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
    have hlogT : 0 < Real.log (T : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < T))
    have hcut : (T : ℝ) / Real.sqrt (Real.log (T : ℝ)) < (T : ℝ) := by
      have hsqrt : 0 < Real.sqrt (Real.log (T : ℝ)) := Real.sqrt_pos.2 hlogT
      have hlogT1 : 1 < Real.log (T : ℝ) := by
        have : 100 ≤ T := by omega
        have h100 : (1 : ℝ) < Real.log 100 :=
          (Real.lt_log_iff_exp_lt (by norm_num)).2
            (lt_trans Real.exp_one_lt_three (by norm_num))
        exact h100.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast this))
      have hsqrt1 : 1 < Real.sqrt (Real.log (T : ℝ)) := by
        have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hlogT1
        simpa using this
      exact (div_lt_iff₀ hsqrt).2 (by nlinarith)
    have hp := hparams t T T htN htT hcut le_rfl
    exact hp.1
  obtain ⟨P, W, R, Q, hWR, hcover, hQminor, hPcard, hNoR, hWcolor⟩ :=
    exists_packing G k (by omega)
  have hQnot : ¬ HadwigerLean.HasCliqueMinor Q t := by
    intro h
    exact hminor (HadwigerLean.hasCliqueMinor_of_minor hQminor h)
  have hkpos : 0 < k := by omega
  have hPmul : Fintype.card P * k ≤ Fintype.card V :=
    (Nat.le_div_iff_mul_le hkpos).mp hPcard
  have hPmulR : (Fintype.card P : ℝ) * (k : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast hPmul
  have hxpow : 0 < x ^ (α / 3) := Real.rpow_pos_of_pos hlog _
  have hkceil : x ^ (α / 3) ≤ (k : ℝ) := Nat.le_ceil _
  have hQorder : (Fintype.card P : ℝ) ≤ (t : ℝ) * x ^ α := by
    apply le_of_mul_le_mul_right ?_ hxpow
    calc
      (Fintype.card P : ℝ) * x ^ (α / 3) ≤
          (Fintype.card P : ℝ) * (k : ℝ) :=
        mul_le_mul_of_nonneg_left hkceil (by positivity)
      _ ≤ (Fintype.card V : ℝ) := hPmulR
      _ ≤ (t : ℝ) * x ^ (4 * α / 3) := horder
      _ = ((t : ℝ) * x ^ α) * x ^ (α / 3) := by
        rw [bootstrap_order_power α x hlog]
        ring
  have hQcolor : HadwigerLean.chromatic Q ≤ D * t :=
    hlocal P Q t htt₀ hQnot hQorder
  have hRminor : ¬ HadwigerLean.HasCliqueMinor (G.induce R) t := by
    intro h
    let e : G.induce R ↪g G := SimpleGraph.Embedding.induce R
    exact hminor (HadwigerLean.hasCliqueMinor_map e.toHom e.injective h)
  have houter : OuterSeparation (G.induce R) T D := by
    intro a hscale hcut Y
    letI : Fintype Y := Fintype.ofFinite Y
    intro hYminor hYchi
    have haT : a ≤ T := outerScale_le hscale
    have hp := hparams t T a htN htT hcut haT
    change 3 ≤ k ∧ (k : ℝ) ≤ 2 * x ^ (α / 3) ∧
      t₀ ≤ 14 * a ∧
      2 * (k : ℝ) ^ 2 ≤ (Real.log ((14 * a : ℕ) : ℝ)) ^ α at hp
    obtain ⟨hk, _, hu₀, hsmall⟩ := hp
    let u : ℕ := 14 * a
    have hu : 0 < u := by dsimp [u]; omega
    have hlocal_u : ∀ (U : Type u) [Fintype U] (H : SimpleGraph U),
        ¬ HadwigerLean.HasCliqueMinor H u →
        Fintype.card U ≤ 2 * u * k ^ 2 →
        HadwigerLean.chromatic H ≤ D * u := by
      intro U _ H hminorU hcardU
      have hcardR : (Fintype.card U : ℝ) ≤
          (u : ℝ) * (2 * (k : ℝ) ^ 2) := by
        have hcast : (Fintype.card U : ℝ) ≤
            (2 * u * k ^ 2 : ℝ) := by exact_mod_cast hcardU
        convert hcast using 1 <;> push_cast <;> ring
      have hcard' : (Fintype.card U : ℝ) ≤
          (u : ℝ) * (Real.log (u : ℝ)) ^ α := by
        calc
          (Fintype.card U : ℝ) ≤ (u : ℝ) * (2 * (k : ℝ) ^ 2) := hcardR
          _ ≤ (u : ℝ) * (Real.log (u : ℝ)) ^ α := by
            exact mul_le_mul_of_nonneg_left hsmall (by positivity)
      exact hlocal U H u hu₀ hminorU hcard'
    have hNoY : NoLargeConnectedBipartite ((G.induce R).induce Y) k :=
      noLargeConnectedBipartite_induce (G.induce R) Y k hNoR
    have hYchi' : D * u < HadwigerLean.chromatic ((G.induce R).induce Y) := by
      have hcoef : 14 * (D * a) ≤ 28 * (D * a) :=
        Nat.mul_le_mul_right (D * a) (by decide : 14 ≤ 28)
      dsimp [u]
      calc
        D * (14 * a) = 14 * (D * a) := by ring
        _ ≤ 28 * (D * a) := hcoef
        _ = 28 * D * a := by ring
        _ < HadwigerLean.chromatic ((G.induce R).induce Y) := hYchi
    have hsep := chromatic_separable_of_path_localization
      ((G.induce R).induce Y) u D k hu (by omega) hlocal_u
      hYminor hNoY hYchi'
      (hpath Y ((G.induce R).induce Y) k
        (HadwigerLean.chromatic ((G.induce R).induce Y) - D * u))
    simpa [u, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hsep
  have hRcolor := h24 R (G.induce R) t T D ht100 hTspec hD hRminor houter
  have hWcolor' : HadwigerLean.chromatic (G.induce W) ≤ (2 * D) * t := by
    calc
      HadwigerLean.chromatic (G.induce W) ≤ 2 * HadwigerLean.chromatic Q := hWcolor
      _ ≤ 2 * (D * t) := Nat.mul_le_mul_left 2 hQcolor
      _ = (2 * D) * t := by ring
  have hpal := chromatic_le_add_induce G W R hcover
  calc
    HadwigerLean.chromatic G ≤
        HadwigerLean.chromatic (G.induce W) +
          HadwigerLean.chromatic (G.induce R) := hpal
    _ ≤ (2 * D) * t +
        (3 * (10 ^ 6 * (D + 1) + 62000)) * t :=
      Nat.add_le_add hWcolor' hRcolor.le
    _ = D' * t := by dsimp [D']; ring

end HadwigerLean.Bootstrap
