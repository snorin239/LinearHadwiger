import HadwigerLean.Deduction.Theorem4Local
import HadwigerLean.Deduction.Theorem4Numerics
import HadwigerLean.Woven.OuterContracts
import Mathlib.Tactic

/-! Chromatic inseparability supplies the Theorem 4 outer separation calls. -/

namespace HadwigerLean.Deduction

universe u

/-- The precise local-bound form of the chromatic inseparability theorem
needed by the Theorem 4 specialization. -/
def Theorem4CIInput (D : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] (Y : SimpleGraph W) (q s : ℕ),
    3 ≤ q → ¬ HasCliqueMinor Y q →
    (∀ U : Finset W,
      (U.card : ℝ) ≤
        (D : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ (4 : ℝ) →
      chromatic (Y.induce (U : Set W)) ≤ q * s) →
    2 * (D * q * (1 + s)) ≤ chromatic Y →
    Bootstrap.ChromaticSeparable Y (D * q * (1 + s))

theorem theorem4_sep_contract_of_ci
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (T D a s : ℕ)
    (ha : 0 < a) (haT : a ≤ T)
    (hcut : (T : ℝ) / Real.sqrt (Real.log (T : ℝ)) < (a : ℝ))
    (hf : theorem4ScaleMaxRatio G D T ≤ (s : ℝ))
    (hCI : Theorem4CIInput.{u} D) :
    Woven.OuterSepContract G a (theorem4Sigma D s a) := by
  classical
  intro j hj root P hminor X hχ
  let N := G.induce (Woven.normalizedSet root P)
  let Y := N.induce (X : Set (Woven.normalizedSet root P))
  have hminorY : ¬ HasCliqueMinor Y (14 * a) := by
    intro h
    let e : Y ↪g N := SimpleGraph.Embedding.induce _
    exact hminor (hasCliqueMinor_map e.toHom e.injective h)
  have hwindow : (T : ℝ) / Real.sqrt (Real.log (T : ℝ)) ≤
      ((14 * a : ℕ) : ℝ) := by
    have hstep : (a : ℝ) ≤ ((14 * a : ℕ) : ℝ) := by
      exact_mod_cast (by omega : a ≤ 14 * a)
    exact hcut.le.trans hstep
  have hqT : 14 * a ≤ 14 * T := Nat.mul_le_mul_left 14 haT
  have hmaxN : theorem4ScaleMaxRatio N D T ≤
      theorem4ScaleMaxRatio G D T :=
    theorem4ScaleMaxRatio_induce_le G (Woven.normalizedSet root P) D T
  have hmaxY : theorem4ScaleMaxRatio Y D T ≤
      theorem4ScaleMaxRatio N D T :=
    theorem4ScaleMaxRatio_induce_le N
      (X : Set (Woven.normalizedSet root P)) D T
  have hfY : theorem4ScaleMaxRatio Y D T ≤ (s : ℝ) :=
    (hmaxY.trans hmaxN).trans hf
  have hlocal' : ∀ U : Finset (X : Set (Woven.normalizedSet root P)),
      (U.card : ℝ) ≤
        (D : ℝ) * ((14 * a : ℕ) : ℝ) *
          (Real.log ((14 * a : ℕ) : ℝ)) ^ (4 : ℝ) →
      chromatic (Y.induce (U : Set _)) ≤ (14 * a) * s := by
    intro U horder
    exact theorem4_local_chromatic_bound Y D T (14 * a) s
      (by omega) hwindow hqT hminorY hfY U horder
  have hsig : theorem4Sigma D s a = D * (14 * a) * (1 + s) := by
    simp [theorem4Sigma]
    ring
  change 2 * theorem4Sigma D s a < chromatic Y at hχ
  rw [hsig] at hχ ⊢
  exact hCI _ Y (14 * a) s (by omega) hminorY hlocal' (by omega)

end HadwigerLean.Deduction
