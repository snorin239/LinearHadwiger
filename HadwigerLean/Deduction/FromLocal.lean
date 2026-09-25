import HadwigerLean.Deduction.ExternalInputs
import HadwigerLean.Deduction.FiniteOrders

/-! Apply the Delcourt--Postle reduction to a sufficiently strong local bound. -/

namespace HadwigerLean.Deduction

open HadwigerLean.Bootstrap

universe u

/-- Once the logarithmic window of Theorem 4 fits into a local linear bound,
Theorem 4 supplies a large-order linear bound. -/
theorem large_linear_of_local_and_window
    (h4 : Theorem4Statement.{u}) (α : ℝ)
    (hlocal : LocalLinearBound.{u} α)
    (hwindow : ∀ (C t₀ : ℕ), 1 ≤ C →
      ∃ T : ℕ, 3 ≤ T ∧
        ∀ (t a : ℕ), T ≤ t →
          (t : ℝ) / Real.sqrt (Real.log (t : ℝ)) ≤ (a : ℝ) →
          a ≤ t → t₀ ≤ a ∧
            (C : ℝ) * (Real.log (a : ℝ)) ^ (4 : ℝ) ≤
              (Real.log (a : ℝ)) ^ α) :
    ∃ C T : ℕ, 2 ≤ T ∧
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (t : ℕ),
        T ≤ t → ¬ HadwigerLean.HasCliqueMinor G t →
        HadwigerLean.chromatic G ≤ C * t := by
  classical
  obtain ⟨D, t₀, hD, ht₀, hlocal⟩ := hlocal
  obtain ⟨C, hC, hDP⟩ := theorem4_elimination h4
  obtain ⟨T, hT, hwindow⟩ := hwindow C t₀ hC
  refine ⟨C * (1 + D), T, by omega, ?_⟩
  intro V _ G t ht hminor
  have hbound := hDP V G t (D : ℝ) (by omega) hminor (by positivity)
    (by
      intro a H _ hlow hhigh hHminor horder
      obtain ⟨ha₀, hdom⟩ := hwindow t a ht hlow hhigh
      have horder' : (Fintype.card H.verts : ℝ) ≤
          (a : ℝ) * (Real.log (a : ℝ)) ^ α := by
        calc
          (Fintype.card H.verts : ℝ) ≤
              (C : ℝ) * (a : ℝ) * (Real.log (a : ℝ)) ^ (4 : ℝ) := horder
          _ = (a : ℝ) * ((C : ℝ) * (Real.log (a : ℝ)) ^ (4 : ℝ)) := by ring
          _ ≤ (a : ℝ) * (Real.log (a : ℝ)) ^ α :=
            mul_le_mul_of_nonneg_left hdom (by positivity)
      have hnat := hlocal H.verts H.coe a ha₀ hHminor horder'
      exact_mod_cast hnat)
  have hcast : (HadwigerLean.chromatic G : ℝ) ≤
      ((C * (1 + D) * t : ℕ) : ℝ) := by
    convert hbound using 1 <;> push_cast <;> ring
  exact_mod_cast hcast

/-- The same bound holds for every excluded complete-minor order at least two. -/
theorem linear_of_local_and_window
    (h4 : Theorem4Statement.{u}) (α : ℝ)
    (hlocal : LocalLinearBound.{u} α)
    (hwindow : ∀ (C t₀ : ℕ), 1 ≤ C →
      ∃ T : ℕ, 3 ≤ T ∧
        ∀ (t a : ℕ), T ≤ t →
          (t : ℝ) / Real.sqrt (Real.log (t : ℝ)) ≤ (a : ℝ) →
          a ≤ t → t₀ ≤ a ∧
            (C : ℝ) * (Real.log (a : ℝ)) ^ (4 : ℝ) ≤
              (Real.log (a : ℝ)) ^ α) :
    ∃ C : ℕ,
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (t : ℕ),
        2 ≤ t → ¬ HadwigerLean.HasCliqueMinor G t →
        HadwigerLean.chromatic G ≤ C * t := by
  obtain ⟨C, T, hT, hlarge⟩ :=
    large_linear_of_local_and_window h4 α hlocal hwindow
  exact ⟨C * T, extend_linear_bound_from_large_orders C T hT hlarge⟩

end HadwigerLean.Deduction
