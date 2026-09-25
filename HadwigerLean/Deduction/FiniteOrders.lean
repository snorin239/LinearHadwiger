import HadwigerLean.Graph.MinorFree
import HadwigerLean.Graph.Finite

/-! Extend a linear coloring bound from large clique orders to all orders. -/

namespace HadwigerLean.Deduction

universe u

/-- A bound for all `t ≥ T` extends to every `t ≥ 2` by enlarging its
coefficient. A `K_t`-minor-free graph is also `K_T`-minor-free when `t < T`.
This is the finite-order step of the paper without its density theorem. -/
theorem extend_linear_bound_from_large_orders
    (C T : ℕ) (hT : 2 ≤ T)
    (hlarge : ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (t : ℕ),
      T ≤ t → ¬ HadwigerLean.HasCliqueMinor G t →
      HadwigerLean.chromatic G ≤ C * t) :
    ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (t : ℕ),
      2 ≤ t → ¬ HadwigerLean.HasCliqueMinor G t →
      HadwigerLean.chromatic G ≤ (C * T) * t := by
  intro V _ G t ht hminor
  by_cases hTt : T ≤ t
  · have h := hlarge V G t hTt hminor
    have hcoef : (C * t) * 1 ≤ (C * t) * T :=
      Nat.mul_le_mul_left (C * t) (by omega : 1 ≤ T)
    have hbound : C * t ≤ (C * T) * t := by
      simpa only [mul_one, mul_assoc, mul_comm, mul_left_comm] using hcoef
    exact h.trans hbound
  · have htT : t ≤ T := by omega
    have hminorT : ¬ HadwigerLean.HasCliqueMinor G T := by
      intro hKT
      exact hminor (HadwigerLean.hasCliqueMinor_order_mono htT hKT)
    have h := hlarge V G T le_rfl hminorT
    have hcoef : (C * T) * 1 ≤ (C * T) * t :=
      Nat.mul_le_mul_left (C * T) (by omega : 1 ≤ t)
    have hbound : C * T ≤ (C * T) * t := by
      simpa only [mul_one] using hcoef
    exact h.trans hbound

end HadwigerLean.Deduction
