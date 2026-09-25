import HadwigerLean.Inseparability.StageRawInduction
import HadwigerLean.Inseparability.StageIteration

/-!
# Chromatic separability from explicit CI stage budgets

All graph-theoretic steps are checked here. The remaining inputs are
numerical inequalities for the scale and a uniform woven theorem on
each small connected piece.
-/

namespace HadwigerLean.Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem chromatic_separable_of_SC_stage_budgets
    (G : SimpleGraph V) (t r x k m q ℓ N : ℕ)
    (b : ℕ → ℕ)
    (ht : 3 ≤ t) (hx : 0 < x) (hk : 0 < k)
    (hminor : ¬ HasCliqueMinor G t)
    (horder : t ≤ r * x)
    (hzero : b 0 = 0)
    (hbound : ∀ u, u ≤ r → b u ≤ b r)
    (hsize : (480 * 6400 : ℝ)^2 * (t : ℝ) *
      (Real.log (t : ℝ))^3 ≤ (N : ℝ))
    (htℓ : t ≤ ℓ)
    (hlocal : ∀ Y : Finset V, Y.card ≤ 3 * b r →
      chromatic (G.induce (Y : Set V)) ≤ q)
    (hLocalWindow : r * N ≤ 3 * b r)
    (hconnect : r * x + ℓ ≤ k)
    (hχPacking : q + 2 * (480 * 6400 * ℓ) +
      m / 2 + r * x < chromatic G)
    (hχRaw : m / 2 + r * x + q + 4 * (3 * r * x) + 7 * k ≤
      chromatic G)
    (hreserveRaw : m / 2 + r * x + q +
      4 * (3 * r * x) + 6 * k ≤ m)
    (hSourceFan : 3 * (3 * r * x) ≤ k)
    (hSourceFinish : 2 * (3 * r * x) ≤ ℓ)
    (hMixedBudget : 3 * r * x + 2 * (r * x) ≤ k)
    (hMiddleSize : 2 * (r * x) ≤ k)
    (hFinishSize : 2 * (r * x) ≤ ℓ)
    (hChildRoots : 2 * x ≤ ℓ)
    (hWovenFromConn : ∀ u, u < r → ∀ Y : Finset V,
      VertexConnected (G.induce (Y : Set V)) ℓ →
      Woven (G.induce (Y : Set V)) (2 * x) ((4 * u + 1) * x))
    (hFirstUniform : Woven.uniformCliqueK x 0 ≤ ℓ)
    (hKnitting : 33 * ((4 * r + 1) * x) ≤ ℓ)
    (hFirstCore : N + x ≤ b 1)
    (hCoreStep : ∀ u, u < r →
      b u + u * N + N + (u + 1) * x ≤ b (u + 1))
    (hbaseBudget : 12 * k ≤ m)
    (hχIter : q + 2 * (r * x) + 7 * k ≤ chromatic G)
    (hreserveIter : q + 2 * (r * x) + 6 * k ≤ m / 2)
    (hbudgetIter : m / 2 + k ≤ m) :
    Bootstrap.ChromaticSeparable G m := by
  classical
  have hraw := raw_stage_extension_of_SC G t r x k m q ℓ N b
    ht hx hk hminor hsize htℓ hlocal hLocalWindow hconnect
    hχPacking hχRaw hreserveRaw hSourceFan hSourceFinish
    hMixedBudget hMiddleSize hFinishSize hChildRoots
    hWovenFromConn hFirstUniform hKnitting hFirstCore hCoreStep
  exact chromatic_separable_of_raw_stage_extension G t r x k m q b
    hminor horder hzero hbound hlocal hk hbaseBudget
    hχIter hreserveIter hbudgetIter
    (by intro _ u hu S _ hrootregion; exact hraw u hu S hrootregion)

end HadwigerLean.Inseparability
