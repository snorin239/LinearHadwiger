import HadwigerLean.Inseparability.StageSCToRaw
import HadwigerLean.Inseparability.StageFirstSCToRaw
import Mathlib.Tactic

/-!
# One uniform raw-stage extension for the CI induction

The first stage uses a rooted model in D. Later stages use the double
fan and the woven child models. This wrapper isolates the numerical
inequalities that must hold at every index below r.
-/

namespace HadwigerLean.Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem raw_stage_extension_of_SC
    (G : SimpleGraph V) (t r x k m q ℓ N : ℕ)
    (b : ℕ → ℕ)
    (ht : 3 ≤ t) (hx : 0 < x) (hk : 0 < k)
    (hminor : ¬ HasCliqueMinor G t)
    (hsize : (480 * 6400 : ℝ)^2 * (t : ℝ) *
      (Real.log (t : ℝ))^3 ≤ (N : ℝ))
    (htℓ : t ≤ ℓ)
    (hlocal : ∀ Y : Finset V, Y.card ≤ 3 * b r →
      chromatic (G.induce (Y : Set V)) ≤ q)
    (hLocalWindow : r * N ≤ 3 * b r)
    (hconnect : r * x + ℓ ≤ k)
    (hχPacking : q + 2 * (480 * 6400 * ℓ) +
      m / 2 + r * x < chromatic G)
    (hχ : m / 2 + r * x + q + 4 * (3 * r * x) + 7 * k ≤
      chromatic G)
    (hreserve : m / 2 + r * x + q +
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
      b u + u * N + N + (u + 1) * x ≤ b (u + 1)) :
    ∀ u, u < r →
      (S : StageState G (u * x) k (m / 2) (b u)) →
      (∀ i, S.root i ∈ S.region) →
      Nonempty (StageState G ((u + 1) * x) k m (b (u + 1))) := by
  classical
  intro u hu S hrootregion
  have hux : u * x ≤ r * x :=
    Nat.mul_le_mul_right x (Nat.le_of_lt hu)
  have hsuccx : (u + 1) * x ≤ r * x :=
    Nat.mul_le_mul_right x hu
  have hlocalStage : ∀ Y : Finset V,
      Y.card ≤ (u + 1) * N →
      chromatic (G.induce (Y : Set V)) ≤ q := by
    intro Y hY
    apply hlocal Y
    have hscale : (u + 1) * N ≤ r * N :=
      Nat.mul_le_mul_right N hu
    omega
  by_cases hu0 : u = 0
  · subst u
    have hconnect₀ : ℓ ≤ k := by omega
    have hχPacking₀ : q + 2 * (480 * 6400 * ℓ) +
        m / 2 < chromatic G := by omega
    have hχ₀ : m / 2 + q + 7 * k ≤ chromatic G := by omega
    have hreserve₀ : m / 2 + q + 6 * k ≤ m := by omega
    have hmiddle₀ : x ≤ k := by omega
    have hfinish₀ : x ≤ ℓ := by omega
    have S₀ : StageState G 0 k (m / 2) (b 0) := by
      simpa only [Nat.zero_mul] using S
    simpa using S₀.first_raw_stage_of_SC x t ℓ N q m (b 1)
      hx hk ht htℓ hminor hsize
      (by simpa using hlocalStage)
      hconnect₀ hχPacking₀ hχ₀ hreserve₀
      hmiddle₀ hfinish₀ hFirstUniform hFirstCore
  · have hup : 0 < u := Nat.pos_of_ne_zero hu0
    have hχPackingᵤ : q + 2 * (480 * 6400 * ℓ) +
        m / 2 + u * x < chromatic G := by omega
    have hχᵤ : m / 2 + u * x + q +
        4 * (3 * u * x) + 7 * k ≤ chromatic G := by
      have hfan : 3 * u * x ≤ 3 * r * x := by
        nlinarith [hux]
      omega
    have hreserveᵤ : m / 2 + u * x + q +
        4 * (3 * u * x) + 6 * k ≤ m := by
      have hfan : 3 * u * x ≤ 3 * r * x := by
        nlinarith [hux]
      omega
    have hsourceFanᵤ : 3 * (3 * u * x) ≤ k := by
      have hfan : 3 * u * x ≤ 3 * r * x := by
        nlinarith [hux]
      omega
    have hsourceFinishᵤ : 2 * (3 * u * x) ≤ ℓ := by
      have hfan : 3 * u * x ≤ 3 * r * x := by
        nlinarith [hux]
      omega
    have hmixedᵤ : 3 * u * x + 2 * ((u + 1) * x) ≤ k := by
      have hfan : 3 * u * x ≤ 3 * r * x := by
        nlinarith [hux]
      omega
    have hmiddleᵤ : 2 * ((u + 1) * x) ≤ k := by omega
    have hfinishᵤ : 2 * ((u + 1) * x) ≤ ℓ := by omega
    have hconnectᵤ : u * x + ℓ ≤ k := by omega
    have hknitᵤ : 33 * ((4 * u + 1) * x) ≤ ℓ := by
      have hstep : (4 * u + 1) * x ≤ (4 * r + 1) * x :=
        Nat.mul_le_mul_right x (by omega)
      omega
    exact S.raw_stage_of_SC hup hx hk hrootregion t ℓ N q m (b (u + 1))
      ht htℓ hminor hsize hlocalStage hconnectᵤ
      hχPackingᵤ hχᵤ hreserveᵤ hsourceFanᵤ
      hsourceFinishᵤ hmixedᵤ hmiddleᵤ hfinishᵤ
      hChildRoots (hWovenFromConn u hu) hknitᵤ (hCoreStep u hu)

end HadwigerLean.Inseparability


