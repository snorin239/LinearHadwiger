import HadwigerLean.Inseparability.StageFirstPackedToRaw
import HadwigerLean.Inseparability.StageSmallPieces

/-!
# The first raw CI stage directly from SC packing
-/

namespace HadwigerLean.Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

theorem StageState.first_raw_stage_of_SC
    (S : StageState G 0 k prevLoss oldBound)
    (x t ℓ N q m coreBound : ℕ)
    (hx : 0 < x) (hk : 0 < k)
    (ht : 3 ≤ t) (htℓ : t ≤ ℓ)
    (hminor : ¬ HasCliqueMinor G t)
    (hsize : (480 * 6400 : ℝ)^2 * (t : ℝ) *
      (Real.log (t : ℝ))^3 ≤ (N : ℝ))
    (hlocal : ∀ Y : Finset V, Y.card ≤ N →
      chromatic (G.induce (Y : Set V)) ≤ q)
    (hconnect : ℓ ≤ k)
    (hχPacking : q + 2 * (480 * 6400 * ℓ) +
      prevLoss < chromatic G)
    (hχ : prevLoss + q + 7 * k ≤ chromatic G)
    (hreserve : prevLoss + q + 6 * k ≤ m)
    (hUsize : x ≤ k) (hDsize : x ≤ ℓ)
    (hUniform : Woven.uniformCliqueK x 0 ≤ ℓ)
    (hCoreBudget : N + x ≤ coreBound) :
    Nonempty (StageState G x k m coreBound) := by
  classical
  have hlocal' : ∀ Y : Finset V, Y.card ≤ 1 * N →
      chromatic (G.induce (Y : Set V)) ≤ q := by
    intro Y hY
    exact hlocal Y (by simpa using hY)
  obtain ⟨K,_,hK,_⟩ :=
    S.exists_small_pieces_after_tangent_deletion
      (by intro i; exact i.elim0)
      t ℓ 1 N q ht htℓ hminor hsize hlocal'
      (by simpa using hconnect) (by simpa using hχPacking)
  let D := K 0
  exact S.first_raw_stage_of_packed_piece x ℓ N q m coreBound
    hx hk D (hK 0).1 (hK 0).2.1 (hK 0).2.2.1
    hlocal hχ hreserve hUsize hDsize hUniform hCoreBudget

end HadwigerLean.Inseparability
