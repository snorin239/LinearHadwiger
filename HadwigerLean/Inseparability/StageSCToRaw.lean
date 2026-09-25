import HadwigerLean.Inseparability.StagePackedToRaw
import HadwigerLean.Inseparability.StageSmallPieces

/-!
# The nonzero raw CI stage from the small connected subgraph theorem

SC packs the `p+1` connected pieces after deleting old tangencies.
The packed-pieces theorem performs the double fan, H3, mixed linkage,
child rerouting, knitting, and rooted-model assembly.
-/

namespace HadwigerLean.Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

theorem StageState.raw_stage_of_SC
    (S : StageState G (p * x) k prevLoss oldBound)
    (hp : 0 < p) (hx : 0 < x) (hk : 0 < k)
    (hrootregion : ∀ i, S.root i ∈ S.region)
    (t ℓ N q m coreBound : ℕ)
    (ht : 3 ≤ t) (htℓ : t ≤ ℓ)
    (hminor : ¬ HasCliqueMinor G t)
    (hsize : (480 * 6400 : ℝ)^2 * (t : ℝ) *
      (Real.log (t : ℝ))^3 ≤ (N : ℝ))
    (hlocal : ∀ Y : Finset V, Y.card ≤ (p + 1) * N →
      chromatic (G.induce (Y : Set V)) ≤ q)
    (hconnect : p * x + ℓ ≤ k)
    (hχPacking : q + 2 * (480 * 6400 * ℓ) +
      prevLoss + p * x < chromatic G)
    (hχ : prevLoss + p * x + q + 4 * (3 * p * x) + 7 * k ≤
      chromatic G)
    (hreserve : prevLoss + p * x + q + 4 * (3 * p * x) + 6 * k ≤ m)
    (hSourceFan : 3 * (3 * p * x) ≤ k)
    (hSourceFinish : 2 * (3 * p * x) ≤ ℓ)
    (hMixedBudget : 3 * p * x + 2 * ((p + 1) * x) ≤ k)
    (hMiddleSize : 2 * ((p + 1) * x) ≤ k)
    (hFinishSize : 2 * ((p + 1) * x) ≤ ℓ)
    (hChildRoots : 2 * x ≤ ℓ)
    (hWovenFromConn : ∀ Y : Finset V,
      VertexConnected (G.induce (Y : Set V)) ℓ →
      Woven (G.induce (Y : Set V)) (2 * x) ((4 * p + 1) * x))
    (hKnitting : 33 * ((4 * p + 1) * x) ≤ ℓ)
    (hCoreBudget : oldBound + p * N + N + (p + 1) * x ≤ coreBound) :
    Nonempty (StageState G ((p + 1) * x) k m coreBound) := by
  classical
  obtain ⟨K,_,hK,hKpair⟩ :=
    S.exists_small_pieces_after_tangent_deletion hrootregion
      t ℓ (p + 1) N q ht htℓ hminor hsize
      hlocal hconnect hχPacking
  exact S.raw_stage_of_packed_pieces hp hx hk hrootregion K
    (fun i => ⟨(hK i).1,(hK i).2.1,(hK i).2.2.1⟩)
    hKpair q m coreBound hlocal hχ hreserve hSourceFan
    hSourceFinish hMixedBudget hMiddleSize hFinishSize
    hChildRoots
    (fun i => hWovenFromConn (K i.castSucc) (hK i.castSucc).2.2.1)
    hKnitting hCoreBudget

end HadwigerLean.Inseparability

