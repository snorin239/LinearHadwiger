import HadwigerLean.Inseparability.StageTangentDeletion
import HadwigerLean.Inseparability.RegionExtractionNested
import Mathlib.Tactic

/-!
# Extract the middle connected region after packing and the double fan

The small pieces cost the local chromatic bound, and the fan costs its own
four-colors-per-source allowance. Additive chromatic connectivity then gives
the new connected region disjoint from both constructions.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {s k m coreBound : ℕ}

theorem StageState.exists_middle_region_after_pieces_and_fan
    (S : StageState G s k m coreBound)
    (hrootregion : ∀ i, S.root i ∈ S.region)
    (r N q fanCost middleK middleLoss : ℕ)
    (J : Fin r → Finset V)
    (hJsize : ∀ i, (J i).card ≤ N)
    (B : Finset V)
    (hBcost : chromatic (G.induce (B : Set V)) ≤ fanCost)
    (hlocal : ∀ U : Finset V, U.card ≤ r * N →
      chromatic (G.induce (U : Set V)) ≤ q)
    (hk : 0 < middleK)
    (hχ : m + s + q + fanCost + 7 * middleK ≤ chromatic G)
    (hbudget : m + s + q + fanCost + 6 * middleK ≤ middleLoss) :
    ∃ H₃ : Finset V,
      H₃ ⊆ (S.region \ S.tangentFinset) \
        (((Finset.univ : Finset (Fin r)).biUnion J) ∪ B) ∧
      VertexConnected (G.induce (H₃ : Set V)) middleK ∧
      chromatic G ≤ chromatic (G.induce (H₃ : Set V)) + middleLoss := by
  classical
  let P : Finset V := (Finset.univ : Finset (Fin r)).biUnion J
  have hPcard : P.card ≤ r * N := by
    have h := Finset.card_biUnion_le_card_mul
      (Finset.univ : Finset (Fin r)) J N (fun i _ => hJsize i)
    simpa [P] using h
  have hPcost : chromatic (G.induce (P : Set V)) ≤ q :=
    hlocal P hPcard
  let R : Finset V := S.region \ S.tangentFinset
  have hreserve : chromatic G ≤
      chromatic (G.induce (R : Set V)) + (m + s) := by
    have hDsub := S.tangentFinset_subset_region hrootregion
    have hχdel := chromatic_induce_le_sdiff_add_card
      G S.region S.tangentFinset hDsub
    have hDcard := S.tangentFinset_card
    have hχold := S.chromatic_reserve
    change chromatic (G.induce (S.region : Set V)) ≤
      chromatic (G.induce (R : Set V)) + S.tangentFinset.card at hχdel
    omega
  exact exists_connected_region_after_deleting_two
    G R P B middleK (m + s) q fanCost middleLoss
      hk hreserve hPcost hBcost (by omega) (by omega)

end Inseparability
end HadwigerLean
