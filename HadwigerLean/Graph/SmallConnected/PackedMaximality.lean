import HadwigerLean.Graph.SmallConnected.LocalMax
import HadwigerLean.Graph.SmallConnected.PackedMax
import HadwigerLean.Graph.SmallConnected.PackedRecover
import HadwigerLean.Graph.SmallConnected.PackedComposeGraph
import Mathlib.Tactic

/-!
# Maximal packing excludes further low-loss blocks
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A maximal admissible family has no additional uncovered connected
`h`-block whose quotient contraction loss is at most `p(h-1)`. -/
theorem no_lowLoss_block_of_maximal_family
    (G : SimpleGraph V) (h p : ℕ)
    (F : ConnectedBlockFamily G) [DecidableRel F.quotient.Adj]
    (hF : GoodPackedFamily G h p F)
    (hmax : ∀ F' : ConnectedBlockFamily G,
      GoodPackedFamily G h p F' → F'.blocks.card ≤ F.blocks.card)
    (H : Finset F.Vertex)
    (hdisj : Disjoint H F.blockVertices)
    (hconn : (F.quotient.induce (H : Set F.Vertex)).Connected)
    (hcard : H.card = h)
    (hloss : connectedSetContractionLoss F.quotient H ≤ p * (h - 1)) :
    False := by
  classical
  let H₀ := F.originalOfSingletons H
  have hdisj₀ : Disjoint H₀ F.covered :=
    F.originalOfSingletons_disjoint_covered H
  have hconn₀ : (G.induce (H₀ : Set V)).Connected :=
    F.originalOfSingletons_connected H hdisj hconn
  have hcard₀ : H₀.card = h := by
    rw [F.originalOfSingletons_card H hdisj, hcard]
  have hlift : F.singletonLift H₀ = H :=
    F.singletonLift_originalOfSingletons H hdisj
  let F' := F.add H₀ hconn₀ hdisj₀
  have hcount := F.add_edgeCount_add_loss H₀ hconn₀ hdisj₀
  rw [hlift] at hcount
  have hcount' : edgeCount F'.quotient + connectedSetContractionLoss F.quotient H = edgeCount F.quotient := hcount
  have hm : F'.blocks.card = F.blocks.card + 1 :=
    F.blocks_card_add H₀ hconn₀ hdisj₀
  have hgood' : GoodPackedFamily G h p F' := by
    unfold GoodPackedFamily
    constructor
    · intro B hB
      rcases Finset.mem_insert.mp hB with hBH | hBF
      · subst B
        exact hcard₀
      · exact hF.1 B hBF
    constructor
    · have hgood := hF.2.1
      rw [hm]
      have hmul : p * (F.blocks.card + 1) * (h - 1) =
          p * F.blocks.card * (h - 1) + p * (h - 1) := by ring
      rw [hmul]
      omega
    · have hQadd : edgeCount F'.quotient ≤ edgeCount F.quotient := by omega
      exact hQadd.trans hF.2.2
  have hbound := hmax F' hgood'
  rw [hm] at hbound
  omega


/-- Every admissible local set in the uncovered quotient is shorter than h. -/
theorem lowLossConnectedSet_card_lt_of_maximal_family
    (G : SimpleGraph V) (h p : ℕ)
    (F : ConnectedBlockFamily G) [DecidableRel F.quotient.Adj]
    (hF : GoodPackedFamily G h p F)
    (hmax : ∀ F' : ConnectedBlockFamily G,
      GoodPackedFamily G h p F' → F'.blocks.card ≤ F.blocks.card)
    (S H : Finset F.Vertex)
    (hSX : Disjoint S F.blockVertices)
    (hH : LowLossConnectedSet F.quotient S h p H) :
    H.card < h := by
  classical
  have hle := hH.2.2.1
  by_contra hnot
  have hcard : H.card = h := by omega
  have hdisj : Disjoint H F.blockVertices :=
    Finset.disjoint_of_subset_left hH.2.1 hSX
  exact no_lowLoss_block_of_maximal_family G h p F hF hmax H
    hdisj hH.2.2.2.1 hcard (by simpa [hcard] using hH.2.2.2.2)
end HadwigerLean