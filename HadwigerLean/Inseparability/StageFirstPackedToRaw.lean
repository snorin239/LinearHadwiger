import HadwigerLean.Inseparability.StageH3
import HadwigerLean.Inseparability.FirstStageState
import HadwigerLean.Woven.ConnectorClean
import HadwigerLean.Woven.Uniform
import Mathlib.Tactic

/-!
# The first raw CI stage from one connected piece

With no old branches the path family comes directly from Menger.
A rooted clique model in D supplies the first-stage clique edges.
-/

namespace HadwigerLean.Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

def StageState.widenCoreBound
    (S : StageState G s k m bound₁) (h : bound₁ ≤ bound₂) :
    StageState G s k m bound₂ :=
  { S with core_card_le := S.core_card_le.trans h }

theorem StageState.first_raw_stage_of_packed_piece
    (S : StageState G 0 k prevLoss oldBound)
    (x ℓ N q m coreBound : ℕ)
    (hx : 0 < x) (hk : 0 < k)
    (D : Finset V)
    (hDR : D ⊆ S.region \ S.tangentFinset)
    (hDcardBound : D.card ≤ N)
    (hDconn : VertexConnected (G.induce (D : Set V)) ℓ)
    (hlocal : ∀ Y : Finset V, Y.card ≤ N →
      chromatic (G.induce (Y : Set V)) ≤ q)
    (hχ : prevLoss + q + 7 * k ≤ chromatic G)
    (hreserve : prevLoss + q + 6 * k ≤ m)
    (hUsize : x ≤ k) (hDsize : x ≤ ℓ)
    (hUniform : Woven.uniformCliqueK x 0 ≤ ℓ)
    (hCoreBudget : N + x ≤ coreBound) :
    Nonempty (StageState G x k m coreBound) := by
  classical
  let K : Fin 1 → Finset V := fun _ => D
  have hKsize : ∀ i, (K i).card ≤ N := fun _ => hDcardBound
  have hlocal' : ∀ Y : Finset V, Y.card ≤ 1 * N →
      chromatic (G.induce (Y : Set V)) ≤ q := by
    intro Y hY
    exact hlocal Y (by simpa using hY)
  obtain ⟨U,hUraw,hUconn,hUreserve⟩ :=
    S.exists_middle_region_after_pieces_and_fan
      (by intro i; exact i.elim0)
      1 N q 0 k m K hKsize ∅ (by simpa using chromatic_le_card (G.induce ((∅ : Finset V) : Set V))) hlocal' hk
      (by omega) (by omega)
  have hUR : U ⊆ S.region := by
    intro v hv
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hUraw hv)).1).1
  have hDregion : D ⊆ S.region := by
    intro v hv
    exact (Finset.mem_sdiff.mp (hDR hv)).1
  have hDU : Disjoint D U := by
    apply Finset.disjoint_left.mpr
    intro v hvD hvU
    exact (Finset.mem_sdiff.mp (hUraw hvU)).2
      (Finset.mem_union_left _
        (Finset.mem_biUnion.mpr
          ⟨0,Finset.mem_univ _,hvD⟩))
  have hUcard : x ≤ U.card := by
    have horder := hUconn.order_gt
    have hcard : Fintype.card (U : Set V) = U.card := by
      apply Fintype.card_of_finset' U
      intro v
      rfl
    rw [hcard] at horder
    omega
  have hDcard : x ≤ D.card := by
    have horder := hDconn.order_gt
    have hcard : Fintype.card (D : Set V) = D.card := by
      apply Fintype.card_of_finset' D
      intro v
      rfl
    rw [hcard] at horder
    omega
  obtain ⟨P,L,hAB,_,hCleanU,hCleanD⟩ :=
    Woven.exists_clean_connectors_inside G S.region U D k x
      S.region_connected hUsize hUR hDregion hUcard hDcard
  have hWoven : Woven (G.induce (D : Set V)) x 0 :=
    Woven.woven_of_uniformCliqueK (G.induce (D : Set V))
      x 0 (by omega) (hDconn.of_le hUniform)
  obtain ⟨T⟩ := exists_first_stage_state D U hDU hWoven P L
    hAB.2 hAB.1 hCleanD hCleanU hUconn hUreserve
  exact ⟨T.widenCoreBound (by omega)⟩

end HadwigerLean.Inseparability


