import HadwigerLean.Inseparability.StageOldReindex
import HadwigerLean.Inseparability.StageChildRoots
import HadwigerLean.Inseparability.StageSourceCover
import HadwigerLean.Inseparability.StageSourcePlacement
import HadwigerLean.Inseparability.StageH3
import HadwigerLean.Woven.DoubleFanInside
import Mathlib.Tactic

/-!
# From packed connected pieces to the next raw CI stage

The old stage and a family of `p+1` small connected pieces determine
the child roots and doubled fan. The chromatic extraction supplies H3;
the geometric assembly then gives the next raw stage.
-/

namespace HadwigerLean.Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

theorem StageState.raw_stage_of_packed_pieces
    (S : StageState G (p * x) k prevLoss oldBound)
    (hp : 0 < p) (hx : 0 < x) (hk : 0 < k)
    (hrootregion : ∀ i, S.root i ∈ S.region)
    (K : Fin (p + 1) → Finset V)
    (hK : ∀ i,
      K i ⊆ S.region \ S.tangentFinset ∧
      (K i).card ≤ N ∧
      VertexConnected (G.induce (K i : Set V)) ℓ)
    (hKpair : Pairwise fun i j => Disjoint (K i) (K j))
    (q m coreBound : ℕ)
    (hlocal : ∀ Y : Finset V, Y.card ≤ (p + 1) * N →
      chromatic (G.induce (Y : Set V)) ≤ q)
    (hχ : prevLoss + p * x + q + 4 * (3 * p * x) + 7 * k ≤
      chromatic G)
    (hreserve : prevLoss + p * x + q + 4 * (3 * p * x) + 6 * k ≤ m)
    (hSourceFan : 3 * (3 * p * x) ≤ k)
    (hSourceFinish : 2 * (3 * p * x) ≤ ℓ)
    (hMixedBudget : 3 * p * x + 2 * ((p + 1) * x) ≤ k)
    (hMiddleSize : 2 * ((p + 1) * x) ≤ k)
    (hFinishSize : 2 * ((p + 1) * x) ≤ ℓ)
    (hChildRoots : 2 * x ≤ ℓ)
    (hWoven : ∀ i : Fin p, Woven (G.induce (K i.castSucc : Set V))
      (2 * x) ((4 * p + 1) * x))
    (hKnitting : 33 * ((4 * p + 1) * x) ≤ ℓ)
    (hCoreBudget : oldBound + p * N + N + (p + 1) * x ≤ coreBound) :
    Nonempty (StageState G ((p + 1) * x) k m coreBound) := by
  classical
  let J : Fin p → Finset V := fun i => K i.castSucc
  let D : Finset V := K (Fin.last p)
  have hJ (i : Fin p) := hK i.castSucc
  have hD := hK (Fin.last p)
  have hJdis : ∀ i j, i ≠ j →
      Disjoint (J i : Set V) (J j : Set V) := by
    intro i j hij
    exact Finset.disjoint_coe.mpr
      (hKpair (fun h => hij (Fin.castSucc_injective p h)))
  have hJDfin : ∀ i, Disjoint (J i) D := by
    intro i
    exact hKpair (Fin.castSucc_ne_last i)
  have hJconn : ∀ i,
      VertexConnected (G.induce (J i : Set V)) ℓ :=
    fun i => (hJ i).2.2
  obtain ⟨childRoot,hrootinj,hrootJ⟩ :=
    exists_child_roots_of_connected_pieces G p x ℓ J hJconn
      hChildRoots
  let oldRoot := S.ciOldRoot
  let A := S.ciOldModel
  have hAJ : ∀ i,
      Disjoint A.toMinorModel.vertices (J i : Set V) := by
    intro i
    exact S.ciOldModel_disjoint_piece hrootregion (J i) (hJ i).1
  let Z : Finset V :=
    Finset.univ.image (ciSourceValue p x oldRoot childRoot)
  have hZcard : Z.card = 3 * p * x :=
    ciSourceFinset_card_of_pieces p x G oldRoot A J childRoot
      hrootinj hrootJ hJdis hAJ
  have hZR : Z ⊆ S.region := by
    apply ciSourceFinset_subset p x oldRoot childRoot S.region
    · intro z
      exact hrootregion (finProdFinEquiv z)
    · intro i z
      exact (Finset.mem_sdiff.mp ((hJ i).1 (hrootJ i z))).1
  have hDR : D ⊆ S.region := by
    intro v hv
    exact (Finset.mem_sdiff.mp (hD.1 hv)).1
  have hOldD : Disjoint (Finset.univ.image oldRoot) D := by
    rw [S.ciOldRoot_image_eq_tangentFinset]
    apply Finset.disjoint_left.mpr
    intro v hvOld hvD
    exact (Finset.mem_sdiff.mp (hD.1 hvD)).2 hvOld
  have hZD : Disjoint Z D :=
    ciSourceFinset_disjoint_of_old_and_children p x oldRoot
      childRoot J hrootJ D hOldD hJDfin
  have hDsize : 2 * Z.card ≤ D.card := by
    have horder := hD.2.2.order_gt
    have hcard : Fintype.card (D : Set V) = D.card := by
      apply Fintype.card_of_finset' D
      intro v
      rfl
    rw [hcard] at horder
    rw [hZcard]
    omega
  obtain ⟨F,hFR,hFcost⟩ :=
    Woven.exists_double_fan_inside_connected_region G
      S.region Z D k S.region_connected hZR hDR
      (by rw [hZcard]; exact hSourceFan) hDsize hZD
  have hFcost' :
      chromatic (G.induce (F.vertexFinset : Set V)) ≤
        4 * (3 * p * x) := by
    rw [← hZcard]
    exact hFcost
  let Kall : Finset V :=
    (Finset.univ : Finset (Fin (p + 1))).biUnion K
  obtain ⟨U,hUraw,hUconn,hUreserve⟩ :=
    S.exists_middle_region_after_pieces_and_fan hrootregion
      (p + 1) N q (4 * (3 * p * x)) k m
      K (fun i => (hK i).2.1) F.vertexFinset hFcost'
      hlocal hk hχ hreserve
  have hUsub : U ⊆ S.region := by
    intro v hv
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hUraw hv)).1).1
  have hUavoidK : Disjoint Kall U := by
    apply Finset.disjoint_left.mpr
    intro v hvK hvU
    exact (Finset.mem_sdiff.mp (hUraw hvU)).2
      (Finset.mem_union_left _ hvK)
  have hUavoidF : Disjoint F.vertexFinset U := by
    apply Finset.disjoint_left.mpr
    intro v hvF hvU
    exact (Finset.mem_sdiff.mp (hUraw hvU)).2
      (Finset.mem_union_right _ hvF)
  have hJsubK (i : Fin p) : J i ⊆ Kall := by
    intro v hv
    exact Finset.mem_biUnion.mpr
      ⟨i.castSucc,Finset.mem_univ _,hv⟩
  have hDsubK : D ⊆ Kall := by
    intro v hv
    exact Finset.mem_biUnion.mpr
      ⟨Fin.last p,Finset.mem_univ _,hv⟩
  have hJUfin : ∀ i, Disjoint (J i) U := by
    intro i
    exact hUavoidK.mono_left (hJsubK i)
  have hDUfin : Disjoint D U :=
    hUavoidK.mono_left hDsubK
  have hOldU : Disjoint (Finset.univ.image oldRoot) U := by
    rw [S.ciOldRoot_image_eq_tangentFinset]
    apply Finset.disjoint_left.mpr
    intro v hvOld hvU
    exact (Finset.mem_sdiff.mp
      (Finset.mem_sdiff.mp (hUraw hvU)).1).2 hvOld
  have hZU : Disjoint Z U :=
    ciSourceFinset_disjoint_of_old_and_children p x oldRoot
      childRoot J hrootJ U hOldU hJUfin
  have hUdiff : U ⊆ S.region \ Z := by
    intro v hv
    exact Finset.mem_sdiff.mpr
      ⟨hUsub hv,fun hz => (Finset.disjoint_left.mp hZU) hz hv⟩
  have hDdiff : D ⊆ S.region \ Z := by
    intro v hv
    exact Finset.mem_sdiff.mpr
      ⟨hDR hv,fun hz => (Finset.disjoint_left.mp hZD) hz hv⟩
  have hUsize : 2 * ((p + 1) * x) ≤ U.card := by
    have horder := hUconn.order_gt
    have hcard : Fintype.card (U : Set V) = U.card := by
      apply Fintype.card_of_finset' U
      intro v
      rfl
    rw [hcard] at horder
    omega
  have hDsize' : 2 * ((p + 1) * x) ≤ D.card := by
    have horder := hD.2.2.order_gt
    have hcard : Fintype.card (D : Set V) = D.card := by
      apply Fintype.card_of_finset' D
      intro v
      rfl
    rw [hcard] at horder
    omega
  have hJD : ∀ i, Disjoint (J i : Set V) (D : Set V) := by
    intro i
    apply Set.disjoint_left.mpr
    intro v hvJ hvD
    exact (Finset.disjoint_left.mp (hJDfin i)) hvJ hvD
  have hJU : ∀ i, Disjoint (J i : Set V) (U : Set V) := by
    intro i
    apply Set.disjoint_left.mpr
    intro v hvJ hvU
    exact (Finset.disjoint_left.mp (hJUfin i)) hvJ hvU
  have hDconn : VertexConnected (G.induce (D : Set V))
      (33 * ((4 * p + 1) * x)) :=
    hD.2.2.of_le hKnitting
  have hCoreWitness := S.ciOldModel_core_witness
  have hRaw := ci_nonzero_raw_stage_from_pieces G p x k m
    ((4 * p + 1) * x) N oldBound coreBound hp
    S.region Z U D J oldRoot A S.core childRoot rfl
    hrootinj hrootJ hJdis hJD hJU hAJ
    (S.ciOldModel_tangent hrootregion)
    hCoreWitness S.core_card_le
    (fun i => (hJ i).2.1) hD.2.1 hCoreBudget
    hWoven le_rfl F hFR S.region_connected hZR
    (by rw [hZcard]; exact hMixedBudget)
    hUdiff hDdiff hUsize hDsize' hUavoidF hDUfin
    hDconn hUconn hUreserve
  exact hRaw

end HadwigerLean.Inseparability




