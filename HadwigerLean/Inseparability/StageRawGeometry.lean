import HadwigerLean.Inseparability.StageMixedIndexed
import HadwigerLean.Inseparability.StageChildRerouting
import HadwigerLean.Inseparability.StageOldMixedExact
import HadwigerLean.Inseparability.StageModelPlacement
import HadwigerLean.Inseparability.StageMixedStartClean
import HadwigerLean.Inseparability.StageExtraAvoid
import HadwigerLean.Inseparability.StageCoreWitness
import HadwigerLean.Inseparability.RawModelStage

/-!
# The nonzero CI raw stage from a mixed fan and woven child pieces

This packages the mixed Menger paths, all-child rerouting, exact model
intersections, knitting, and raw rooted-model assembly into one stage.
The chromatic extraction of the regions and the double fan are separate.
-/

namespace HadwigerLean.Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ci_nonzero_raw_stage_from_geometry
    (G : SimpleGraph V) (p x k m b N oldBound coreBound : ℕ)
    (hp : 0 < p)
    (R W Z U D : Finset V) (J : Fin p → Finset V)
    (oldRoot : Fin p × Fin x → V)
    (A : RootedMinorModel
      (SimpleGraph.completeGraph (Fin p × Fin x)) G oldRoot)
    (oldCore : Finset V)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (source : Fin (3 * p * x) ≃ Z)
    (hOldSource : ∀ i r,
      (source (ciSourceBlock p x ⟨i.val, by omega⟩ r)).1 =
        oldRoot (i,r))
    (hChildOldSource : ∀ i r,
      (source (ciSourceBlock p x ⟨p + 2 * i.val, by omega⟩ r)).1 =
        childRoot i (0,r))
    (hChildNewSource : ∀ i r,
      (source (ciSourceBlock p x
        ⟨p + 2 * i.val + 1, by omega⟩ r)).1 =
        childRoot i (1,r))
    (hrootinj : ∀ i, Function.Injective (childRoot i))
    (hrootJ : ∀ i z, childRoot i z ∈ J i)
    (hJdis : ∀ i j, i ≠ j →
      Disjoint (J i : Set V) (J j : Set V))
    (hJD : ∀ i, Disjoint (J i : Set V) (D : Set V))
    (hJU : ∀ i, Disjoint (J i : Set V) (U : Set V))
    (hAJ : ∀ i, Disjoint A.toMinorModel.vertices (J i : Set V))
    (htangent : ∀ z, A.branch z ∩ (R : Set V) = {oldRoot z})
    (hOldW : ∀ z, oldRoot z ∈ W)
    (hOldWitness : ∀ z w, z ≠ w →
      ∃ a ∈ A.branch z, ∃ c ∈ A.branch w,
        a ∈ oldCore ∧ c ∈ oldCore ∧ G.Adj a c)
    (hOldCard : oldCore.card ≤ oldBound)
    (hJcard : ∀ i, (J i).card ≤ N)
    (hDcardBound : D.card ≤ N)
    (hCoreBudget : oldBound + p * N + N + (p + 1) * x ≤ coreBound)
    (hWoven : ∀ i, Woven (G.induce (J i : Set V)) (2 * x) b)
    (hb : (4 * p + 1) * x ≤ b)
    (F : Woven.DoubleFan G Z D)
    (hFR : F.vertexFinset ⊆ R)
    (hconn : VertexConnected (G.induce (R : Set V)) k)
    (hWR : W ⊆ R) (hZW : Z ⊆ W)
    (hbudget : W.card + 2 * ((p + 1) * x) ≤ k)
    (hU : U ⊆ R \ W) (hD : D ⊆ R \ W)
    (hUcard : 2 * ((p + 1) * x) ≤ U.card)
    (hDcard : 2 * ((p + 1) * x) ≤ D.card)
    (hFU : Disjoint F.vertexFinset U)
    (hDU : Disjoint D U)
    (hDconn : VertexConnected (G.induce (D : Set V))
      (33 * ((4 * p + 1) * x)))
    (hUconn : VertexConnected (G.induce (U : Set V)) k)
    (hReserve : chromatic G ≤ chromatic (G.induce (U : Set V)) + m) :
    Nonempty (StageState G ((p + 1) * x) k m coreBound) := by
  classical
  obtain ⟨P,L₀,root,hOldStart,hChildOldStart,hChildNewStart,
    hFinal,hFinishD,hCleanD₀,hCleanU₀,hSupport₀⟩ :=
    exists_stage_mixed_paths_indexed G p x k R W Z U D F source
      oldRoot childRoot hOldSource hChildOldSource hChildNewSource
      hconn hWR hZW hbudget hU hD hUcard hDcard hFU hDU
  have hterminal :=
    ciChildRootFin_terminal_of_starts p x childRoot P
      hChildOldStart hChildNewStart
  obtain ⟨L,M,hMsub,hMexact,hLsub⟩ :=
    ci_reroute_through_children p x b J hJdis hWoven
      childRoot hrootinj hrootJ L₀ hb hterminal
  let Jall : Set V := ⋃ i, (J i : Set V)
  have hJallD : Disjoint Jall (D : Set V) := by
    apply Set.disjoint_left.mpr
    intro v hvJ hvD
    obtain ⟨i,hvi⟩ := Set.mem_iUnion.mp hvJ
    exact (Set.disjoint_left.mp (hJD i)) hvi hvD
  have hJallU : Disjoint Jall (U : Set V) := by
    apply Set.disjoint_left.mpr
    intro v hvJ hvU
    obtain ⟨i,hvi⟩ := Set.mem_iUnion.mp hvJ
    exact (Set.disjoint_left.mp (hJU i)) hvi hvU
  have hAD : Disjoint A.toMinorModel.vertices (D : Set V) := by
    apply rooted_model_disjoint_piece_of_tangent A
      (R : Set V) (W : Set V) (D : Set V) htangent
    · intro v hv
      exact Finset.mem_sdiff.mp (hD hv)
    · exact hOldW
  have hAU : Disjoint A.toMinorModel.vertices (U : Set V) := by
    apply rooted_model_disjoint_piece_of_tangent A
      (R : Set V) (W : Set V) (U : Set V) htangent
    · intro v hv
      exact Finset.mem_sdiff.mp (hU hv)
    · exact hOldW
  have hAChild : ∀ i,
      Disjoint A.toMinorModel.vertices (M i).toMinorModel.vertices := by
    intro i
    exact (hAJ i).mono_right (hMsub i)
  have hChildChild : ∀ i j, i ≠ j →
      Disjoint (M i).toMinorModel.vertices
        (M j).toMinorModel.vertices := by
    intro i j hij
    exact (hJdis i j hij).mono (hMsub i) (hMsub j)
  have hMD : ∀ i, Disjoint (M i).toMinorModel.vertices (D : Set V) := by
    intro i
    exact hJallD.mono_left
      (fun v hv => Set.mem_iUnion.mpr ⟨i,hMsub i hv⟩)
  have hMU : ∀ i, Disjoint (M i).toMinorModel.vertices (U : Set V) := by
    intro i
    exact hJallU.mono_left
      (fun v hv => Set.mem_iUnion.mpr ⟨i,hMsub i hv⟩)
  have hAall : Disjoint A.toMinorModel.vertices Jall := by
    apply Set.disjoint_left.mpr
    intro v hvA hvJ
    obtain ⟨i,hvi⟩ := Set.mem_iUnion.mp hvJ
    exact (Set.disjoint_left.mp (hAJ i)) hvA hvi
  have hOldExact₀ :
      A.toMinorModel.vertices ∩ L₀.vertices = Set.range oldRoot :=
    ci_mixed_old_model_intersection p x G R W oldRoot A L₀
      F.vertexFinset hFR hSupport₀ htangent hOldStart
  have hOldRootsL : Set.range oldRoot ⊆ L.vertices := by
    rintro v ⟨⟨i,r⟩,rfl⟩
    rw [← hOldStart i r]
    exact L.start_mem_vertices (ciOldStartIndex p x i r)
  have hOldExact :
      A.toMinorModel.vertices ∩ L.vertices = Set.range oldRoot :=
    rooted_model_exact_inter_linkage_of_reroute A L₀ L Jall
      hOldExact₀ hLsub hAall hOldRootsL
  have hCleanD : ∀ k v, v ∈ pathVertexSet (L.path k) →
      v ∈ D → v = P.finish k :=
    Woven.IndexedLinkage.clean_finish_of_supported_reroute
      L₀ L (D : Set V) Jall hCleanD₀ hLsub hJallD
  have hCleanU : ∀ k v, v ∈ pathVertexSet (L.path k) →
      v ∈ U → v = root (pathOwner p x k) :=
    ci_path_H3_only_root_after_reroute L₀ L root
      (U : Set V) Jall (fun z => (hFinal z).1)
      hCleanU₀ hLsub hJallU
  let core := ciNextCore p x oldCore J D root
  have hCoreCard : core.card ≤ coreBound := by
    have h := ciNextCore_card_le p x N oldBound oldCore J D root
      hOldCard hJcard hDcardBound
    exact h.trans hCoreBudget
  have hExtraD : ∀ z j, j ∈ ciExtraIndex p x z →
      Disjoint
        (ciExtraPiece p x A.toMinorModel
          (fun i => (M i).toMinorModel) z j) (D : Set V) := by
    intro z j _
    exact ciExtraPiece_disjoint_of_models p x A.toMinorModel
      (fun i => (M i).toMinorModel) (D : Set V) hAD hMD z j
  have hExtraU : ∀ z j, j ∈ ciExtraIndex p x z →
      Disjoint
        (ciExtraPiece p x A.toMinorModel
          (fun i => (M i).toMinorModel) z j) (U : Set V) := by
    intro z j _
    exact ciExtraPiece_disjoint_of_models p x A.toMinorModel
      (fun i => (M i).toMinorModel) (U : Set V) hAU hMU z j
  have hFinalRoot : ∀ z,
      root z ∈ pathVertexSet (L.path (ciFinalIndex p x z)) := by
    intro z
    rw [(hFinal z).1]
    exact pathVertexSet.start_mem (L.path (ciFinalIndex p x z))
  have hOldTerm : ∀ i r,
      oldRoot (i,r) ∈ P.terminals (ciOldStartIndex p x i r) := by
    intro i r
    rw [← hOldStart i r]
    simp [IndexedPairs.terminals]
  have hChildOldTerm : ∀ i r,
      childRoot i (0,r) ∈ P.terminals (ciOldMiddleIndex p x i r) := by
    intro i r
    rw [← hChildOldStart i r]
    simp [IndexedPairs.terminals]
  have hChildNewTerm : ∀ i r,
      childRoot i (1,r) ∈ P.terminals (ciNewMiddleIndex p x i r) := by
    intro i r
    rw [← hChildNewStart i r]
    simp [IndexedPairs.terminals]
  have hOldCore : ∀ z w, z ≠ w →
      ∃ a ∈ A.branch z, ∃ c ∈ A.branch w,
        a ∈ core ∧ c ∈ core ∧ G.Adj a c :=
    ciNextCore_old_witness p x G oldCore J D root oldRoot A
      hOldWitness
  have hChildCore : ∀ i z, (M i).branch z ⊆ (core : Set V) :=
    ciNextCore_child_branch_subset p x G oldCore J D root
      childRoot M hMsub
  have hDUset : Disjoint (D : Set V) (U : Set V) := by
    apply Set.disjoint_left.mpr
    intro v hvD hvU
    exact (Finset.disjoint_left.mp hDU) hvD hvU
  obtain ⟨Nmodel,hTangent,hWitness,hIntersection⟩ :=
    ci_nonzero_raw_model_from_linkage p x hp G D hDconn
      oldRoot A childRoot M L root (U : Set V) (core : Set V)
      hFinishD hCleanD hExtraD hExtraU hDUset
      hAChild hChildChild hOldExact hMexact
      hOldTerm hChildOldTerm hChildNewTerm
      hFinalRoot (fun z => (hFinal z).2) hCleanU
      (ciNextCore_root_mem p x oldCore J D root)
      hOldCore hChildCore
  exact stageState_of_raw_model G p x k m coreBound root Nmodel
    core U hUconn hReserve hCoreCard
    hTangent hWitness hIntersection

end HadwigerLean.Inseparability


