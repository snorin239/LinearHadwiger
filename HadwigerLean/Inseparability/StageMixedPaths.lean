import HadwigerLean.Inseparability.StagePairedConnectors
import HadwigerLean.Woven.MixedFanSupportContainment

/-!
# Mixed paths for a chromatic inseparability stage

The doubled old-source fan and the paired middle-region connectors are
combined by redundant Menger. The result keeps one path per old source
and one per middle-region pair, with exact intersections with all three
distinguished sets and support inside the two supplied path families.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_stage_mixed_paths
    (G : SimpleGraph V) (R W Z U D : Finset V) (k s : ℕ)
    (F : Woven.DoubleFan G Z D)
    (hconn : VertexConnected (G.induce (R : Set V)) k)
    (hWR : W ⊆ R) (hZW : Z ⊆ W)
    (hbudget : W.card + 2 * s ≤ k)
    (hU : U ⊆ R \ W) (hD : D ⊆ R \ W)
    (hUcard : 2 * s ≤ U.card) (hDcard : 2 * s ≤ D.card)
    (hFU : Disjoint F.vertexFinset U)
    (hDU : Disjoint D U) :
    ∃ (P : IndexedPairs (Z ⊕ Fin s) V)
      (L : IndexedLinkage G P),
      (∀ z : Z, P.start (.inl z) = z.1) ∧
      (∀ i : Fin s, P.start (.inr i) ∈ U) ∧
      SetMenger.IsABLinkage L (Z ∪ U) D ∧
      (∀ i v, v ∈ pathVertexSet (L.path i) →
        v ∈ Z ∪ U ∪ D → v = P.start i ∨ v = P.finish i) ∧
      (∀ i, pathVertexSet (L.path i) ⊆
        (F.vertexFinset : Set V) ∪ ((R \ W : Finset V) : Set V)) := by
  obtain ⟨Q,M,hAB,hMR,honlyU,_⟩ :=
    exists_clean_paired_connectors_after_delete G R W U D k s
      hconn hWR hbudget hU hD hUcard hDcard
  have havoidZ (slot) (v) (hv : v ∈ pathVertexSet (M.path slot)) :
      v ∉ Z := by
    intro hvZ
    have hvRW : v ∈ R \ W := hMR slot hv
    exact (Finset.mem_sdiff.mp hvRW).2 (hZW hvZ)
  have hfanU (slot) (v) (hv : v ∈ pathVertexSet (F.path slot)) :
      v ∉ U := by
    have hvF : v ∈ F.vertexFinset := by
      apply Finset.mem_biUnion.mpr
      exact ⟨slot,Finset.mem_univ _,List.mem_toFinset.mpr hv⟩
    exact (Finset.disjoint_left.mp hFU) hvF
  have hZU : Disjoint Z U := by
    apply Finset.disjoint_left.mpr
    intro z hzZ hzU
    exact (Finset.mem_sdiff.mp (hU hzU)).2 (hZW hzZ)
  obtain ⟨P,L,hproxy,hpair,hABmixed,hclean,hsupp⟩ :=
    Woven.exists_mixed_linkage_clean_supported F M U
      hAB.1 hAB.2 havoidZ hfanU honlyU hZU hDU
  refine ⟨P,L,hproxy,?_,hABmixed,hclean,?_⟩
  · intro i
    obtain ⟨b,hb⟩ := hpair i
    rw [hb]
    exact hAB.1 (i,b)
  · intro i v hv
    rcases hsupp i hv with hvF | hvM
    · exact Or.inl hvF
    · apply Or.inr
      obtain ⟨slot,hvslot⟩ := Set.mem_iUnion.mp hvM
      exact hMR slot hvslot

end Inseparability
end HadwigerLean
