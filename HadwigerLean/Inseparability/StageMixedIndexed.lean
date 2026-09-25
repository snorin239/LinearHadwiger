import HadwigerLean.Inseparability.StageMixedReindex
import Mathlib.Tactic

/-!
# Mixed CI paths in the raw-model index order

The old tangent sources and the two child-root blocks are prescribed by
an enumeration of the reserved source set. Final paths have the new
middle-region tangencies as starts. This result packages the exact
terminal data expected by the raw rooted-model assembly.
-/

namespace HadwigerLean.Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_stage_mixed_paths_indexed
    (G : SimpleGraph V) (p x k : ℕ)
    (R W Z U D : Finset V)
    (F : Woven.DoubleFan G Z D)
    (source : Fin (3 * p * x) ≃ Z)
    (oldRoot : Fin p × Fin x → V)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (hOldSource : ∀ i r,
      (source (ciSourceBlock p x ⟨i.val, by omega⟩ r)).1 =
        oldRoot (i,r))
    (hChildOldSource : ∀ i r,
      (source (ciSourceBlock p x ⟨p + 2 * i.val, by omega⟩ r)).1 =
        childRoot i (0,r))
    (hChildNewSource : ∀ i r,
      (source (ciSourceBlock p x ⟨p + 2 * i.val + 1, by omega⟩ r)).1 =
        childRoot i (1,r))
    (hconn : VertexConnected (G.induce (R : Set V)) k)
    (hWR : W ⊆ R) (hZW : Z ⊆ W)
    (hbudget : W.card + 2 * ((p + 1) * x) ≤ k)
    (hU : U ⊆ R \ W) (hD : D ⊆ R \ W)
    (hUcard : 2 * ((p + 1) * x) ≤ U.card)
    (hDcard : 2 * ((p + 1) * x) ≤ D.card)
    (hFU : Disjoint F.vertexFinset U)
    (hDU : Disjoint D U) :
    ∃ (P : IndexedPairs (CIPathIndex p x) V)
      (L : IndexedLinkage G P)
      (root : CIRawIndex p x → V),
      (∀ i r, P.start (ciOldStartIndex p x i r) = oldRoot (i,r)) ∧
      (∀ i r, P.start (ciOldMiddleIndex p x i r) =
        childRoot i (0,r)) ∧
      (∀ i r, P.start (ciNewMiddleIndex p x i r) =
        childRoot i (1,r)) ∧
      (∀ z, root z = P.start (ciFinalIndex p x z) ∧ root z ∈ U) ∧
      (∀ k, P.finish k ∈ D) ∧
      (∀ k v, v ∈ pathVertexSet (L.path k) →
        v ∈ D → v = P.finish k) ∧
      (∀ k v, v ∈ pathVertexSet (L.path k) →
        v ∈ U → v = root (pathOwner p x k)) ∧
      (∀ k, pathVertexSet (L.path k) ⊆
        (F.vertexFinset : Set V) ∪ ((R \ W : Finset V) : Set V)) := by
  classical
  obtain ⟨Q,M,hproxy,hnew,hAB,hclean,hsupp⟩ :=
    exists_stage_mixed_paths G R W Z U D k ((p + 1) * x) F
      hconn hWR hZW hbudget hU hD hUcard hDcard hFU hDU
  let e := ciPathMixedEquiv p x Z source
  let P : IndexedPairs (CIPathIndex p x) V := Q.reindex e.toEmbedding
  let L : IndexedLinkage G P := M.reindex e.toEmbedding
  let root : CIRawIndex p x → V := fun z => P.start (ciFinalIndex p x z)
  have hZU : Disjoint Z U := by
    apply Finset.disjoint_left.mpr
    intro v hvZ hvU
    exact (Finset.mem_sdiff.mp (hU hvU)).2 (hZW hvZ)
  have hZD : Disjoint Z D := by
    apply Finset.disjoint_left.mpr
    intro v hvZ hvD
    exact (Finset.mem_sdiff.mp (hD hvD)).2 (hZW hvZ)
  refine ⟨P,L,root,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i r
    change Q.start (e (ciOldStartIndex p x i r)) = oldRoot (i,r)
    rw [ciPathMixedEquiv_old_start]
    exact (hproxy _).trans (hOldSource i r)
  · intro i r
    change Q.start (e (ciOldMiddleIndex p x i r)) = childRoot i (0,r)
    rw [ciPathMixedEquiv_old_middle]
    exact (hproxy _).trans (hChildOldSource i r)
  · intro i r
    change Q.start (e (ciNewMiddleIndex p x i r)) = childRoot i (1,r)
    rw [ciPathMixedEquiv_new_middle]
    exact (hproxy _).trans (hChildNewSource i r)
  · intro z
    constructor
    · rfl
    · change Q.start (e (ciFinalIndex p x z)) ∈ U
      rw [ciPathMixedEquiv_final]
      exact hnew _
  · exact fun k => hAB.2 (e k)
  · intro k v hv hvD
    have hv' : v ∈ pathVertexSet (M.path (e k)) := hv
    rcases hclean (e k) v hv'
        (Finset.mem_union_right _ hvD) with hstart | hfinish
    · rcases Finset.mem_union.mp (hAB.1 (e k)) with hvZ | hvU
      · exact False.elim ((Finset.disjoint_left.mp hZD)
          (hstart ▸ hvZ) hvD)
      · exact False.elim ((Finset.disjoint_left.mp hDU)
          hvD (hstart ▸ hvU))
    · exact hfinish
  · intro k v hv hvU
    have hv' : v ∈ pathVertexSet (M.path (e k)) := hv
    rcases hclean (e k) v hv'
        (Finset.mem_union_left _ (Finset.mem_union_right _ hvU)) with
      hstart | hfinish
    · cases he : e k with
      | inl z =>
          have hz : v ∈ Z := by
            rw [hstart, he, hproxy]
            exact z.property
          exact False.elim ((Finset.disjoint_left.mp hZU) hz hvU)
      | inr i =>
          have hfinal := ciPathMixedEquiv_inr_is_final p x Z source k i he
          change v = P.start (ciFinalIndex p x (pathOwner p x k))
          rw [← hfinal]
          exact hstart
    · exact False.elim ((Finset.disjoint_left.mp hDU)
        (hfinish ▸ hAB.2 (e k)) hvU)
  · exact fun k => hsupp (e k)

end HadwigerLean.Inseparability

