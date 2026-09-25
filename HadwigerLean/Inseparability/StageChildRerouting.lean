import HadwigerLean.Inseparability.StageChildReindex
import HadwigerLean.Inseparability.RawModelCI
import HadwigerLean.Inseparability.RawModelAttachment
import HadwigerLean.Woven.ManyChildRerouting

/-!
# CI child rerouting with two-sided branch labels

Apply the finite sequential woven rerouting theorem to all p small
pieces, then convert each rooted K_(2x) model to the side-and-offset
branch labels required by the raw CI model.
-/

namespace HadwigerLean.Inseparability

universe u

theorem ci_reroute_through_children
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (p x b : ℕ)
    (J : Fin p → Finset V)
    (hJdis : ∀ i j, i ≠ j →
      Disjoint (J i : Set V) (J j : Set V))
    (hW : ∀ i, Woven (G.induce (J i : Set V)) (2 * x) b)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (hrootinj : ∀ i, Function.Injective (childRoot i))
    (hrootJ : ∀ i z, childRoot i z ∈ J i)
    {P : IndexedPairs (CIPathIndex p x) V}
    (L₀ : IndexedLinkage G P)
    (hb : (4 * p + 1) * x ≤ b)
    (hterminal : ∀ i,
      Set.range (ciChildRootFin x (childRoot i)) ⊆ P.allTerminals) :
    ∃ (L : IndexedLinkage G P)
      (M : ∀ i, RootedMinorModel
        (SimpleGraph.completeGraph (Fin 2 × Fin x)) G (childRoot i)),
      (∀ i, (M i).toMinorModel.vertices ⊆ (J i : Set V)) ∧
      (∀ i, (M i).toMinorModel.vertices ∩ L.vertices =
        Set.range (childRoot i)) ∧
      L.vertices ⊆ L₀.vertices ∪ ⋃ i, (J i : Set V) := by
  let rootFin (i : Fin p) := ciChildRootFin x (childRoot i)
  have hrootFinInj : ∀ i, Function.Injective (rootFin i) := by
    intro i n m h
    apply (finProdFinEquiv : Fin 2 × Fin x ≃ Fin (2 * x)).symm.injective
    exact hrootinj i h
  have hrootFinJ : ∀ i z, rootFin i z ∈ J i := by
    intro i z
    exact hrootJ i (finProdFinEquiv.symm z)
  obtain ⟨L,M₀,hMsub,hMexact,hLsub⟩ :=
    Woven.reroute_linkage_through_all_children
      p (2 * x) b ((4 * p + 1) * x) J hJdis hW
      rootFin hrootFinInj hrootFinJ L₀ hb hterminal
  let M (i : Fin p) := ciChildModelReindex x (childRoot i) (M₀ i)
  refine ⟨L,M,?_,?_,hLsub⟩
  · intro i
    change (ciChildModelReindex x (childRoot i) (M₀ i)).toMinorModel.vertices ⊆
      (J i : Set V)
    rw [ciChildModelReindex_vertices]
    exact hMsub i
  · intro i
    exact ciChildModelReindex_exact L x (childRoot i)
      (M₀ i) (hMexact i)

theorem ciChildRootFin_terminal_of_starts
    {V : Type*} (p x : ℕ)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (P : IndexedPairs (CIPathIndex p x) V)
    (hOld : ∀ i r,
      P.start (ciOldMiddleIndex p x i r) = childRoot i (0,r))
    (hNew : ∀ i r,
      P.start (ciNewMiddleIndex p x i r) = childRoot i (1,r)) :
    ∀ i, Set.range (ciChildRootFin x (childRoot i)) ⊆ P.allTerminals := by
  intro i v hv
  obtain ⟨n,rfl⟩ := hv
  let z : Fin 2 × Fin x := finProdFinEquiv.symm n
  change childRoot i z ∈ P.allTerminals
  obtain ⟨d,r⟩ := z
  have hd : d = 0 ∨ d = 1 := by
    by_cases h : d.val = 0
    · exact Or.inl (Fin.ext h)
    · right
      apply Fin.ext
      have hdlt := d.isLt
      omega
  rcases hd with rfl | rfl
  · rw [← hOld i r]
    exact Set.mem_iUnion.mpr
      ⟨ciOldMiddleIndex p x i r, by simp [IndexedPairs.terminals]⟩
  · rw [← hNew i r]
    exact Set.mem_iUnion.mpr
      ⟨ciNewMiddleIndex p x i r, by simp [IndexedPairs.terminals]⟩

end HadwigerLean.Inseparability


