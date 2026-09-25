import HadwigerLean.Inseparability.StageSourceEnumeration
import HadwigerLean.Graph.RootedMinor

/-!
# Enumerating source roots before the child models are constructed

The selected roots in disjoint child pieces and the old rooted model
already give the distinct source enumeration needed for the mixed fan.
-/

namespace HadwigerLean.Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ci_child_roots_global_injective
    (p x : ℕ) (J : Fin p → Finset V)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (hrootinj : ∀ i, Function.Injective (childRoot i))
    (hrootJ : ∀ i z, childRoot i z ∈ J i)
    (hJdis : ∀ i j, i ≠ j → Disjoint (J i : Set V) (J j : Set V)) :
    Function.Injective
      (fun q : Fin p × (Fin 2 × Fin x) => childRoot q.1 q.2) := by
  intro q q' h
  obtain ⟨i,z⟩ := q
  obtain ⟨j,w⟩ := q'
  change childRoot i z = childRoot j w at h
  by_cases hij : i = j
  · subst j
    exact Prod.ext rfl (hrootinj i h)
  · exfalso
    exact (Set.disjoint_left.mp (hJdis i j hij))
      (hrootJ i z) (h.symm ▸ hrootJ j w)

theorem ci_source_roots_cross_disjoint
    (p x : ℕ) (G : SimpleGraph V)
    (oldRoot : Fin p × Fin x → V)
    (A : RootedMinorModel
      (SimpleGraph.completeGraph (Fin p × Fin x)) G oldRoot)
    (J : Fin p → Finset V)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (hAJ : ∀ i, Disjoint A.toMinorModel.vertices (J i : Set V))
    (hrootJ : ∀ i z, childRoot i z ∈ J i) :
    ∀ (z : Fin p × Fin x) (q : Fin p × (Fin 2 × Fin x)),
      oldRoot z ≠ childRoot q.1 q.2 := by
  intro z q heq
  exact (Set.disjoint_left.mp (hAJ q.1))
    (Set.mem_iUnion.mpr ⟨z,A.root_mem z⟩)
    (heq ▸ hrootJ q.1 q.2)

noncomputable def ciSourceEquivOfPieces
    (p x : ℕ) (G : SimpleGraph V)
    (oldRoot : Fin p × Fin x → V)
    (A : RootedMinorModel
      (SimpleGraph.completeGraph (Fin p × Fin x)) G oldRoot)
    (J : Fin p → Finset V)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (hrootinj : ∀ i, Function.Injective (childRoot i))
    (hrootJ : ∀ i z, childRoot i z ∈ J i)
    (hJdis : ∀ i j, i ≠ j → Disjoint (J i : Set V) (J j : Set V))
    (hAJ : ∀ i, Disjoint A.toMinorModel.vertices (J i : Set V)) :
    Fin (3 * p * x) ≃
      (Finset.univ.image (ciSourceValue p x oldRoot childRoot) : Finset V) :=
  ciSourceEquiv p x oldRoot childRoot A.root_injective
    (ci_child_roots_global_injective p x J childRoot hrootinj hrootJ hJdis)
    (ci_source_roots_cross_disjoint p x G oldRoot A J childRoot hAJ hrootJ)

@[simp] theorem ciSourceEquivOfPieces_apply
    (p x : ℕ) (G : SimpleGraph V)
    (oldRoot : Fin p × Fin x → V)
    (A : RootedMinorModel
      (SimpleGraph.completeGraph (Fin p × Fin x)) G oldRoot)
    (J : Fin p → Finset V)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (hrootinj : ∀ i, Function.Injective (childRoot i))
    (hrootJ : ∀ i z, childRoot i z ∈ J i)
    (hJdis : ∀ i j, i ≠ j → Disjoint (J i : Set V) (J j : Set V))
    (hAJ : ∀ i, Disjoint A.toMinorModel.vertices (J i : Set V))
    (q : Fin (3 * p * x)) :
    ((ciSourceEquivOfPieces p x G oldRoot A J childRoot
      hrootinj hrootJ hJdis hAJ q) : V) =
      ciSourceValue p x oldRoot childRoot q := by
  exact ciSourceEquiv_apply p x oldRoot childRoot A.root_injective
    (ci_child_roots_global_injective p x J childRoot hrootinj hrootJ hJdis)
    (ci_source_roots_cross_disjoint p x G oldRoot A J childRoot hAJ hrootJ) q


theorem ciSourceEquivOfPieces_old
    (p x : ℕ) (G : SimpleGraph V)
    (oldRoot : Fin p × Fin x → V)
    (A : RootedMinorModel
      (SimpleGraph.completeGraph (Fin p × Fin x)) G oldRoot)
    (J : Fin p → Finset V)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (hrootinj : ∀ i, Function.Injective (childRoot i))
    (hrootJ : ∀ i z, childRoot i z ∈ J i)
    (hJdis : ∀ i j, i ≠ j → Disjoint (J i : Set V) (J j : Set V))
    (hAJ : ∀ i, Disjoint A.toMinorModel.vertices (J i : Set V))
    (i : Fin p) (r : Fin x) :
    ((ciSourceEquivOfPieces p x G oldRoot A J childRoot
      hrootinj hrootJ hJdis hAJ
      (ciSourceBlock p x ⟨i.val, by omega⟩ r)) : V) =
        oldRoot (i,r) := by
  rw [ciSourceEquivOfPieces_apply]
  exact ciSourceValue_old p x oldRoot childRoot i r

theorem ciSourceEquivOfPieces_child
    (p x : ℕ) (G : SimpleGraph V)
    (oldRoot : Fin p × Fin x → V)
    (A : RootedMinorModel
      (SimpleGraph.completeGraph (Fin p × Fin x)) G oldRoot)
    (J : Fin p → Finset V)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (hrootinj : ∀ i, Function.Injective (childRoot i))
    (hrootJ : ∀ i z, childRoot i z ∈ J i)
    (hJdis : ∀ i j, i ≠ j → Disjoint (J i : Set V) (J j : Set V))
    (hAJ : ∀ i, Disjoint A.toMinorModel.vertices (J i : Set V))
    (i : Fin p) (d : Fin 2) (r : Fin x) :
    ((ciSourceEquivOfPieces p x G oldRoot A J childRoot
      hrootinj hrootJ hJdis hAJ
      (ciSourceBlock p x
        ⟨p + 2 * i.val + d.val, by omega⟩ r)) : V) =
        childRoot i (d,r) := by
  rw [ciSourceEquivOfPieces_apply]
  exact ciSourceValue_child p x oldRoot childRoot i d r

theorem ciSourceFinset_card_of_pieces
    (p x : ℕ) (G : SimpleGraph V)
    (oldRoot : Fin p × Fin x → V)
    (A : RootedMinorModel
      (SimpleGraph.completeGraph (Fin p × Fin x)) G oldRoot)
    (J : Fin p → Finset V)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (hrootinj : ∀ i, Function.Injective (childRoot i))
    (hrootJ : ∀ i z, childRoot i z ∈ J i)
    (hJdis : ∀ i j, i ≠ j → Disjoint (J i : Set V) (J j : Set V))
    (hAJ : ∀ i, Disjoint A.toMinorModel.vertices (J i : Set V)) :
    (Finset.univ.image (ciSourceValue p x oldRoot childRoot)).card =
      3 * p * x := by
  have h := Fintype.card_congr
    (ciSourceEquivOfPieces p x G oldRoot A J childRoot
      hrootinj hrootJ hJdis hAJ)
  simpa only [Fintype.card_coe, Fintype.card_fin] using h.symm
end HadwigerLean.Inseparability




