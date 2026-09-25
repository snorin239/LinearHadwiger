import HadwigerLean.Woven.DoubleFanMenger
import Mathlib.Tactic

/-!
# Reindexing a saturated clone linkage by its original source slots
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A vertex-disjoint linkage with as many paths as private source
clones uses every clone exactly once as a path start. -/
theorem doubleClone_start_surjective
    (G : SimpleGraph V) (Z H : Finset V)
    (hdis : Disjoint Z H)
    (P : IndexedPairs (Fin (2 * Z.card))
      (DoubleCloneVertex V Z))
    (L : IndexedLinkage (doubleCloneGraph G Z) P)
    (hAB : SetMenger.IsABLinkage L
      (doubleCloneSources Z) (doubleCloneTargets Z H hdis))
    (c : DoubleCloneVertex V Z)
    (hc : c ∈ doubleCloneSources Z) :
    ∃ j : Fin (2 * Z.card), P.start j = c := by
  classical
  let I : Finset (DoubleCloneVertex V Z) :=
    Finset.univ.image P.start
  have hI : I.card = 2 * Z.card := by
    change (Finset.univ.image P.start).card = 2 * Z.card
    rw [Finset.card_image_of_injective _ L.start_injective]
    simp
  have hsub : I ⊆ doubleCloneSources Z := by
    intro v hv
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hv
    exact hAB.1 j
  have hIeq : I = doubleCloneSources Z := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [doubleCloneSources_card, hI]
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp (hIeq ▸ hc)
  exact ⟨j,hj⟩

/-- Every source slot has a distinguished path index, and
different slots receive different indices. -/
theorem doubleClone_slot_index
    (G : SimpleGraph V) (Z H : Finset V)
    (hdis : Disjoint Z H)
    (P : IndexedPairs (Fin (2 * Z.card))
      (DoubleCloneVertex V Z))
    (L : IndexedLinkage (doubleCloneGraph G Z) P)
    (hAB : SetMenger.IsABLinkage L
      (doubleCloneSources Z) (doubleCloneTargets Z H hdis)) :
    ∃ f : Z × Fin 2 → Fin (2 * Z.card),
      Function.Injective f ∧
      ∀ slot, P.start (f slot) =
        doubleClone Z slot.1 slot.2 := by
  classical
  let f (slot : Z × Fin 2) : Fin (2 * Z.card) :=
    Classical.choose (doubleClone_start_surjective G Z H hdis P L hAB
      (doubleClone Z slot.1 slot.2)
      (doubleClone_mem_sources Z slot.1 slot.2))
  have hf (slot : Z × Fin 2) :
      P.start (f slot) = doubleClone Z slot.1 slot.2 :=
    Classical.choose_spec (doubleClone_start_surjective G Z H hdis P L hAB
      (doubleClone Z slot.1 slot.2)
      (doubleClone_mem_sources Z slot.1 slot.2))
  refine ⟨f, ?_, hf⟩
  intro x y hxy
  have hclone := (hf x).symm.trans ((congrArg P.start hxy).trans (hf y))
  exact Sum.inr_injective hclone

end Woven
end HadwigerLean
