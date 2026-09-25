import HadwigerLean.Woven.MixedFanProject
import Mathlib.Tactic

/-!
# Saturating all old and paired sources in the mixed linkage
-/

namespace HadwigerLean
namespace Woven

variable {W ι : Type*} [Fintype W] [DecidableEq W] [Fintype ι]
  {E : SimpleGraph W} {Q : IndexedPairs ι W}

/-- A disjoint linkage with as many paths as source vertices uses every
source exactly once. -/
theorem IndexedLinkage.start_surjective_of_card_eq
    (M : IndexedLinkage E Q) (A : Finset W)
    (hstart : ∀ i, Q.start i ∈ A)
    (hcard : Fintype.card ι = A.card)
    (x : W) (hx : x ∈ A) : ∃ i, Q.start i = x := by
  classical
  let I : Finset W := Finset.univ.image Q.start
  have hI : I.card = Fintype.card ι := by
    simp [I, Finset.card_image_of_injective _ M.start_injective]
  have hsub : I ⊆ A := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    exact hstart i
  have heq : I = A := Finset.eq_of_subset_of_card_le hsub (by omega)
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (heq ▸ hx)
  exact ⟨i,hi⟩

/-- A saturated linkage path meets the source set only at its own start. -/
theorem IndexedLinkage.source_only_of_start_surjective
    (M : IndexedLinkage E Q) (A : Finset W)
    (hsurj : ∀ x ∈ A, ∃ i, Q.start i = x)
    (i : ι) (x : W) (hx : x ∈ pathVertexSet (M.path i))
    (hxA : x ∈ A) : x = Q.start i := by
  obtain ⟨j,hj⟩ := hsurj x hxA
  by_cases hji : j = i
  · subst j
    exact hj.symm
  · have hxj : x ∈ pathVertexSet (M.path j) := by
      rw [← hj]
      exact pathVertexSet.start_mem (M.path j)
    have hij : i ≠ j := Ne.symm hji
    exact False.elim ((Set.disjoint_left.mp (M.disjoint hij)) hx hxj)


section Paired

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {Z H : Finset V} {a : ℕ}
  {P : IndexedPairs (Fin a × Fin 2) V}

/-- Every old proxy and every auxiliary pair vertex is used as a start
in the full mixed Menger linkage. -/
theorem pairedMixed_start_surjective
    (Q : IndexedPairs (Fin ((pairedFanLeftSet (a := a) Z).card +
        (pairedFanRightSet (V := V) (a := a)).card))
      (PairedFanVertex V a))
    (M : IndexedLinkage (pairedFanGraph G P.start) Q)
    (hAB : SetMenger.IsABLinkage M
      (pairedFanLeftSet (a := a) Z ∪
        pairedFanRightSet (V := V) (a := a))
      (pairedFanLeftSet (a := a) H))
    (x : PairedFanVertex V a)
    (hx : x ∈ pairedFanLeftSet (a := a) Z ∪
      pairedFanRightSet (V := V) (a := a)) :
    ∃ j, Q.start j = x := by
  classical
  let A₁ := pairedFanLeftSet (a := a) Z
  let A₂ := pairedFanRightSet (V := V) (a := a)
  have hcard : Fintype.card (Fin (A₁.card + A₂.card)) =
      (A₁ ∪ A₂).card := by
    rw [Finset.card_union_of_disjoint (pairedFanLeftRight_disjoint Z)]
    simp [A₁, A₂]
  exact HadwigerLean.Woven.IndexedLinkage.start_surjective_of_card_eq M (A₁ ∪ A₂) hAB.1 hcard x hx

end Paired
end Woven
end HadwigerLean
