import HadwigerLean.Graph.RootedDensity.Universal
import Mathlib.Tactic

/-! Universality of a target minor is invariant under host-graph isomorphism. -/

namespace HadwigerLean.RootedDensity

universe u v w

/-- Move rooted universality across a graph isomorphism. -/
theorem UniversalAt.of_iso
    {V : Type u} {V' : Type v} {W : Type w}
    [Fintype V] [Fintype V'] [Fintype W]
    [DecidableEq V] [DecidableEq V']
    {G : SimpleGraph V} {J : SimpleGraph V'} {H : SimpleGraph W}
    (e : G ≃g J) (X : Finset V) (h : UniversalAt G H X) :
    UniversalAt J H (X.image e) := by
  classical
  intro Y root' hroot' hrange'
  let root : ↥(Y : Set W) → V := fun i => e.symm (root' i)
  have hroot : Function.Injective root := by
    intro i j hij
    exact hroot' (e.symm.injective hij)
  have hrange : Set.range root = (X : Set V) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      have hi : root' i ∈ (X.image e : Set V') := by
        rw [← hrange']
        exact ⟨i, rfl⟩
      obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp hi
      have heq : e.symm (root' i) = x := by simp [← hxe]
      change e.symm (root' i) ∈ (X : Set V)
      rw [heq]
      exact hx
    · intro hv
      have he : e v ∈ (X.image e : Set V') :=
        Finset.mem_image.mpr ⟨v, hv, rfl⟩
      have hi : e v ∈ Set.range root' := by
        rw [hrange']
        exact he
      obtain ⟨i, hi⟩ := hi
      refine ⟨i, ?_⟩
      simp [root, hi]
  obtain ⟨M⟩ := h Y root hroot hrange
  have hM : RootedMinorModel (H.induce (Y : Set W)) J root' := by
    convert (M.map e.toHom e.injective) using 1
    funext i
    exact (e.apply_symm_apply (root' i)).symm
  exact ⟨hM⟩

/-- Full universality transfers across a graph isomorphism. -/
theorem Universal.of_iso
    {V : Type u} {V' : Type v} {W : Type w}
    [Fintype V] [Fintype V'] [Fintype W]
    [DecidableEq V] [DecidableEq V']
    {G : SimpleGraph V} {J : SimpleGraph V'} {H : SimpleGraph W}
    (e : G ≃g J) (h : Universal G H) : Universal J H := by
  classical
  constructor
  · simpa [Fintype.card_congr e.toEquiv] using h.1
  intro X' hX'
  let X : Finset V := X'.image e.symm
  have hcard : X.card = Fintype.card W := by
    rw [Finset.card_image_of_injective _ e.symm.injective]
    exact hX'
  have hXmap : X.image e = X' := by
    ext x
    simp [X]
  simpa only [hXmap] using UniversalAt.of_iso e X (h.2 X hcard)

end HadwigerLean.RootedDensity



