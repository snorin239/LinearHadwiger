import HadwigerLean.Graph.RootedDensity.UniversalRigidFanFull
import Mathlib.Tactic

/-!
# Universality from a full fan indexed by any finite type

Reindex a full root-to-rigid-shore fan by an arbitrary injective target
label assignment. The fixed-label full-fan theorem then gives exactly
the rooted target model requested by universal-at.
-/

namespace HadwigerLean.RootedDensity

universe u v w

theorem universalAt_of_full_fan_to_universal_right_image
    {V : Type u} {W : Type v} {ι : Type w}
    [Fintype V] [DecidableEq V] [Fintype W] [Fintype ι]
    (G : SimpleGraph V) (S : VertexSeparation G)
    (H : SimpleGraph W)
    (huni : UniversalAtRightShore H S)
    (hsize : (Linkedness.separationBoundaryFinset S).card ≤ Fintype.card W)
    (P : IndexedPairs ι V) (L : IndexedLinkage G P)
    (hstartLeft : ∀ i, P.start i ∈ S.left)
    (hfinishRight : ∀ i, P.finish i ∈ S.right) :
    UniversalAt G H (Finset.univ.image P.start) := by
  classical
  let X : Finset V := Finset.univ.image P.start
  let f : ι ↪ ↥(X : Set V) := {
    toFun := fun i => ⟨P.start i,
      Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
    inj' := by
      intro i j hij
      exact L.start_injective (congrArg Subtype.val hij)
  }
  have hfSurj : Function.Surjective f := by
    intro x
    obtain ⟨i,_,hix⟩ := Finset.mem_image.mp x.property
    refine ⟨i,?_⟩
    apply Subtype.ext
    exact hix
  let e : ι ≃ ↥(X : Set V) :=
    Equiv.ofBijective f ⟨f.injective,hfSurj⟩
  intro Y root hroot hrange
  let idx : ↥(Y : Set W) ↪ ι := {
    toFun := fun y =>
      e.symm ⟨root y, by
        rw [← hrange]
        exact ⟨y,rfl⟩⟩
    inj' := by
      intro a b hab
      apply hroot
      have he : (⟨root a, by
          rw [← hrange]
          exact ⟨a,rfl⟩⟩ : ↥(X : Set V)) =
        ⟨root b, by
          rw [← hrange]
          exact ⟨b,rfl⟩⟩ := e.symm.injective hab
      exact congrArg Subtype.val he
  }
  let Q : IndexedPairs ↥(Y : Set W) V := P.reindex idx
  let F : IndexedLinkage G Q := L.reindex idx
  have hQstart : Q.start = root := by
    funext y
    have he := e.apply_symm_apply
      (⟨root y, by
        rw [← hrange]
        exact ⟨y,rfl⟩⟩ : ↥(X : Set V))
    exact congrArg Subtype.val he
  have hmodel := rootedMinor_of_universal_right_and_full_fan
    G S H huni hsize Y Q F
    (fun y => hstartLeft (idx y))
    (fun y => hfinishRight (idx y))
  rw [hQstart] at hmodel
  exact hmodel

end HadwigerLean.RootedDensity
