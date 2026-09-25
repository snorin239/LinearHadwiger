import HadwigerLean.Graph.RootedDensity.RigidLabels
import HadwigerLean.Graph.RootedDensity.FanExtension
import Mathlib.Tactic

/-!
# Attaching an arbitrary target model through a clean fan to a rigid shore

A universal rigid far shore supplies a rooted model at any injectively
labeled subset of its adhesion. A clean fan brings those roots back to
the prescribed starts without altering disjointness.
-/

namespace HadwigerLean.RootedDensity

universe u v

theorem rootedMinor_of_universal_right_and_clean_fan
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) (S : VertexSeparation G)
    (H : SimpleGraph W)
    (huni : UniversalAtRightShore H S)
    (hsize : (Linkedness.separationBoundaryFinset S).card ≤ Fintype.card W)
    (Y : Finset W)
    (P : IndexedPairs ↥(Y : Set W) V)
    (L : IndexedLinkage G P)
    (hfinish : ∀ i, P.finish i ∈ S.separator)
    (hclean : ∀ i x, x ∈ pathVertexSet (L.path i) →
      x ∈ S.right → x = P.finish i) :
    Nonempty (RootedMinorModel (H.induce (Y : Set W)) G P.start) := by
  classical
  let arrival : ↥(Y : Set W) → S.right :=
    fun i => ⟨P.finish i,(hfinish i).2⟩
  have harrinj : Function.Injective arrival := by
    intro i j heq
    exact L.finish_injective (congrArg Subtype.val heq)
  let A : Finset S.right := Finset.univ.image arrival
  have hAZ : A ⊆ Linkedness.separationBoundaryFinset S := by
    intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    exact (Linkedness.mem_separationBoundaryFinset S _).mpr
      (hfinish i).1
  have hA : (A : Set S.right) = Set.range arrival := by
    ext z
    simp [A]
  let e₀ := Equiv.ofInjective arrival harrinj
  let e : ↥(Y : Set W) ≃ ↥(A : Set S.right) :=
    e₀.trans (Equiv.setCongr hA.symm)
  let f : ↥(A : Set S.right) → W := fun a => (e.symm a).1
  have hf : Function.Injective f :=
    Subtype.val_injective.comp e.symm.injective
  obtain ⟨Y',r',⟨N⟩,hr⟩ :=
    rigid_shore_model_of_partial_labels G S H huni A hAZ f hf hsize
  have hYY' : (Y : Set W) ⊆ (Y' : Set W) := by
    intro y hy
    let i : ↥(Y : Set W) := ⟨y,hy⟩
    have hi := (hr (e i)).choose
    have hfi : f (e i) = y := by
      simp [f,i]
    simpa only [hfi, Finset.mem_coe] using hi
  let R := rooted_model_restrict_to_subset N (Y : Set W) hYY'
  have hrootEq : (fun i : ↥(Y : Set W) =>
      r' ⟨i.1,hYY' i.2⟩) = arrival := by
    funext i
    obtain ⟨hi,hri⟩ := hr (e i)
    have hfi : f (e i) = i.1 := by
      simp [f]
    have hArg : (⟨f (e i),hi⟩ : ↥(Y' : Set W)) =
        ⟨i.1,hYY' i.2⟩ := Subtype.ext hfi
    have hArrival : (e i).1 = arrival i := rfl
    rw [hArg,hArrival] at hri
    exact hri
  have hmodel : Nonempty (RootedMinorModel
      (H.induce (Y : Set W)) (G.induce S.right) arrival) := by
    rw [← hrootEq]
    exact ⟨R⟩
  exact rootedMinor_of_induced_rootedMinor_and_clean_fan
    L S.right (fun i => (hfinish i).2) hclean hmodel

end HadwigerLean.RootedDensity
