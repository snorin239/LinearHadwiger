import HadwigerLean.Graph.RootedDensity.UniversalRigidFanClean
import HadwigerLean.Graph.Linkedness.RegionLinkage
import Mathlib.Tactic

/-! Attach a rooted model from a universal rigid shore along a fan inside a
larger induced region. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- A clean fan confined to `R` carries arbitrary partial target roots from
an H-universal rigid shore into the graph induced on `R`. -/
theorem rootedMinor_of_universal_right_and_clean_fan_in_region
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) (S : VertexSeparation G) (R : Set V)
    (hSR : S.right ⊆ R)
    (H : SimpleGraph W)
    (huni : UniversalAtRightShore H S)
    (hsize : (Linkedness.separationBoundaryFinset S).card ≤ Fintype.card W)
    (Y : Finset W)
    (P : IndexedPairs ↥(Y : Set W) V)
    (L : IndexedLinkage G P)
    (hfinish : ∀ i, P.finish i ∈ S.separator)
    (hpathR : ∀ i x, x ∈ pathVertexSet (L.path i) → x ∈ R)
    (hclean : ∀ i x, x ∈ pathVertexSet (L.path i) →
      x ∈ S.right → x = P.finish i) :
    Nonempty (RootedMinorModel (H.induce (Y : Set W))
      (G.induce R)
      (fun i => (⟨P.start i,
        hpathR i _ (pathVertexSet.start_mem (L.path i))⟩ : R))) := by
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
  obtain ⟨Y',r',⟨M⟩,hr⟩ :=
    rigid_shore_model_of_partial_labels G S H huni A hAZ f hf hsize
  have hYY' : (Y : Set W) ⊆ (Y' : Set W) := by
    intro y hy
    let i : ↥(Y : Set W) := ⟨y,hy⟩
    have hi := (hr (e i)).choose
    have hfi : f (e i) = y := by
      simp [f,i]
    simpa only [hfi, Finset.mem_coe] using hi
  let M' := rooted_model_restrict_to_subset M (Y : Set W) hYY'
  have hrootEq : (fun i : ↥(Y : Set W) =>
      r' ⟨i.1,hYY' i.2⟩) = arrival := by
    funext i
    obtain ⟨hmem,hri⟩ := hr (e i)
    have hfi : f (e i) = i.1 := by simp [f]
    have hArg : (⟨f (e i),hmem⟩ : ↥(Y' : Set W)) =
        ⟨i.1,hYY' i.2⟩ := Subtype.ext hfi
    have hArrival : (e i).1 = arrival i := rfl
    rw [hArg,hArrival] at hri
    exact hri
  let E : (G.induce S.right) ↪g (G.induce R) :=
    G.induceHomOfLE hSR
  let N₀ : RootedMinorModel (H.induce (Y : Set W)) (G.induce R)
      (E ∘ (fun i => r' ⟨i.1,hYY' i.2⟩)) :=
    M'.map E.toHom E.injective
  let PR : IndexedPairs ↥(Y : Set W) R :=
    ⟨(fun i => ⟨P.start i,
        hpathR i _ (pathVertexSet.start_mem (L.path i))⟩),
     (fun i => ⟨P.finish i,
        hpathR i _ (pathVertexSet.finish_mem (L.path i))⟩)⟩
  let LR : IndexedLinkage (G.induce R) PR :=
    Linkedness.IndexedLinkage.induce L R hpathR
  let N' : RootedMinorModel (H.induce (Y : Set W)) (G.induce R)
      PR.finish := {
    toMinorModel := N₀.toMinorModel
    root_mem := by
      intro i
      have heq : PR.finish i = E (r' ⟨i.1,hYY' i.2⟩) := by
        apply Subtype.ext
        change P.finish i = (r' ⟨i.1,hYY' i.2⟩ : S.right).1
        exact congrArg (fun z : S.right => (z : V)) (congrFun hrootEq.symm i)
      rw [heq]
      exact N₀.root_mem i
  }
  let J : Set R := {z | (z : V) ∈ S.right}
  have hNsubset (i : ↥(Y : Set W)) : N'.branch i ⊆ J := by
    intro z hz
    change z ∈ N₀.branch i at hz
    change z ∈ E '' M'.branch i at hz
    rcases hz with ⟨a, ha, rfl⟩
    exact a.property
  have hcleanR (i : ↥(Y : Set W)) (z : R)
      (hz : z ∈ pathVertexSet (LR.path i)) (hzJ : z ∈ J) :
      z = PR.finish i := by
    have hzG : (z : V) ∈ pathVertexSet (L.path i) :=
      (Linkedness.IndexedLinkage.mem_induce_pathVertexSet_iff L R hpathR i z).mp hz
    apply Subtype.ext
    exact hclean i (z : V) hzG hzJ
  exact ⟨rootedMinor_extendAlongCleanLinkage N' LR J hNsubset hcleanR⟩

end HadwigerLean.RootedDensity
