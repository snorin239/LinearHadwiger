import HadwigerLean.Graph.Linkedness.RigidFirstHit
import HadwigerLean.Graph.Linkedness.RootedMonotonicity
import HadwigerLean.Graph.Linkedness.CoreFanFinal
import HadwigerLean.Graph.Linkedness.RootedLinkedIso

namespace HadwigerLean
namespace Linkedness

/-- A full fan from the roots into a linked rigid far side links the roots. -/
theorem rootedLinked_of_full_fan_to_rigid_far
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : VertexSeparation G) [Fintype S.right]
    {r : ℕ} (P : IndexedPairs (Fin r) V) (F : IndexedLinkage G P)
    (hstart : ∀ i, P.start i ∈ S.left)
    (hfinish : ∀ i, P.finish i ∈ S.right)
    (hfar : RootedLinked (G.induce S.right) (separationBoundaryFinset S)) :
    RootedLinked G (Finset.univ.image P.start) := by
  classical
  let J : Finset V := S.right.toFinset
  have hfinishJ : ∀ i, P.finish i ∈ J := by
    intro i
    simpa [J] using hfinish i
  obtain ⟨P',F',hstart',hfinish',hfirst',_⟩ :=
    IndexedLinkage.trim_to_first_hit F J hfinishJ
  have hArrivalSep (i : Fin r) : P'.finish i ∈ S.separator := by
    have hboundary : ∀ x ∈ (F'.path i : G.Walk (P'.start i) (P'.finish i)).support,
        x ∈ S.separator → x = P'.finish i := by
      intro x hx hxSep
      exact hfirst' i x hx (by simpa [J] using hxSep.2)
    have hleft := S.path_support_subset_left_of_boundary_only_at_finish
      (F'.path i : G.Walk (P'.start i) (P'.finish i))
      (F'.path i).property (hstart' i ▸ hstart i) hboundary
    exact ⟨hleft (P'.finish i)
        (F'.path i : G.Walk (P'.start i) (P'.finish i)).end_mem_support,
      by simpa [J] using hfinish' i⟩
  have hJeq : (J : Set V) = S.right := by
    ext x
    simp [J]
  letI : Fintype (J : Set V) := Fintype.ofFinite (J : Set V)
  let e : (G.induce S.right) ≃g G.induce (J : Set V) := {
    toEquiv := Equiv.setCongr hJeq.symm
    map_rel_iff' := by intro a b; rfl
  }
  let Z : Finset (J : Set V) := (separationBoundaryFinset S).image e
  have hiso : RootedLinked (G.induce (J : Set V)) Z :=
    rootedLinked_of_iso e (separationBoundaryFinset S) Z
      (by intro v; simp [Z]) hfar
  have hsubset : fanArrivalFinset P' J hfinish' ⊆ Z := by
    intro u hu
    change u ∈ Finset.univ.image (fun i : Fin r =>
      (⟨P'.finish i, hfinish' i⟩ : (J : Set V))) at hu
    obtain ⟨i,_,hueq⟩ := Finset.mem_image.mp hu
    let v : S.right := ⟨P'.finish i, (hArrivalSep i).2⟩
    have hvZ : v ∈ separationBoundaryFinset S :=
      (mem_separationBoundaryFinset S v).mpr (hArrivalSep i).1
    have hev : e v = u := by
      apply Subtype.ext
      exact congrArg Subtype.val hueq
    exact Finset.mem_image.mpr ⟨v,hvZ,hev⟩
  have hcore : RootedLinked (G.induce (J : Set V))
      (fanArrivalFinset P' J hfinish') := hiso.of_subset hsubset
  have hrooted := rootedLinked_of_trimmed_fan_to_arrivals
    P' F' J hfinish' hfirst' hcore
  have hset : Finset.univ.image P'.start = Finset.univ.image P.start := by
    apply Finset.image_congr
    intro i hi
    exact hstart' i
  exact hset ▸ hrooted

end Linkedness
end HadwigerLean
