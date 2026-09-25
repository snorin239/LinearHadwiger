import HadwigerLean.Graph.Linkedness.CoreFarFan
import HadwigerLean.Graph.Linkedness.NestedRootedReverse
import Mathlib.Tactic

namespace HadwigerLean
namespace Linkedness

/-- A boundary-to-core fan contained in the far shore transfers the
core's rooted linkedness to the entire adhesion. -/
theorem rootedLinked_right_of_boundary_core_fan
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    (J : Finset V) (hJright : ∀ x ∈ J, x ∈ S.right)
    (k q : ℕ) (hq : q ≤ 2 * k)
    (hcore : ∀ Y : Finset (J : Set V), Y.card ≤ 2 * k →
      RootedLinked (G.induce (J : Set V)) Y)
    (C : IndexedPairs (Fin q) V) (F : IndexedLinkage G C)
    (hstarts : Finset.univ.image C.start = S.separatorFinset)
    (hfinish : ∀ i, C.finish i ∈ J)
    (hright : ∀ i x, x ∈ pathVertexSet (F.path i) → x ∈ S.right)
    (hfirst : ∀ i x, x ∈ pathVertexSet (F.path i) → x ∈ J → x = C.finish i) :
    RootedLinked (G.induce S.right) (separationBoundaryFinset S) := by
  classical
  let R : Set V := S.right
  let T : Finset R := @Finset.subtype V R (Classical.decPred R) J
  let C' : IndexedPairs (Fin q) R :=
    ⟨(fun i => ⟨C.start i, hright i _ (pathVertexSet.start_mem (F.path i))⟩),
     (fun i => ⟨C.finish i, hright i _ (pathVertexSet.finish_mem (F.path i))⟩)⟩
  let F' : IndexedLinkage (G.induce R) C' := IndexedLinkage.induce F R hright
  have hstartR : Finset.univ.image C'.start = separationBoundaryFinset S := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hx
      have hqmem : (x : V) ∈ S.separatorFinset := by
        rw [← hstarts]
        exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _, congrArg Subtype.val hi⟩
      exact (mem_separationBoundaryFinset S x).2 ((S.mem_separatorFinset x).mp hqmem).1
    · intro hx
      have hqmem : (x : V) ∈ S.separatorFinset :=
        (S.mem_separatorFinset x).2 ⟨(mem_separationBoundaryFinset S x).mp hx, x.property⟩
      rw [← hstarts] at hqmem
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hqmem
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,Subtype.ext hi⟩
  have hfinishT : ∀ i, C'.finish i ∈ T := by
    intro i
    exact (Finset.mem_subtype).2 (hfinish i)
  have hfirstT : ∀ i x, x ∈ pathVertexSet (F'.path i) →
      x ∈ T → x = C'.finish i := by
    intro i x hx hxT
    have hxorig : (x : V) ∈ pathVertexSet (F.path i) :=
      (IndexedLinkage.mem_induce_pathVertexSet_iff F R hright i x).mp hx
    have hxJ : (x : V) ∈ J := (Finset.mem_subtype).1 hxT
    exact Subtype.ext (hfirst i x hxorig hxJ)
  have hTcore : ∀ Y : Finset (T : Set R), Y.card ≤ 2 * k →
      RootedLinked ((G.induce R).induce (T : Set R)) Y :=
    rootedLinked_nested_of_ambient G R J hJright k hcore
  have hrooted : RootedLinked (G.induce R) (Finset.univ.image C'.start) :=
    rootedLinked_of_trimmed_fan_to_core C' F' T hfinishT hfirstT
      (fun Y hY => hTcore Y (hY.trans hq))
  simpa only [R, hstartR] using hrooted

end Linkedness
end HadwigerLean
