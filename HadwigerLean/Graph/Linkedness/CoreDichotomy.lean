import HadwigerLean.Graph.Linkedness.CoreFarLinked
import HadwigerLean.Graph.Linkedness.CoreTransfer
import Mathlib.Tactic

namespace HadwigerLean
namespace Linkedness

/-- A core linked at every small arrival set either links all prescribed
roots, or yields a proper linked far shore of order below the root count. -/
theorem rootedLinked_or_rigid_shore_of_rooted_core
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {r k : ℕ}
    (root : Fin r → V) (hroot : Function.Injective root)
    (J : Finset V) (hJ : r ≤ J.card) (hr : r ≤ 2 * k)
    (hcore : ∀ Y : Finset (J : Set V), Y.card ≤ 2 * k →
      RootedLinked (G.induce (J : Set V)) Y) :
    RootedLinked G (Finset.univ.image root) ∨
      ∃ S : VertexSeparation G,
        (∀ i, root i ∈ S.left) ∧
        S.strictRight.Nonempty ∧
        S.separatorFinset.card < r ∧
        RootedLinked (G.induce S.right) (separationBoundaryFinset S) := by
  classical
  let R : Finset V := Finset.univ.image root
  rcases root_set_linkage_or_separator G root hroot J with
    ⟨P,L,hstart,hfinish⟩ | ⟨Q,hQsmall,hABQ⟩
  · obtain ⟨P',L',hstart',hfinish',hfirst',_⟩ :=
      IndexedLinkage.trim_to_first_hit L J hfinish
    left
    have hrooted : RootedLinked G (Finset.univ.image P'.start) :=
      rootedLinked_of_trimmed_fan_to_core P' L' J hfinish' hfirst'
        (fun Y hY => hcore Y (hY.trans hr))
    have hset : Finset.univ.image P'.start = Finset.univ.image root := by
      apply Finset.image_congr
      intro i hi
      exact (hstart' i).trans (hstart i)
    exact hset ▸ hrooted
  · obtain ⟨Q0,n,P,L,hQ0,hAB,hcard,hmin⟩ :=
      SetMenger.finite_set_menger G R J
    have hn : n < r := by
      have hminQ := hmin Q hABQ
      omega
    let S := SetMenger.reachableSeparation G R Q0
    have hJoutside : ∃ j ∈ J, j ∉ Q0 := by
      by_contra h
      push Not at h
      have hsub : J ⊆ Q0 := by
        intro j hj
        exact h j hj
      have hc := Finset.card_le_card hsub
      omega
    obtain ⟨j,hj,hjQ⟩ := hJoutside
    have hJright : ∀ x ∈ J, x ∈ S.right := by
      intro x hx
      exact SetMenger.reachableSeparation_right_of_ABSeparator G R Q0 J hQ0 x hx
    have hhit : ∀ i, ∃ x ∈ S.separatorFinset,
        x ∈ pathVertexSet (L.path i) := by
      intro i
      obtain ⟨x,hxQ,hxP⟩ := hQ0 (P.start i) (hAB.1 i)
        (P.finish i) (hAB.2 i) (L.path i)
      exact ⟨x,SetMenger.reachableSeparation_separatorFinset G R Q0 ▸ hxQ,hxP⟩
    have hScard : S.separatorFinset.card = n := by
      simpa [S, SetMenger.reachableSeparation_separatorFinset] using hcard
    obtain ⟨C,F,hstarts,hfinish,hpathRight,hfirst⟩ :=
      boundary_core_fan_in_right S J hJright P L hAB.2 hhit hScard
    have hfarLinked : RootedLinked (G.induce S.right)
        (separationBoundaryFinset S) :=
      rootedLinked_right_of_boundary_core_fan S J hJright k n
        (by omega) hcore C F hstarts hfinish hpathRight hfirst
    right
    refine ⟨S,?_,?_,?_,hfarLinked⟩
    · intro i
      exact SetMenger.reachableSeparation_left_of_mem G R Q0
        (root i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    · exact ⟨j,SetMenger.reachableSeparation_strictRight_of_ABSeparator
        G R Q0 J hQ0 j hj hjQ⟩
    · omega

end Linkedness
end HadwigerLean
