import HadwigerLean.Graph.RootedDensity.UniversalRigidFanClean
import HadwigerLean.Graph.Linkedness.FirstHit
import Mathlib.Tactic

/-!
# Full fan into a universal rigid shore

A full disjoint fan from prescribed roots to the far side can be
trimmed at its first far-side hit. That hit lies in the adhesion, and
the resulting paths are clean for the arbitrary-target shore model.
-/

namespace HadwigerLean.RootedDensity

universe u v

theorem rootedMinor_of_universal_right_and_full_fan
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) (S : VertexSeparation G)
    (H : SimpleGraph W)
    (huni : UniversalAtRightShore H S)
    (hsize : (Linkedness.separationBoundaryFinset S).card ≤ Fintype.card W)
    (Y : Finset W)
    (P : IndexedPairs ↥(Y : Set W) V)
    (L : IndexedLinkage G P)
    (hstartLeft : ∀ i, P.start i ∈ S.left)
    (hfinishRight : ∀ i, P.finish i ∈ S.right) :
    Nonempty (RootedMinorModel (H.induce (Y : Set W)) G P.start) := by
  classical
  letI : Fintype S.right := Fintype.ofFinite S.right
  let J : Finset V := S.right.toFinset
  have hfinishJ : ∀ i, P.finish i ∈ J := by
    intro i
    simpa [J] using hfinishRight i
  obtain ⟨P',L',hstart',hfinish',hfirst',_⟩ :=
    Linkedness.IndexedLinkage.trim_to_first_hit L J hfinishJ
  have hSep (i : ↥(Y : Set W)) : P'.finish i ∈ S.separator := by
    have hBoundary : ∀ x ∈
        (L'.path i : G.Walk (P'.start i) (P'.finish i)).support,
        x ∈ S.separator → x = P'.finish i := by
      intro x hx hxSep
      exact hfirst' i x hx (by simpa [J] using hxSep.2)
    have hleft :=
      S.path_support_subset_left_of_boundary_only_at_finish
        (L'.path i : G.Walk (P'.start i) (P'.finish i))
        (L'.path i).property
        (hstart' i ▸ hstartLeft i) hBoundary
    exact ⟨hleft (P'.finish i)
        (L'.path i : G.Walk (P'.start i) (P'.finish i)).end_mem_support,
      by simpa [J] using hfinish' i⟩
  have hclean : ∀ i x, x ∈ pathVertexSet (L'.path i) →
      x ∈ S.right → x = P'.finish i := by
    intro i x hx hxR
    exact hfirst' i x hx (by simpa [J] using hxR)
  have hmodel := rootedMinor_of_universal_right_and_clean_fan
    G S H huni hsize Y P' L' hSep hclean
  have hstartEq : P'.start = P.start := by
    funext i
    exact hstart' i
  rw [hstartEq] at hmodel
  exact hmodel

end HadwigerLean.RootedDensity
