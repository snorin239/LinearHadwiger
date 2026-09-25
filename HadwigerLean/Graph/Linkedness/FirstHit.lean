import HadwigerLean.Graph.IndexedLinkage
import Mathlib.Tactic

/-!
# Trim a family of paths at their first visits to a set
-/

namespace HadwigerLean
namespace Linkedness

structure FirstHit {V : Type*} {G : SimpleGraph V} {s t : V}
    (p : G.Path s t) (J : Finset V) where
  finish : V
  finish_mem : finish ∈ J
  path : G.Path s finish
  path_subset : pathVertexSet path ⊆ pathVertexSet p
  unique_hit : ∀ x ∈ pathVertexSet path, x ∈ J → x = finish

/-- The prefix ending at the first visit to a set. -/
theorem FirstHit.exists_of_finish_mem
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {s t : V}
    (p : G.Path s t) (J : Finset V) (ht : t ∈ J) :
    Nonempty (FirstHit p J) := by
  classical
  let w : G.Walk s t := p
  have hhit : {x ∈ J | x ∈ w.support}.Nonempty := by
    exact ⟨t, Finset.mem_filter.mpr ⟨ht, w.end_mem_support⟩⟩
  obtain ⟨u, huJ, huW, hfirst⟩ :=
    w.exists_mem_support_forall_mem_support_imp_eq J hhit
  let q : G.Path s u := ⟨w.takeUntil u huW, p.property.takeUntil huW⟩
  exact ⟨{
    finish := u
    finish_mem := huJ
    path := q
    path_subset := by
      intro x hx
      exact w.support_takeUntil_subset_support huW hx
    unique_hit := by
      intro x hx hxJ
      exact hfirst x hxJ hx
  }⟩

/-- Trimming each path of a disjoint family preserves disjointness and
ensures that every trimmed path meets the target only at its finish. -/
theorem IndexedLinkage.trim_to_first_hit
    {ι V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {P : IndexedPairs ι V}
    (L : IndexedLinkage G P) (J : Finset V)
    (hfinish : ∀ i, P.finish i ∈ J) :
    ∃ (P' : IndexedPairs ι V) (L' : IndexedLinkage G P'),
      (∀ i, P'.start i = P.start i) ∧
      (∀ i, P'.finish i ∈ J) ∧
      (∀ i x, x ∈ pathVertexSet (L'.path i) → x ∈ J → x = P'.finish i) ∧
      (∀ i, pathVertexSet (L'.path i) ⊆ pathVertexSet (L.path i)) := by
  classical
  let F (i : ι) : FirstHit (L.path i) J :=
    Classical.choice (FirstHit.exists_of_finish_mem (L.path i) J (hfinish i))
  let P' : IndexedPairs ι V :=
    ⟨P.start, fun i => (F i).finish⟩
  let L' : IndexedLinkage G P' := {
    path := fun i => (F i).path
    disjoint := by
      intro i j hij
      exact Set.disjoint_of_subset (F i).path_subset (F j).path_subset (L.disjoint hij)
  }
  exact ⟨P', L', (fun _ => rfl), (fun i => (F i).finish_mem),
    (fun i x hx hxJ => (F i).unique_hit x hx hxJ),
    (fun i => (F i).path_subset)⟩

end Linkedness
end HadwigerLean
