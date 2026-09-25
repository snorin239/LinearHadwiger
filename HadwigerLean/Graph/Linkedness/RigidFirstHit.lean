import HadwigerLean.Graph.Linkedness.CoreFarFan

namespace HadwigerLean
namespace Linkedness

/-- The first visit to the far side of a separation lies in its adhesion. -/
theorem FirstHit.finish_mem_separator_of_right
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : VertexSeparation G) [Fintype S.right]
    {s t : V} (p : G.Path s t) (hs : s ∈ S.left)
    (F : FirstHit p S.right.toFinset) :
    F.finish ∈ S.separator := by
  classical
  have hboundary : ∀ x ∈ (F.path : G.Walk s F.finish).support,
      x ∈ S.separator → x = F.finish := by
    intro x hx hxSep
    exact F.unique_hit x hx (by simpa using hxSep.2)
  have hleft := S.path_support_subset_left_of_boundary_only_at_finish
    (F.path : G.Walk s F.finish) F.path.property hs hboundary
  exact ⟨hleft F.finish (F.path : G.Walk s F.finish).end_mem_support,
    by simpa using F.finish_mem⟩

/-- Trim a path to its first far-side vertex; the endpoint is on the adhesion. -/
theorem exists_first_right_hit_in_separator
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : VertexSeparation G) [Fintype S.right]
    {s t : V} (p : G.Path s t) (hs : s ∈ S.left)
    (ht : t ∈ S.right) :
    ∃ F : FirstHit p S.right.toFinset, F.finish ∈ S.separator := by
  classical
  obtain ⟨F⟩ := FirstHit.exists_of_finish_mem p S.right.toFinset (by simpa using ht)
  exact ⟨F,F.finish_mem_separator_of_right S p hs⟩

end Linkedness
end HadwigerLean
