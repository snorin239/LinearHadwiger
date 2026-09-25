import HadwigerLean.Graph.Linkedness.Massed

/-!
# Full indexed linkages avoid all other designated terminals
-/

namespace HadwigerLean
namespace Linkedness

/-- A vertex-disjoint linkage uses each designated terminal only on the
path for that terminal's pair. -/
theorem IndexedLinkage.interiorsAvoid_terminal_cover
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {ι : Type*} [Fintype ι]
    {P : IndexedPairs ι V} (L : IndexedLinkage G P)
    (Y : Finset V) (hY : Y ⊆ terminalFinset P) :
    InteriorsAvoid L Y := by
  intro i v hv hvY
  have hvTerm : v ∈ terminalFinset P := hY hvY
  rcases (mem_terminalFinset P v).mp hvTerm with ⟨j,hj⟩ | ⟨j,hj⟩
  · by_cases hij : i = j
    · subst j
      exact Or.inl hj.symm
    · have hvj : v ∈ pathVertexSet (L.path j) := by
        rw [← hj]
        exact pathVertexSet.start_mem (L.path j)
      exact False.elim ((Set.disjoint_left.mp (L.disjoint hij)) hv hvj)
  · by_cases hij : i = j
    · subst j
      exact Or.inr hj.symm
    · have hvj : v ∈ pathVertexSet (L.path j) := by
        rw [← hj]
        exact pathVertexSet.finish_mem (L.path j)
      exact False.elim ((Set.disjoint_left.mp (L.disjoint hij)) hv hvj)

end Linkedness
end HadwigerLean
