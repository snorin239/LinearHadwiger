import HadwigerLean.Graph.CliqueDensity.Reduction
import Mathlib.Tactic

/-!
# Deleting surplus edges to achieve an exact integral density
-/

namespace HadwigerLean

universe u

theorem exists_spanning_subgraph_exact_edgeCount
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (m : ℕ) (hm : m ≤ edgeCount G) :
    ∃ H : SimpleGraph V, H ≤ G ∧ edgeCount H = m := by
  classical
  obtain ⟨E, hEG, hEcard⟩ :=
    Finset.exists_subset_card_eq
      (s := G.edgeFinset) (n := m)
      (by simpa only [edgeCount_eq_card_edgeFinset] using hm)
  let H := G.deleteEdges ((G.edgeFinset \ E : Finset (Sym2 V)) : Set (Sym2 V))
  have hHedges : H.edgeFinset = E := by
    change (G.deleteEdges ((G.edgeFinset \ E : Finset (Sym2 V)) : Set (Sym2 V))).edgeFinset = E
    rw [G.edgeFinset_deleteEdges]
    exact Finset.sdiff_sdiff_eq_self hEG
  refine ⟨H, G.deleteEdges_le _, ?_⟩
  rw [edgeCount_eq_card_edgeFinset, hHedges]
  exact hEcard

end HadwigerLean
