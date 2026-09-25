import HadwigerLean.Graph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Real.Basic

/-!
# Finite edge counts and density

The density used in the proof is the number of edges divided by the number
of vertices.  Edge incidence counts record edges with at least one endpoint
in a selected vertex set, as in the massed-pair argument.
-/

namespace HadwigerLean

universe u

variable {V : Type u} [Fintype V]

/-- Number of edges of a finite simple graph. -/
noncomputable def edgeCount (G : SimpleGraph V) : ℕ := Nat.card G.edgeSet

/-- Number of edges touching at least one vertex of `S`. -/
noncomputable def edgeIncidenceCount (G : SimpleGraph V) (S : Finset V) : ℕ := by
  classical
  exact (G.edgeFinset.filter fun e => ∃ v ∈ S, v ∈ e).card

/-- The edge-per-vertex density, with zero density for the empty graph. -/
noncomputable def edgeDensity (G : SimpleGraph V) : ℝ :=
  (edgeCount G : ℝ) / (Fintype.card V : ℝ)

theorem edgeCount_eq_card_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeCount G = G.edgeFinset.card := by
  classical
  simpa [edgeCount, Nat.card_eq_fintype_card] using G.edgeFinset_card.symm

theorem edgeIncidenceCount_empty (G : SimpleGraph V) :
    edgeIncidenceCount G ∅ = 0 := by
  classical
  simp [edgeIncidenceCount]

theorem edgeIncidenceCount_mono (G : SimpleGraph V)
    {S T : Finset V} (hST : S ⊆ T) :
    edgeIncidenceCount G S ≤ edgeIncidenceCount G T := by
  classical
  unfold edgeIncidenceCount
  apply Finset.card_le_card
  intro e he
  simp only [Finset.mem_filter] at he ⊢
  obtain ⟨hEdge, v, hv, hve⟩ := he
  exact ⟨hEdge, v, hST hv, hve⟩

theorem edgeIncidenceCount_le_edgeCount (G : SimpleGraph V) (S : Finset V) :
    edgeIncidenceCount G S ≤ edgeCount G := by
  classical
  unfold edgeIncidenceCount
  rw [edgeCount_eq_card_edgeFinset]
  exact Finset.card_filter_le _ _

/-- The handshaking identity in the local edge-count notation. -/
theorem sum_degree_eq_two_edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v, G.degree v) = 2 * edgeCount G := by
  classical
  rw [edgeCount_eq_card_edgeFinset]
  exact G.sum_degrees_eq_twice_card_edges

theorem edgeDensity_nonneg (G : SimpleGraph V) : 0 ≤ edgeDensity G := by
  unfold edgeDensity
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end HadwigerLean
