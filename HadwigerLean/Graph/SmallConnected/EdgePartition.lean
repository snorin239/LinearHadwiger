import HadwigerLean.Graph.SmallConnected.InducedAdj
import HadwigerLean.Graph.ContractionEdges
import Mathlib.Tactic

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The edges split into those inside a finite set, those outside it, and
crossing edges counted from the outside. -/
theorem edgeCount_eq_inside_add_outside_add_cross
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (edgeCount G : ℝ) =
      (edgeCount (G.induce (S : Set V)) : ℝ) +
      (edgeCount (G.induce ((Sᶜ : Finset V) : Set V)) : ℝ) +
      ∑ w ∈ Sᶜ, ((G.neighborFinset w ∩ S).card : ℝ) := by
  classical
  have hdegree (v : V) : (G.degree v : ℝ) =
      ((G.neighborFinset v ∩ S).card : ℝ) +
      ((G.neighborFinset v ∩ Sᶜ).card : ℝ) := by
    have hcard := Finset.card_sdiff_add_card_inter (G.neighborFinset v) S
    rw [Finset.sdiff_eq_inter_compl, G.card_neighborFinset_eq_degree] at hcard
    have hnat : G.degree v =
        (G.neighborFinset v ∩ S).card +
        (G.neighborFinset v ∩ Sᶜ).card := by omega
    exact_mod_cast hnat
  have hinner (T : Finset V) :
      (∑ v ∈ T, ((G.neighborFinset v ∩ T).card : ℝ)) =
        2 * (edgeCount (G.induce (T : Set V)) : ℝ) := by
    have h := inducedEdgeWeight_eq_edgeCount G T
    simp only [inducedEdgeWeight, internalNeighborWeight_eq_card] at h
    linarith
  have hcross :
      (∑ v ∈ S, ((G.neighborFinset v ∩ Sᶜ).card : ℝ)) =
      ∑ w ∈ Sᶜ, ((G.neighborFinset w ∩ S).card : ℝ) := by
    simp_rw [← internalNeighborWeight_eq_card]
    simp only [internalNeighborWeight]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w hw
    apply Finset.sum_congr rfl
    intro v hv
    simp [G.adj_comm]
  have hsplit :
      (∑ v : V, (G.degree v : ℝ)) =
        (∑ v ∈ S, (G.degree v : ℝ)) +
          (∑ v ∈ Sᶜ, (G.degree v : ℝ)) := by
    have hdisj : Disjoint S Sᶜ := by
      apply Finset.disjoint_left.mpr
      intro x hx hxc
      exact (Finset.mem_compl.mp hxc) hx
    have hunion : S ∪ Sᶜ = (Finset.univ : Finset V) := Finset.union_compl S
    rw [← hunion]
    exact Finset.sum_union hdisj
  have hhand : (∑ v : V, (G.degree v : ℝ)) =
      2 * (edgeCount G : ℝ) := by
    exact_mod_cast (by simpa only [edgeCount_eq_card_edgeFinset] using
      G.sum_degrees_eq_twice_card_edges)
  rw [hsplit] at hhand
  simp_rw [hdegree] at hhand
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hhand
  linarith [hinner S, hinner Sᶜ, hcross]

end HadwigerLean