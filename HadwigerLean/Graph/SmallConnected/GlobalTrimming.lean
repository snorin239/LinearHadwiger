import HadwigerLean.Graph.SmallConnected.LocalIncidence
import HadwigerLean.Graph.SmallConnected.InducedAdj
import Mathlib.Tactic

/-!
# Degree sum and the Section 8 trimming inequality
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Degrees in a vertex set count its internal edges twice and its
boundary edges once. -/
theorem sum_degrees_on_eq_twice_inside_add_cross
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (∑ v ∈ S, G.degree v) =
      2 * edgeCount (G.induce (S : Set V)) +
        ∑ w ∈ Sᶜ, (G.neighborFinset w ∩ S).card := by
  classical
  have hpoint (v : V) : G.degree v =
      (G.neighborFinset v ∩ S).card +
        (G.neighborFinset v ∩ Sᶜ).card := by
    have h := Finset.card_inter_add_card_sdiff (G.neighborFinset v) S
    have heq : G.neighborFinset v \ S = G.neighborFinset v ∩ Sᶜ := by
      ext w
      simp
    rw [heq, G.card_neighborFinset_eq_degree] at h
    exact h.symm
  calc
    (∑ v ∈ S, G.degree v) =
        ∑ v ∈ S, ((G.neighborFinset v ∩ S).card +
          (G.neighborFinset v ∩ Sᶜ).card) := by
            apply Finset.sum_congr rfl
            intro v hv
            exact hpoint v
    _ = (∑ v ∈ S, (G.neighborFinset v ∩ S).card) +
          (∑ v ∈ S, (G.neighborFinset v ∩ Sᶜ).card) :=
            Finset.sum_add_distrib
    _ = 2 * edgeCount (G.induce (S : Set V)) +
          ∑ w ∈ Sᶜ, (G.neighborFinset w ∩ S).card := by
            rw [inside_incidence_twice_edges,
              cross_incidence_symm]

/-- The original boundary form (8.2) of the trimming lemma. -/
theorem exists_trimmed_of_inside_cross_surplus
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (r δ : ℝ) (hr : 2 < r) (hδ : 0 < δ)
    (hsurplus : (r - 2) *
        (edgeCount (G.induce (S : Set V)) : ℝ) >
      (r - 1) * δ * (S.card : ℝ) +
        ∑ w ∈ Sᶜ, ((G.neighborFinset w ∩ S).card : ℝ)) :
    ∃ T : Finset V, T.Nonempty ∧ T ⊆ S ∧
      (∀ v ∈ T, δ ≤ ((G.neighborFinset v ∩ T).card : ℝ)) ∧
      (∀ v ∈ T, (G.degree v : ℝ) ≤
        r * ((G.neighborFinset v ∩ T).card : ℝ)) := by
  classical
  apply exists_trimmed_induced_finset_of_edge_score G S r δ hr hδ
  have hnat := sum_degrees_on_eq_twice_inside_add_cross G S
  have hreal : (∑ v ∈ S, (G.degree v : ℝ)) =
      2 * (edgeCount (G.induce (S : Set V)) : ℝ) +
        ∑ w ∈ Sᶜ, ((G.neighborFinset w ∩ S).card : ℝ) := by
    exact_mod_cast hnat
  linarith

end HadwigerLean
