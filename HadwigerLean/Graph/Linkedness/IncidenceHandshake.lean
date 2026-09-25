import HadwigerLean.Graph.Linkedness.Massed
import Mathlib.Tactic

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

private def exteriorGraph (G : SimpleGraph V) (X : Finset V) : SimpleGraph V :=
  G.deleteEdges (X.sym2 : Set (Sym2 V))

private theorem exteriorGraph_adj (G : SimpleGraph V) (X : Finset V) (v w : V) :
    (exteriorGraph G X).Adj v w ↔ G.Adj v w ∧ (v ∉ X ∨ w ∉ X) := by
  simp [exteriorGraph, SimpleGraph.deleteEdges_adj]
  tauto

end Linkedness
end HadwigerLean

namespace HadwigerLean
namespace Linkedness

private theorem exteriorGraph_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V)
    [DecidableRel (exteriorGraph G X).Adj] (v : V) :
    (exteriorGraph G X).neighborFinset v =
      if v ∈ X then G.neighborFinset v \ X else G.neighborFinset v := by
  classical
  ext w
  rw [SimpleGraph.mem_neighborFinset, exteriorGraph_adj]
  by_cases hv : v ∈ X
  · simp [hv, SimpleGraph.mem_neighborFinset]
  · simp [hv, SimpleGraph.mem_neighborFinset]

private theorem exteriorGraph_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V)
    [DecidableRel (exteriorGraph G X).Adj] (v : V) :
    (exteriorGraph G X).degree v =
      if v ∈ X then (G.neighborFinset v \ X).card else G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    exteriorGraph_neighborFinset]
  split_ifs <;> rfl

private theorem incident_iff_not_internal
    {V : Type*} [Fintype V] [DecidableEq V] (X : Finset V) (e : Sym2 V) :
    (∃ v ∈ Xᶜ, v ∈ e) ↔ e ∉ X.sym2 := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp [Sym2.mem_iff]
    constructor
    · rintro ⟨z, hz, rfl | rfl⟩
      · exact fun hu => (hz hu).elim
      · exact fun _ => hz
    · intro h
      by_cases hu : u ∈ X
      · exact ⟨v, h hu, by simp⟩
      · exact ⟨u, hu, by simp⟩

private theorem exteriorGraph_incidenceCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) :
    edgeIncidenceSetCount G (X : Set V)ᶜ = edgeCount (exteriorGraph G X) := by
  classical
  rw [show edgeIncidenceSetCount G (X : Set V)ᶜ = edgeIncidenceCount G Xᶜ by
    simpa using incidenceSetCount_eq_finsetCount G Xᶜ]
  rw [edgeCount_eq_card_edgeFinset]
  unfold edgeIncidenceCount
  congr 1
  ext e
  simp [exteriorGraph, SimpleGraph.mem_edgeFinset]
  intro _
  constructor
  · rintro ⟨v, hvX, hve⟩
    exact ⟨v, hve, hvX⟩
  · rintro ⟨v, hve, hvX⟩
    exact ⟨v, hvX, hve⟩

end Linkedness
end HadwigerLean




namespace HadwigerLean
namespace Linkedness

/-- Edges meeting the outside of `X` are counted twice by degrees of outside
vertices and by outward neighbors of the roots. -/
theorem edgeIncidenceSetCount_handshake
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) :
    2 * edgeIncidenceSetCount G (X : Set V)ᶜ =
      (∑ v ∈ Xᶜ, G.degree v) +
        (∑ x ∈ X, (G.neighborFinset x \ X).card) := by
  classical
  let H := exteriorGraph G X
  calc
    2 * edgeIncidenceSetCount G (X : Set V)ᶜ = 2 * edgeCount H := by
      rw [exteriorGraph_incidenceCount]
    _ = ∑ v : V, H.degree v := (sum_degree_eq_two_edgeCount H).symm
    _ = (∑ v ∈ Xᶜ, H.degree v) + (∑ v ∈ X, H.degree v) := by
      simpa only [Finset.sum_compl_add_sum]
    _ = (∑ v ∈ Xᶜ, G.degree v) +
          (∑ x ∈ X, (G.neighborFinset x \ X).card) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro v hv
        rw [exteriorGraph_degree]
        simp [Finset.mem_compl.mp hv]
      · apply Finset.sum_congr rfl
        intro v hv
        rw [exteriorGraph_degree]
        simp [hv]

end Linkedness
end HadwigerLean


namespace HadwigerLean
namespace Linkedness

/-- In an edge-tight massed graph, outward root degree at least two forces
some outside vertex to have degree below twice the mass parameter. -/
theorem exists_outside_degree_lt_twice_of_tight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (lam : ℕ)
    (hX : 2 ≤ X.card)
    (htight : edgeIncidenceSetCount G (X : Set V)ᶜ =
      lam * (Xᶜ).card + 1)
    (hroot : ∀ x ∈ X, 2 ≤ (G.neighborFinset x \ X).card) :
    ∃ v ∈ Xᶜ, G.degree v < 2 * lam := by
  by_contra hnone
  push Not at hnone
  have hout : ∀ v ∈ Xᶜ, 2 * lam ≤ G.degree v := by
    intro v hv
    exact hnone v hv
  have hsumout : (∑ v ∈ Xᶜ, 2 * lam) ≤
      (∑ v ∈ Xᶜ, G.degree v) := by
    exact Finset.sum_le_sum (fun v hv => hout v hv)
  have hsumroot : (∑ x ∈ X, 2) ≤
      (∑ x ∈ X, (G.neighborFinset x \ X).card) := by
    exact Finset.sum_le_sum (fun x hx => hroot x hx)
  have hh := edgeIncidenceSetCount_handshake G X
  rw [htight] at hh
  simp only [Finset.sum_const, nsmul_eq_mul] at hsumout hsumroot
  nlinarith

end Linkedness
end HadwigerLean
