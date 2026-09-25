import HadwigerLean.Graph.RootedDensity.TwoEdgeAttach
import HadwigerLean.Graph.RootedDensity.SamplingAvoid
import Mathlib.Tactic

/-! Counting common-neighbor candidates outside a sample and its roots. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- Two minimum-degree bounds force enough common neighbors after deleting
an occupied sample and a prescribed root set. -/
theorem common_neighbor_candidates_of_min_degree
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X S : Finset V) (d : ℝ) (r : ℕ)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hbudget : (Fintype.card V : ℝ) + (S.card : ℝ) +
      (X.card : ℝ) + (r : ℝ) ≤ 2 * d) :
    ∀ x ∈ X, ∀ y ∈ S,
      r ≤ ((G.neighborFinset x ∩ G.neighborFinset y) \ (S ∪ X)).card := by
  intro x hx y hy
  let A := G.neighborFinset x
  let B := G.neighborFinset y
  let U := S ∪ X
  let C := (A ∩ B) \ U
  have hAB : A.card + B.card = (A ∪ B).card + (A ∩ B).card :=
    (Finset.card_union_add_card_inter A B).symm
  have hUniv : (A ∪ B).card ≤ Fintype.card V :=
    Finset.card_le_univ _
  have hCut : (A ∩ B).card ≤ C.card + U.card := by
    exact Finset.card_le_card_sdiff_add_card
  have hU : U.card ≤ S.card + X.card := Finset.card_union_le _ _
  have hnat : A.card + B.card ≤ Fintype.card V + S.card + X.card + C.card := by
    omega
  have hreal : (G.degree x : ℝ) + (G.degree y : ℝ) ≤
      (Fintype.card V : ℝ) + (S.card : ℝ) + (X.card : ℝ) + (C.card : ℝ) := by
    have hcast : ((A.card + B.card : ℕ) : ℝ) ≤
        ((Fintype.card V + S.card + X.card + C.card : ℕ) : ℝ) := by
      exact_mod_cast hnat
    simpa [A, B, SimpleGraph.card_neighborFinset_eq_degree, Nat.cast_add] using hcast
  have hr : (r : ℝ) ≤ (C.card : ℝ) := by
    linarith [hmin x, hmin y]
  exact_mod_cast hr

/-- A sampled dense minor in the complement of the roots is universal
whenever a degree-overlap budget supplies common-neighbor proxies. -/
theorem universalAt_of_sampled_common_neighbors
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (c : ℝ) (hc : 0 ≤ c) (hforces : DensityForcesMinor.{u,v} H c)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V)
    (hn : 2 ≤ Fintype.card ↥((X : Set V)ᶜ))
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hbudget : c * (p * (Fintype.card ↥((X : Set V)ᶜ) : ℝ) + 2) <
      p ^ 2 * (edgeCount (G.induce (X : Set V)ᶜ) : ℝ))
    (d : ℝ) (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hoverlap : (Fintype.card V : ℝ) +
      (p * (Fintype.card ↥((X : Set V)ᶜ) : ℝ) + 2) +
      (X.card : ℝ) + (Fintype.card W : ℝ) ≤ 2 * d) :
    UniversalAt G H X := by
  classical
  obtain ⟨S, hXS, hSsize, ⟨M⟩⟩ :=
    exists_induced_minor_avoiding_of_sampling_budget H c hc hforces G X
      hn p hp hp1 hbudget
  have hbudgetS : (Fintype.card V : ℝ) + (S.card : ℝ) +
      (X.card : ℝ) + (Fintype.card W : ℝ) ≤ 2 * d := by
    linarith
  exact universalAt_of_minor_common_neighbor_candidates H G X S hXS M
    (common_neighbor_candidates_of_min_degree G X S d (Fintype.card W)
      hmin hbudgetS)

end HadwigerLean.RootedDensity
