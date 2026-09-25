import HadwigerLean.Graph.CliqueDensity.Reduction
import Mathlib.Tactic

/-! The elementary closed-neighborhood bounds used by Appendix F.b. -/

namespace HadwigerLean.RootedDensity

universe u

/-- The closed neighborhood of a vertex as a finite vertex set. -/
def closedNeighborhoodFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  insert v (G.neighborFinset v)

/-- Closed-neighborhood order is center degree plus one. -/
theorem card_closedNeighborhoodFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (closedNeighborhoodFinset G v).card = G.degree v + 1 := by
  have hv : v ∉ G.neighborFinset v := by simp
  simp [closedNeighborhoodFinset, Finset.card_insert_of_notMem hv,
    SimpleGraph.card_neighborFinset_eq_degree]

/-- Every common neighbor of `v,w` is a neighbor of `w` inside the
closed neighborhood of `v`. -/
theorem card_commonNeighbors_le_degree_closedNeighborhood
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {v w : V} (hvw : G.Adj v w) :
    Fintype.card (G.commonNeighbors v w) ≤
      (G.induce (closedNeighborhoodFinset G v : Set V)).degree
        ⟨w, Finset.mem_insert.mpr (Or.inr ((G.mem_neighborFinset v w).mpr hvw))⟩ := by
  classical
  let D := closedNeighborhoodFinset G v
  let ww : ↥(D : Set V) := ⟨w, Finset.mem_insert.mpr (Or.inr ((G.mem_neighborFinset v w).mpr hvw))⟩
  let f : G.commonNeighbors v w ↪ (G.induce (D : Set V)).neighborSet ww := {
    toFun := fun x => by
      have hxv : G.Adj v x := (G.mem_commonNeighbors.mp x.property).1
      have hxw : G.Adj w x := (G.mem_commonNeighbors.mp x.property).2
      exact ⟨⟨x, by
        exact Finset.mem_insert_of_mem
          ((G.mem_neighborFinset v x).mpr hxv)⟩, hxw⟩
    inj' := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : (G.induce (D : Set V)).neighborSet ww =>
        ((z : ↥(D : Set V)) : V)) hxy
  }
  change Fintype.card (G.commonNeighbors v w) ≤
    (G.induce (D : Set V)).degree ww
  rw [← (G.induce (D : Set V)).card_neighborSet_eq_degree]
  exact Fintype.card_le_of_injective f f.injective

/-- A center degree bound and common-neighbor bounds on every incident edge
make its closed neighborhood uniformly dense in minimum degree. -/
theorem min_degree_closedNeighborhood_of_commonNeighbors
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (d : ℝ)
    (hcenter : d ≤ (G.degree v : ℝ))
    (hcommon : ∀ w : V, G.Adj v w →
      d ≤ (Fintype.card (G.commonNeighbors v w) : ℝ)) :
    ∀ x : ↥(closedNeighborhoodFinset G v : Set V),
      d ≤ ((G.induce (closedNeighborhoodFinset G v : Set V)).degree x : ℝ) := by
  classical
  intro x
  have hx : (x : V) = v ∨ G.Adj v x := by
    have hmem := x.property
    change (x : V) ∈ closedNeighborhoodFinset G v at hmem
    rcases Finset.mem_insert.mp hmem with heq | hne
    · exact Or.inl heq
    · exact Or.inr ((G.mem_neighborFinset v x).mp hne)
  rcases hx with heq | hadj
  · let vv : ↥(closedNeighborhoodFinset G v : Set V) := ⟨v, by
      simp [closedNeighborhoodFinset]⟩
    have hxEq : x = vv := Subtype.ext heq
    rw [hxEq]
    let D := closedNeighborhoodFinset G v
    let f : G.neighborSet v ↪ (G.induce (D : Set V)).neighborSet vv := {
      toFun := fun y => ⟨⟨y, Finset.mem_insert_of_mem
        ((G.mem_neighborFinset v y).mpr y.property)⟩, y.property⟩
      inj' := by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun z : (G.induce (D : Set V)).neighborSet vv =>
          ((z : ↥(D : Set V)) : V)) hab
    }
    have hcard : G.degree v ≤
        (G.induce (D : Set V)).degree vv := by
      rw [← G.card_neighborSet_eq_degree,
        ← (G.induce (D : Set V)).card_neighborSet_eq_degree]
      exact Fintype.card_le_of_injective f f.injective
    have hcardR : (G.degree v : ℝ) ≤
        ((G.induce (D : Set V)).degree vv : ℝ) := by exact_mod_cast hcard
    exact hcenter.trans hcardR
  · have hcard := card_commonNeighbors_le_degree_closedNeighborhood G hadj
    have hcardR : (Fintype.card (G.commonNeighbors v x) : ℝ) ≤
        ((G.induce (closedNeighborhoodFinset G v : Set V)).degree x : ℝ) := by
      exact_mod_cast hcard
    linarith [hcommon x hadj]

end HadwigerLean.RootedDensity



