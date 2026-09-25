import HadwigerLean.Graph.UnbalancedBipartite.RandomContraction
import HadwigerLean.Graph.UnbalancedBipartite.PathContraction
import HadwigerLean.Graph.UnbalancedBipartite.VertexDeletion

import Mathlib.Tactic

/-!
Structural bookkeeping for the final unbalanced bipartite bound.
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Vertices on the larger side retained for the star contraction. -/
def sampledLeftVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) (v : V) : Finset V :=
  (A.erase v).filter (fun w => ∃ x ∈ X, G.Adj w x)

theorem sampledLeftVertices_disjoint_neighbors
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B X : Finset V)
    (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (v : V) (hv : v ∈ A) (hX : X ⊆ G.neighborFinset v) :
    Disjoint (sampledLeftVertices G A X v) X := by
  apply Finset.disjoint_left.mpr
  intro w hwA hwX
  have hwA' : w ∈ A := (Finset.mem_erase.mp (Finset.mem_filter.mp hwA).1).2
  have hwB : w ∈ B := hG.mem_of_mem_adj hv
    ((G.mem_neighborFinset v w).mp (hX hwX))
  exact (Set.disjoint_left.mp hG.disjoint) hwA' hwB

theorem sampledLeftVertices_has_choice
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) (v : V) :
    ∀ w ∈ sampledLeftVertices G A X v, ∃ x ∈ X, G.Adj w x := by
  intro w hw
  exact (Finset.mem_filter.mp hw).2

/-- Every common neighbor of two sampled vertices, except the center,
appears among the vertices eligible for the random star contraction. -/
theorem common_neighbors_le_sampled_star_common
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B X : Finset V)
    (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (v : V) (hv : v ∈ A) (hX : X ⊆ G.neighborFinset v)
    (x y : ↥(X : Set V)) :
    ((G.neighborFinset x.1 ∩ G.neighborFinset y.1).erase v).card ≤
      (starCommonNeighbors G (sampledLeftVertices G A X v) X x y).card := by
  classical
  let C := (G.neighborFinset x.1 ∩ G.neighborFinset y.1).erase v
  let D := starCommonNeighbors G (sampledLeftVertices G A X v) X x y
  have hxB : x.1 ∈ B := hG.mem_of_mem_adj hv
    ((G.mem_neighborFinset v x.1).mp (hX x.property))
  let f : ↥(C : Set V) → ↥(D : Set ↥(sampledLeftVertices G A X v : Set V)) :=
    fun w => by
      have hwne : w.1 ≠ v := (Finset.mem_erase.mp w.property).1
      have hwinter := (Finset.mem_erase.mp w.property).2
      have hwx : G.Adj w.1 x.1 :=
        (G.mem_neighborFinset x.1 w.1).mp (Finset.mem_inter.mp hwinter).1 |>.symm
      have hwy : G.Adj w.1 y.1 :=
        (G.mem_neighborFinset y.1 w.1).mp (Finset.mem_inter.mp hwinter).2 |>.symm
      have hwA : w.1 ∈ A := hG.mem_of_mem_adj' hxB hwx
      have hwSample : w.1 ∈ sampledLeftVertices G A X v := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_erase.mpr ⟨hwne, hwA⟩, ⟨x.1, x.property, hwx⟩⟩
      exact ⟨⟨w.1, hwSample⟩, by
        simp [D, starCommonNeighbors, hwx, hwy]⟩
  have hf : Function.Injective f := by
    intro w z h
    apply Subtype.ext
    exact congrArg (fun q : ↥(sampledLeftVertices G A X v : Set V) => q.1)
      (congrArg Subtype.val h)
  exact Finset.card_le_card_of_injective hf


/-- The surviving bipartition classes cover the path-contraction graph. -/
theorem twoNeighborContraction_class_cover
    (A B : Finset V) (hcover : A ∪ B = Finset.univ)
    (v u₂ : V) :
    let S := twoNeighborContractionSet v u₂
    let L : Finset S := Finset.univ.filter (fun x => x.1 ∈ A)
    let R : Finset S := Finset.univ.filter (fun x => x.1 ∈ B)
    L ∪ R = Finset.univ := by
  intro S L R
  ext x
  have hx : x.1 ∈ A ∪ B := by rw [hcover]; simp
  simp only [Finset.mem_union, Finset.mem_univ, iff_true]
  rcases Finset.mem_union.mp hx with hA | hB
  · exact Or.inl (by simpa [L] using hA)
  · exact Or.inr (by simpa [R] using hB)
end HadwigerLean
