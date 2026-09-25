import HadwigerLean.Graph.CliqueDensity.Reduction
import HadwigerLean.Graph.UnbalancedBipartite.BoundFinal
import Mathlib.Tactic

/-!
# The bipartite graph crossing two disjoint vertex sets
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

private def crossValue (A B : Finset V) : (↥(A : Set V) ⊕ ↥(B : Set V)) → V
  | .inl a => a.1
  | .inr b => b.1

private theorem crossValue_injective (A B : Finset V) (hdisj : Disjoint A B) :
    Function.Injective (crossValue A B) := by
  intro x y hxy
  cases x with
  | inl a =>
      cases y with
      | inl a' => exact congrArg Sum.inl (Subtype.ext hxy)
      | inr b =>
          have hab : a.1 = b.1 := hxy
          have haB : a.1 ∈ B := by rw [hab]; exact b.2
          exact False.elim ((Finset.disjoint_left.mp hdisj a.2) haB)
  | inr b =>
      cases y with
      | inl a =>
          have hba : b.1 = a.1 := hxy
          have hbA : b.1 ∈ A := by rw [hba]; exact a.2
          exact False.elim ((Finset.disjoint_left.mp hdisj hbA) b.2)
      | inr b' => exact congrArg Sum.inr (Subtype.ext hxy)

private def crossLeft (A B : Finset V) :
    Set (↥(A : Set V) ⊕ ↥(B : Set V)) :=
  {q | ∃ a, q = Sum.inl a}

private def crossRight (A B : Finset V) :
    Set (↥(A : Set V) ⊕ ↥(B : Set V)) :=
  {q | ∃ b, q = Sum.inr b}

private theorem crossLeft_disjoint_crossRight (A B : Finset V) :
    Disjoint (crossLeft A B) (crossRight A B) := by
  apply Set.disjoint_left.mpr
  intro q hqL hqR
  obtain ⟨a, rfl⟩ := hqL
  obtain ⟨b, hb⟩ := hqR
  cases hb

/-- All original edges between `A` and `B`, on a disjoint-sum vertex type. -/
noncomputable def crossGraph (G : SimpleGraph V) (A B : Finset V) :
    SimpleGraph (↥(A : Set V) ⊕ ↥(B : Set V)) :=
  (G.comap (crossValue A B)).between (crossLeft A B) (crossRight A B)

private noncomputable def crossLeftFinset (A B : Finset V) :
    Finset (↥(A : Set V) ⊕ ↥(B : Set V)) := by
  classical
  exact Finset.univ.filter (fun q => q ∈ crossLeft A B)

private noncomputable def crossRightFinset (A B : Finset V) :
    Finset (↥(A : Set V) ⊕ ↥(B : Set V)) := by
  classical
  exact Finset.univ.filter (fun q => q ∈ crossRight A B)

private theorem crossFinsets_cover (A B : Finset V) :
    crossLeftFinset A B ∪ crossRightFinset A B = Finset.univ := by
  classical
  ext q
  cases q <;> simp [crossLeftFinset, crossRightFinset, crossLeft, crossRight]

private theorem crossFinsets_card_left (A B : Finset V) :
    (crossLeftFinset A B).card = A.card := by
  classical
  have heq : crossLeftFinset A B =
      (Finset.univ : Finset ↥(A : Set V)).map Function.Embedding.inl := by
    ext q
    cases q <;> simp [crossLeftFinset, crossLeft]
  rw [heq, Finset.card_map]
  simpa using Fintype.card_coe A

private theorem crossFinsets_card_right (A B : Finset V) :
    (crossRightFinset A B).card = B.card := by
  classical
  have heq : crossRightFinset A B =
      (Finset.univ : Finset ↥(B : Set V)).map Function.Embedding.inr := by
    ext q
    cases q <;> simp [crossRightFinset, crossRight]
  rw [heq, Finset.card_map]
  simpa using Fintype.card_coe B

theorem crossGraph_isBipartiteWith (G : SimpleGraph V) (A B : Finset V) :
    (crossGraph G A B).IsBipartiteWith
      (crossLeftFinset A B : Set _) (crossRightFinset A B : Set _) := by
  classical
  simpa [crossGraph, crossLeftFinset, crossRightFinset] using
    ((G.comap (crossValue A B)).between_isBipartiteWith
      (crossLeft_disjoint_crossRight A B))

theorem crossGraph_isMinor (G : SimpleGraph V)
    (A B : Finset V) (hdisj : Disjoint A B) :
    IsMinor (crossGraph G A B) G := by
  let H := G.comap (crossValue A B)
  have hle : crossGraph G A B ≤ H := SimpleGraph.between_le
  have hminorH : IsMinor H G := by
    let f : H →g G := {
      toFun := crossValue A B
      map_rel' := by intro x y hxy; exact hxy
    }
    exact ⟨(MinorModel.refl H).map f (crossValue_injective A B hdisj)⟩
  exact IsMinor.trans (isMinor_of_graph_le hle) hminorH

private theorem crossGraph_degree_inl
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) [DecidableRel (crossGraph G A B).Adj]
    (a : ↥(A : Set V)) :
    (crossGraph G A B).degree (Sum.inl a) =
      (G.neighborFinset a.1 ∩ B).card := by
  classical
  let D := crossGraph G A B
  let T : Finset ↥(B : Set V) :=
    Finset.univ.filter (fun b => G.Adj a.1 b.1)
  have hmap : D.neighborFinset (Sum.inl a) =
      T.map Function.Embedding.inr := by
    ext q
    cases q with
    | inl a' =>
        simp [D, T, crossGraph, SimpleGraph.between_adj,
          crossLeft, crossRight, crossValue, D.mem_neighborFinset]
    | inr b =>
        simp [D, T, crossGraph, SimpleGraph.between_adj,
          crossLeft, crossRight, crossValue, D.mem_neighborFinset,
          G.mem_neighborFinset]
  have himage : T.image Subtype.val = G.neighborFinset a.1 ∩ B := by
    ext v
    simp [T, G.mem_neighborFinset]
  rw [← D.card_neighborFinset_eq_degree, hmap, Finset.card_map,
    ← himage]
  exact (Finset.card_image_of_injective T Subtype.val_injective).symm

/-- The edge count of the crossing bipartite graph is the sum of degrees
from the first part into the second. -/
theorem crossGraph_edgeCount_eq_sum_neighbors
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    edgeCount (crossGraph G A B) =
      ∑ v ∈ A, (G.neighborFinset v ∩ B).card := by
  classical
  let D := crossGraph G A B
  have hhand : ∑ q ∈ crossLeftFinset A B, D.degree q = edgeCount D := by
    simpa only [edgeCount_eq_card_edgeFinset] using
      D.isBipartiteWith_sum_degrees_eq_card_edges
        (crossGraph_isBipartiteWith G A B)
  have hleft : crossLeftFinset A B =
      (Finset.univ : Finset ↥(A : Set V)).map Function.Embedding.inl := by
    ext q
    cases q <;> simp [crossLeftFinset, crossLeft]
  calc
    edgeCount D = ∑ q ∈ crossLeftFinset A B, D.degree q := hhand.symm
    _ = ∑ a : ↥(A : Set V), D.degree (Sum.inl a) := by
      rw [hleft, Finset.sum_map]
      rfl
    _ = ∑ a : ↥(A : Set V), (G.neighborFinset a.1 ∩ B).card := by
      apply Finset.sum_congr rfl
      intro a ha
      exact crossGraph_degree_inl G A B a
    _ = ∑ v ∈ A, (G.neighborFinset v ∩ B).card := by
      exact (Finset.sum_coe_sort A
        (fun v => (G.neighborFinset v ∩ B).card))

/-- The checked Norin--Postle bound applied to arbitrary disjoint vertex
sets of a minor-free graph. -/
theorem cross_edges_le_unbalanced_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hdisj : Disjoint A B)
    (t : ℕ) (ht : 3 ≤ t) (hminor : ¬ HasCliqueMinor G t) :
    (∑ v ∈ A, ((G.neighborFinset v ∩ B).card : ℝ)) ≤
      6400 * ((t : ℝ) * Real.sqrt (Real.log (t : ℝ))) *
        Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) +
      ((t - 2 : ℕ) : ℝ) * ((A.card : ℝ) + (B.card : ℝ)) := by
  classical
  let D := crossGraph G A B
  letI : DecidableRel D.Adj := Classical.decRel _
  have hDminor : ¬ HasCliqueMinor D t := by
    intro h
    exact hminor (hasCliqueMinor_of_minor
      (crossGraph_isMinor G A B hdisj) h)
  have hbound := unbalanced_bipartite_edge_bound D
    (crossLeftFinset A B) (crossRightFinset A B) t ht
    (crossGraph_isBipartiteWith G A B) (crossFinsets_cover A B)
    hDminor
  rw [crossFinsets_card_left, crossFinsets_card_right] at hbound
  have hedges := crossGraph_edgeCount_eq_sum_neighbors G A B
  exact_mod_cast hedges ▸ hbound
end HadwigerLean
