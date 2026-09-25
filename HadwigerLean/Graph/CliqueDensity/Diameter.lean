import HadwigerLean.Graph.DensityBasic
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Short diameter from minimum degree above two fifths

Three vertices at pairwise distance at least three have disjoint open
neighborhoods. A shortest path of length at least six supplies such a triple,
contradicting minimum degree greater than two fifths of the order.
-/

namespace HadwigerLean

open SimpleGraph

/-- Open neighborhoods of vertices at distance at least three are disjoint. -/
private theorem neighborFinset_disjoint_of_two_lt_dist
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : V} (hxy : 2 < G.dist x y) :
    Disjoint (G.neighborFinset x) (G.neighborFinset y) := by
  apply Finset.disjoint_left.mpr
  intro z hx hy
  have hxz : G.Adj x z := (G.mem_neighborFinset x z).mp hx
  have hyz : G.Adj y z := (G.mem_neighborFinset y z).mp hy
  let p : G.Walk x y := .cons hxz (.cons hyz.symm .nil)
  have hle := G.dist_le p
  have hlen : p.length = 2 := rfl
  omega

/-- A finite connected graph with minimum degree above two fifths of its
order has diameter at most five. -/
theorem dist_le_five_of_min_degree_gt_two_fifths
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hdegree : ∀ v, 2 * Fintype.card V < 5 * G.degree v)
    (u v : V) : G.dist u v ≤ 5 := by
  classical
  by_contra hfar
  have hdist : 6 ≤ G.dist u v := by omega
  obtain ⟨p, hp, hlen⟩ := hconn.exists_path_of_dist u v
  let w : V := p.getVert 3
  have h3 : 3 ≤ p.length := by omega
  have huwtake :=
    SimpleGraph.length_eq_dist_of_subwalk hlen (p.isSubwalk_take 3)
  have huW : G.dist u w = 3 := by
    have ht : (p.take 3).length = 3 := by simp [h3]
    exact huwtake.symm.trans ht
  have hwvdrop :=
    SimpleGraph.length_eq_dist_of_subwalk hlen (p.isSubwalk_drop 3)
  have hwV : 3 ≤ G.dist w v := by
    have ht : (p.drop 3).length = p.length - 3 := p.drop_length 3
    rw [← hwvdrop]
    omega
  have hUW : Disjoint (G.neighborFinset u) (G.neighborFinset w) :=
    neighborFinset_disjoint_of_two_lt_dist G (by omega)
  have hUV : Disjoint (G.neighborFinset u) (G.neighborFinset v) :=
    neighborFinset_disjoint_of_two_lt_dist G (by omega)
  have hWV : Disjoint (G.neighborFinset w) (G.neighborFinset v) :=
    neighborFinset_disjoint_of_two_lt_dist G (by omega)
  have hunion : ((G.neighborFinset u ∪ G.neighborFinset w) ∪
      G.neighborFinset v).card ≤ Fintype.card V := by
    simpa using Finset.card_le_card
      (Finset.subset_univ
        ((G.neighborFinset u ∪ G.neighborFinset w) ∪ G.neighborFinset v))
  have hdisj : Disjoint (G.neighborFinset u ∪ G.neighborFinset w)
      (G.neighborFinset v) :=
    Finset.disjoint_union_left.mpr ⟨hUV, hWV⟩
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_union_of_disjoint hUW] at hunion
  change G.degree u + G.degree w + G.degree v ≤ Fintype.card V at hunion
  have hdu := hdegree u
  have hdw := hdegree w
  have hdv := hdegree v
  omega

end HadwigerLean
