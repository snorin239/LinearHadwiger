import HadwigerLean.Graph.Linkedness.PathShortcut
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic

/-!
# Diameter bound for dense small graphs
-/

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A shortest path has no two vertices separated by at least three edges
with a common neighbor. -/
private theorem geodesic_neighborFinset_disjoint
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {s t : V} (p : G.Path s t)
    (hmin : ∀ q : G.Path s t,
      (p : G.Walk s t).length ≤ (q : G.Walk s t).length)
    (i j : ℕ) (hi : i ≤ (p : G.Walk s t).length)
    (hj : j ≤ (p : G.Walk s t).length) (hgap : i + 3 ≤ j) :
    Disjoint (G.neighborFinset ((p : G.Walk s t).getVert i))
      (G.neighborFinset ((p : G.Walk s t).getVert j)) := by
  classical
  have hidx (n : ℕ) (hn : n ≤ (p : G.Walk s t).length) :
      (p : G.Walk s t).support.idxOf ((p : G.Walk s t).getVert n) = n := by
    rw [(p : G.Walk s t).getVert_eq_support_getElem hn]
    exact List.get_idxOf p.property.support_nodup
      ⟨n, by simpa only [(p : G.Walk s t).length_support] using Nat.lt_add_one_of_le hn⟩
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  have hai : G.Adj ((p : G.Walk s t).getVert i) v :=
    (G.mem_neighborFinset _ _).mp hvi
  have hbj : G.Adj v ((p : G.Walk s t).getVert j) :=
    (G.adj_comm _ _).mp ((G.mem_neighborFinset _ _).mp hvj)
  obtain ⟨q, _, hlt⟩ := path_shortcut_of_distant_neighbors p
    ((p : G.Walk s t).getVert_mem_support i)
    ((p : G.Walk s t).getVert_mem_support j)
    hai hbj (by simpa [hidx i hi, hidx j hj] using hgap)
  exact (Nat.not_lt_of_ge (hmin q)) hlt

end Linkedness
end HadwigerLean


namespace HadwigerLean
namespace Linkedness

private theorem reachable_exists_shortestPath
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {s t : V}
    (hr : G.Reachable s t) :
    ∃ p : G.Path s t, ∀ q : G.Path s t,
      (p : G.Walk s t).length ≤ (q : G.Walk s t).length := by
  obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_edist
  refine ⟨w.toPath, ?_⟩
  intro q
  have hwle : w.length ≤ (q : G.Walk s t).length := by
    have hq := (q : G.Walk s t).edist_le
    rw [← hw] at hq
    exact ENat.coe_le_coe.mp hq
  exact w.length_bypass_le_length.trans hwle

/-- In a graph on at most `14k` vertices of minimum degree at least `5k`,
any two vertices in the same component have a path of length at most five. -/
theorem dense_reachable_path_length_le_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hdeg : ∀ v, 5 * k ≤ G.degree v)
    (horder : Fintype.card V ≤ 14 * k)
    {s t : V} (hr : G.Reachable s t) :
    ∃ p : G.Path s t, (p : G.Walk s t).length ≤ 5 := by
  classical
  obtain ⟨p, hmin⟩ := reachable_exists_shortestPath hr
  refine ⟨p, ?_⟩
  by_contra hlong
  have hp6 : 6 ≤ (p : G.Walk s t).length := by omega
  let v₀ := (p : G.Walk s t).getVert 0
  let v₃ := (p : G.Walk s t).getVert 3
  let v₆ := (p : G.Walk s t).getVert 6
  have h03 : Disjoint (G.neighborFinset v₀) (G.neighborFinset v₃) :=
    geodesic_neighborFinset_disjoint p hmin 0 3 (by omega) (by omega) (by omega)
  have h36 : Disjoint (G.neighborFinset v₃) (G.neighborFinset v₆) :=
    geodesic_neighborFinset_disjoint p hmin 3 6 (by omega) (by omega) (by omega)
  have h06 : Disjoint (G.neighborFinset v₀) (G.neighborFinset v₆) :=
    geodesic_neighborFinset_disjoint p hmin 0 6 (by omega) (by omega) (by omega)
  have hdis : Disjoint (G.neighborFinset v₀ ∪ G.neighborFinset v₃)
      (G.neighborFinset v₆) := by
    exact Finset.disjoint_union_left.mpr ⟨h06, h36⟩
  have hcard : (G.neighborFinset v₀ ∪ G.neighborFinset v₃ ∪
      G.neighborFinset v₆).card =
      G.degree v₀ + G.degree v₃ + G.degree v₆ := by
    rw [Finset.card_union_of_disjoint hdis, Finset.card_union_of_disjoint h03]
    rfl
  have hle : (G.neighborFinset v₀ ∪ G.neighborFinset v₃ ∪
      G.neighborFinset v₆).card ≤ Fintype.card V := by
    simpa using (Finset.card_le_card (Finset.subset_univ
      (G.neighborFinset v₀ ∪ G.neighborFinset v₃ ∪ G.neighborFinset v₆)))
  have hk : 0 < k := by
    haveI : Nonempty V := ⟨s⟩
    have hV : 0 < Fintype.card V := Fintype.card_pos
    omega
  have h₀ := hdeg v₀
  have h₃ := hdeg v₃
  have h₆ := hdeg v₆
  omega

end Linkedness
end HadwigerLean
