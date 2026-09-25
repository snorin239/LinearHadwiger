import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Tactic

/-!
# A spanning tree containing every adhesion star edge

In a torso, adhesion vertices form a clique. Choose any adhesion
vertex as a temporary center; the star from it to all other adhesion
vertices is an acyclic subgraph. Extend that star to a spanning tree.
This provides the tree used in the multiboundary rigid truncation.
-/

namespace HadwigerLean.RootedDensity

universe u

theorem exists_tree_with_boundary_star
    {V : Type u} (K : SimpleGraph V) (Z : Set V)
    (center : V)
    (hK : K.Connected)
    (hstar : ∀ z ∈ Z, z ≠ center → K.Adj center z) :
    ∃ T : SimpleGraph V,
      T ≤ K ∧ T.IsTree ∧
      ∀ z ∈ Z, z ≠ center → T.Adj center z := by
  let F : SimpleGraph V := SimpleGraph.starGraph center ⊓ K
  have hFK : F ≤ K := inf_le_right
  have hFacyc : F.IsAcyclic :=
    (SimpleGraph.isAcyclic_starGraph center).anti inf_le_left
  obtain ⟨T,hFT,hTK,hTree⟩ :=
    hK.exists_isTree_le_of_le_of_isAcyclic hFK hFacyc
  refine ⟨T,hTK,hTree,?_⟩
  intro z hz hzc
  apply hFT
  change (SimpleGraph.starGraph center).Adj center z ∧
    K.Adj center z
  exact ⟨SimpleGraph.starGraph_center_adj hzc.symm,
    hstar z hz hzc⟩


/-- The star edges joining the temporary center to the other
adhesion vertices. -/
def boundaryStarEdges {V : Type u} (Z : Set V) (center : V) :
    Set (Sym2 V) :=
  {e | ∃ z ∈ Z, z ≠ center ∧ e = s(center,z)}

/-- Removing the prescribed star edges from a tree separates all
distinct adhesion vertices. This is the forest underlying the
center and hanging pieces of rigid truncation. -/
theorem boundary_vertices_separated_after_star_delete
    {V : Type u} (T : SimpleGraph V) (Z : Set V)
    (center : V) (hT : T.IsTree)
    (hstar : ∀ z ∈ Z, z ≠ center → T.Adj center z)
    {z w : V} (hz : z ∈ Z) (hw : w ∈ Z) (hzw : z ≠ w) :
    ¬ (T.deleteEdges (boundaryStarEdges Z center)).Reachable z w := by
  let F := T.deleteEdges (boundaryStarEdges Z center)
  have hseparated (a : V) (ha : a ∈ Z) (hac : a ≠ center) :
      ¬ F.Reachable center a := by
    have hsingle : ({s(center,a)} : Set (Sym2 V)) ⊆
        boundaryStarEdges Z center := by
      intro e he
      have heq : e = s(center,a) := by simpa using he
      exact ⟨a,ha,hac,heq⟩
    have hFle : F ≤ T.deleteEdges {s(center,a)} :=
      T.deleteEdges_anti hsingle
    have hbridge : T.IsBridge s(center,a) :=
      (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp
        hT.isAcyclic) (hstar a ha hac)
    exact fun h => (SimpleGraph.isBridge_iff.mp hbridge)
      (h.mono hFle)
  by_cases hzc : z = center
  · subst z
    exact hseparated w hw (Ne.symm hzw)
  by_cases hwc : w = center
  · subst w
    intro h
    exact hseparated z hz hzc h.symm
  intro hreach
  have hsingle : ({s(center,z)} : Set (Sym2 V)) ⊆
      boundaryStarEdges Z center := by
    intro e he
    have heq : e = s(center,z) := by simpa using he
    exact ⟨z,hz,hzc,heq⟩
  have hFle : F ≤ T.deleteEdges {s(center,z)} :=
    T.deleteEdges_anti hsingle
  have hzw' : (T.deleteEdges {s(center,z)}).Reachable z w :=
    hreach.mono hFle
  have hEdge : (T.deleteEdges {s(center,z)}).Adj w center := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨(hstar w hw hwc).symm, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro heq
    rcases Sym2.eq_iff.mp heq with ⟨hwc',_⟩ | ⟨hwz,_⟩
    · exact hwc hwc'
    · exact hzw hwz.symm
  have hbridge : T.IsBridge s(center,z) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp
      hT.isAcyclic) (hstar z hz hzc)
  exact (SimpleGraph.isBridge_iff.mp hbridge)
    (hzw'.trans hEdge.reachable).symm


/-- Every component of the forest obtained by deleting the adhesion
star meets the adhesion. Removed edges have both ends in the
adhesion, so a component avoiding the adhesion would remain
isolated even in the connected tree. -/
theorem star_forest_component_meets_boundary
    {V : Type u} (T : SimpleGraph V) (Z : Set V)
    (center : V) (hT : T.Connected) (hcenter : center ∈ Z)
    (v : V) :
    ∃ z ∈ Z,
      (T.deleteEdges (boundaryStarEdges Z center)).Reachable v z := by
  let F := T.deleteEdges (boundaryStarEdges Z center)
  by_contra hnone
  have havoid : ∀ z ∈ Z, ¬ F.Reachable v z := by
    intro z hz hr
    exact hnone ⟨z,hz,hr⟩
  have hlift : ∀ w, Relation.ReflTransGen T.Adj v w →
      F.Reachable v w := by
    intro w hw
    induction hw with
    | refl => exact SimpleGraph.Reachable.refl v
    | @tail b c hprev hbc ih =>
        have hbNotZ : b ∉ Z := fun hb => havoid b hb ih
        have hbcF : F.Adj b c := by
          apply SimpleGraph.deleteEdges_adj.mpr
          refine ⟨hbc,?_⟩
          rintro ⟨z,hz,_,heq⟩
          rcases Sym2.eq_iff.mp heq with h | h
          · exact hbNotZ (h.1 ▸ hcenter)
          · exact hbNotZ (h.1 ▸ hz)
        exact ih.trans hbcF.reachable
  have hvc : Relation.ReflTransGen T.Adj v center := by
    rw [← SimpleGraph.reachable_eq_reflTransGen]
    exact hT.preconnected v center
  exact havoid center hcenter (hlift center hvc)

/-- Each forest component contains exactly one adhesion vertex.
The existence uses connectivity of the original tree; uniqueness
uses the bridge property of its prescribed star edges. -/
theorem star_forest_unique_boundary
    {V : Type u} (T : SimpleGraph V) (Z : Set V)
    (center : V) (hT : T.IsTree) (hcenter : center ∈ Z)
    (hstar : ∀ z ∈ Z, z ≠ center → T.Adj center z)
    (v : V) :
    ∃! z : V, z ∈ Z ∧
      (T.deleteEdges (boundaryStarEdges Z center)).Reachable v z := by
  obtain ⟨z,hz,hvz⟩ :=
    star_forest_component_meets_boundary T Z center
      hT.connected hcenter v
  refine ⟨z,⟨hz,hvz⟩,?_⟩
  intro w ⟨hw,hvw⟩
  by_contra hne
  exact boundary_vertices_separated_after_star_delete
    T Z center hT hstar hz hw (fun h => hne h.symm)
    (hvz.symm.trans hvw)


/-- A forest edge remaining after deleting the adhesion star is a
real edge: an artificial torso edge would join two distinct
adhesion vertices, which the forest has separated. -/
theorem star_forest_edges_real
    {V : Type u}
    (K near T : SimpleGraph V) (Z : Set V)
    (center : V)
    (hTK : T ≤ K) (hT : T.IsTree)
    (hstar : ∀ z ∈ Z, z ≠ center → T.Adj center z)
    (hfake : ∀ a b, K.Adj a b →
      near.Adj a b ∨ (a ∈ Z ∧ b ∈ Z)) :
    T.deleteEdges (boundaryStarEdges Z center) ≤ near := by
  intro a b hab
  have habT : T.Adj a b :=
    (SimpleGraph.deleteEdges_adj.mp hab).1
  rcases hfake a b (hTK habT) with hreal | ⟨ha,hb⟩
  · exact hreal
  · exact False.elim
      (boundary_vertices_separated_after_star_delete
        T Z center hT hstar ha hb habT.ne hab.reachable)

/-- A connected torso branch with clique adhesion admits a forest
partition into connected real-edge pieces, one per adhesion
vertex. The piece containing the prescribed root is determined
by its unique adhesion vertex. -/
theorem exists_star_forest_real_decomposition
    {V : Type u}
    (K near : SimpleGraph V) (Z : Set V)
    (center : V) (hcenter : center ∈ Z)
    (hK : K.Connected)
    (hstar : ∀ z ∈ Z, z ≠ center → K.Adj center z)
    (hfake : ∀ a b, K.Adj a b →
      near.Adj a b ∨ (a ∈ Z ∧ b ∈ Z)) :
    ∃ T : SimpleGraph V,
      T ≤ K ∧ T.IsTree ∧
      let F := T.deleteEdges (boundaryStarEdges Z center)
      F ≤ near ∧
      (∀ v, ∃! z, z ∈ Z ∧ F.Reachable v z) ∧
      (∀ v,
        (near.induce
          ((F.connectedComponentMk v).supp : Set V)).Connected) := by
  obtain ⟨T,hTK,hTree,hStarT⟩ :=
    exists_tree_with_boundary_star K Z center hK hstar
  refine ⟨T,hTK,hTree,?_⟩
  let F := T.deleteEdges (boundaryStarEdges Z center)
  have hFNear : F ≤ near :=
    star_forest_edges_real K near T Z center hTK hTree hStarT hfake
  refine ⟨hFNear,?_,?_⟩
  · intro v
    exact star_forest_unique_boundary T Z center
      hTree hcenter hStarT v
  · intro v
    let C := F.connectedComponentMk v
    have hCconn : (F.induce (C.supp : Set V)).Connected :=
      C.connected_toSimpleGraph
    have hle : F.induce (C.supp : Set V) ≤
        near.induce (C.supp : Set V) := by
      intro a b hab
      exact hFNear hab
    exact hCconn.mono hle

end HadwigerLean.RootedDensity
