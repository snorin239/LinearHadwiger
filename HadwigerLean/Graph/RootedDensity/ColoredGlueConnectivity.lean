import HadwigerLean.Graph.RootedDensity.RigidUnion
import Mathlib.Tactic

/-! Connectivity of the near/far branches in the colored rigid glue. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- Any family of connected pieces attached by an edge to a connected
anchor has connected union with that anchor. -/
theorem connected_induce_anchor_union_iUnion
    {V : Type u} {U : Type v} (G : SimpleGraph V)
    (A : Set V) (P : U → Set V)
    (hA : (G.induce A).Connected)
    (hP : ∀ u, (G.induce (P u)).Connected)
    (hattach : ∀ u, ∃ a ∈ A, ∃ p ∈ P u, G.Adj a p) :
    (G.induce (A ∪ ⋃ u, P u)).Connected := by
  classical
  obtain ⟨a, ha⟩ := hA.nonempty
  have haUnion : a ∈ A ∪ ⋃ u, P u := Or.inl ha
  apply G.induce_connected_of_patches a haUnion
  intro x hx
  rcases hx with hxA | hxP
  · refine ⟨A, ?_, ha, hxA, hA.preconnected _ _⟩
    exact Set.subset_union_left
  · obtain ⟨u, hxPu⟩ := Set.mem_iUnion.mp hxP
    obtain ⟨z, hzA, w, hwP, hzw⟩ := hattach u
    have hconn := G.connected_induce_union
      hA.preconnected (hP u).preconnected hzA hwP hzw
    refine ⟨A ∪ P u, ?_, Or.inl ha, Or.inr hxPu, hconn.preconnected _ _⟩
    intro y hy
    rcases hy with hyA | hyPu
    · exact Or.inl hyA
    · exact Or.inr (Set.mem_iUnion.mpr ⟨u, hyPu⟩)

/-- A color-2 hanger connects to its far branch at the hanger root;
that far branch connects to the owner's far branch by a target edge. -/
theorem connected_induce_color2_attachment
    {V : Type u} (G : SimpleGraph V)
    (farOwner farMatched hanger : Set V)
    (hfarOwner : (G.induce farOwner).Connected)
    (hfarMatched : (G.induce farMatched).Connected)
    (hhanger : (G.induce hanger).Connected)
    (hfarEdge : ∃ x ∈ farOwner, ∃ y ∈ farMatched, G.Adj x y)
    (hroot : (farMatched ∩ hanger).Nonempty) :
    (G.induce (farOwner ∪ farMatched ∪ hanger)).Connected := by
  obtain ⟨x,hx,y,hy,hxy⟩ := hfarEdge
  have hfirst := G.connected_induce_union hfarOwner.preconnected
    hfarMatched.preconnected hx hy hxy
  have hsecond := G.induce_union_connected hfirst.preconnected
    hhanger.preconnected (by
      obtain ⟨z,hzFar,hzHanger⟩ := hroot
      exact ⟨z,Or.inr hzFar,hzHanger⟩)
  simpa only [Set.union_assoc] using hsecond

/-- A color-1 hanger joins a boundary-free near branch by a real edge
and joins its far branch at the labeled adhesion vertex. -/
theorem connected_induce_color1_attachment
    {V : Type u} (G : SimpleGraph V)
    (nearFree hanger farFree : Set V)
    (hnear : (G.induce nearFree).Connected)
    (hhanger : (G.induce hanger).Connected)
    (hfar : (G.induce farFree).Connected)
    (hwitness : ∃ x ∈ nearFree, ∃ y ∈ hanger, G.Adj x y)
    (hroot : (hanger ∩ farFree).Nonempty) :
    (G.induce (nearFree ∪ hanger ∪ farFree)).Connected := by
  obtain ⟨x,hx,y,hy,hxy⟩ := hwitness
  have hfirst := G.connected_induce_union hnear.preconnected
    hhanger.preconnected hx hy hxy
  have hsecond := G.induce_union_connected hfirst.preconnected
    hfar.preconnected (by
      obtain ⟨z,hzHanger,hzFar⟩ := hroot
      exact ⟨z,Or.inr hzHanger,hzFar⟩)
  simpa only [Set.union_assoc] using hsecond

end HadwigerLean.RootedDensity

