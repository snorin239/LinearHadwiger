import HadwigerLean.Graph.RootedDensity.RigidLabels
import Mathlib.Tactic

/-!
# Joining real near-side and far-side branch pieces
-/

namespace HadwigerLean.RootedDensity

universe u

/-- Induced connectivity passes through the inclusion of a subtype into
the ambient graph, with the vertex set recorded as an image. -/
theorem connected_induce_subtype_image
    {V : Type u} (G : SimpleGraph V) (S : Set V) (A : Set S)
    (hconn : ((G.induce S).induce A).Connected) :
    (G.induce (Subtype.val '' A)).Connected := by
  let f : ((G.induce S).induce A) →g
      (G.induce (Subtype.val '' A)) := {
    toFun := fun x => ⟨x.1.1, ⟨x.1, x.2, rfl⟩⟩
    map_rel' := by
      intro x y hxy
      exact hxy
  }
  apply hconn.map f
  rintro ⟨v, hv⟩
  obtain ⟨x, hx, rfl⟩ := hv
  exact ⟨⟨x, hx⟩, rfl⟩

/-- Connected pieces in the two sides of a separation glue into one
connected branch when they share an adhesion vertex. -/
theorem connected_induce_near_far_union
    {V : Type u} (G : SimpleGraph V) (S : VertexSeparation G)
    (A : Set S.left) (B : Set S.right)
    (hA : ((G.induce S.left).induce A).Connected)
    (hB : ((G.induce S.right).induce B).Connected)
    (hinter : (Subtype.val '' A ∩ Subtype.val '' B).Nonempty) :
    (G.induce (Subtype.val '' A ∪ Subtype.val '' B)).Connected := by
  have hA' := connected_induce_subtype_image G S.left A hA
  have hB' := connected_induce_subtype_image G S.right B hB
  exact G.induce_union_connected hA'.preconnected hB'.preconnected hinter

end HadwigerLean.RootedDensity