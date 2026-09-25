import HadwigerLean.Graph.RootedDensity.StarPieces
import HadwigerLean.Graph.RootedDensity.RigidUnion
import Mathlib.Tactic

/-!
# Deleting a forest component inside an ambient branch

The star-piece lemmas work on the subtype of one torso branch. This
module maps the connected retained complement back to the ambient
torso graph, preserving the exact vertex set.
-/

namespace HadwigerLean.RootedDensity

universe u

theorem image_compl_starPiece_eq_diff
    {V : Type u} (S : Set V) (F : SimpleGraph S) (drop : S) :
    Subtype.val '' (starPiece F drop)ᶜ =
      S \ (Subtype.val '' starPiece F drop) := by
  ext v
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨x.2,?_⟩
    rintro ⟨y,hy,hxy⟩
    have h : x = y := Subtype.ext hxy.symm
    exact hx (h ▸ hy)
  · rintro ⟨hvS,hvNot⟩
    refine ⟨⟨v,hvS⟩,?_,rfl⟩
    intro hv
    exact hvNot ⟨⟨v,hvS⟩,hv,rfl⟩

theorem starPiece_delete_connected_ambient
    {V : Type u} (G : SimpleGraph V) (S : Set V)
    (F : SimpleGraph S) (Z : Set S)
    (hFK : F ≤ G.induce S)
    (hUnique : ∀ v, ∃! z, z ∈ Z ∧ F.Reachable v z)
    (hclique : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w →
      (G.induce S).Adj z w)
    (center drop : S) (hc : center ∈ Z) (hd : drop ∈ Z)
    (hneq : center ≠ drop) :
    (G.induce (S \ (Subtype.val '' starPiece F drop))).Connected := by
  have hconn := starPiece_complement_connected
    (G.induce S) F Z hFK hUnique hclique
    center drop hc hd hneq
  have hambient := connected_induce_subtype_image G S
    (starPiece F drop)ᶜ hconn
  rw [image_compl_starPiece_eq_diff S F drop] at hambient
  exact hambient

end HadwigerLean.RootedDensity
