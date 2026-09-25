import HadwigerLean.Inseparability.StageOldIntersection

/-!
# Placement of old and child CI models

The old model meets the previous connected region only at its reserved
roots. Every child model lies in a piece avoiding those roots, and
different child pieces are disjoint.
-/

namespace HadwigerLean.Inseparability

universe u

theorem rooted_model_disjoint_piece_of_tangent
    {I : Type u} {V : Type*} {G : SimpleGraph V}
    {root : I → V}
    (A : RootedMinorModel (SimpleGraph.completeGraph I) G root)
    (R W J : Set V)
    (htangent : ∀ i, A.branch i ∩ R = {root i})
    (hJ : J ⊆ R \ W)
    (hrootW : ∀ i, root i ∈ W) :
    Disjoint A.toMinorModel.vertices J := by
  apply Set.disjoint_left.mpr
  intro v hvA hvJ
  have hvR : v ∈ R := (hJ hvJ).1
  have hvRoot : v ∈ Set.range root := by
    rw [← rooted_model_vertices_inter_region_eq_roots A R htangent]
    exact ⟨hvA,hvR⟩
  obtain ⟨i,rfl⟩ := hvRoot
  exact (hJ hvJ).2 (hrootW i)

theorem rooted_model_disjoint_child_of_tangent
    {I K : Type u} {V : Type*} {G : SimpleGraph V}
    {root : I → V} {childRoot : K → V}
    (A : RootedMinorModel (SimpleGraph.completeGraph I) G root)
    (M : RootedMinorModel (SimpleGraph.completeGraph K) G childRoot)
    (R W J : Set V)
    (htangent : ∀ i, A.branch i ∩ R = {root i})
    (hJ : J ⊆ R \ W)
    (hrootW : ∀ i, root i ∈ W)
    (hM : M.toMinorModel.vertices ⊆ J) :
    Disjoint A.toMinorModel.vertices M.toMinorModel.vertices := by
  exact (rooted_model_disjoint_piece_of_tangent A R W J
    htangent hJ hrootW).mono_right hM

theorem rooted_child_models_disjoint_of_pieces
    {I K : Type u} {V : Type*} {G : SimpleGraph V}
    {root₁ : I → V} {root₂ : K → V}
    (M₁ : RootedMinorModel (SimpleGraph.completeGraph I) G root₁)
    (M₂ : RootedMinorModel (SimpleGraph.completeGraph K) G root₂)
    (J₁ J₂ : Set V)
    (hM₁ : M₁.toMinorModel.vertices ⊆ J₁)
    (hM₂ : M₂.toMinorModel.vertices ⊆ J₂)
    (hJ : Disjoint J₁ J₂) :
    Disjoint M₁.toMinorModel.vertices M₂.toMinorModel.vertices :=
  hJ.mono hM₁ hM₂

end HadwigerLean.Inseparability
