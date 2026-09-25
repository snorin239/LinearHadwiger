import HadwigerLean.Graph.RootedDensity.RootedModelTrim
import Mathlib.Tactic

/-!
# A minimal branch needs a boundary-free witness for each hanging piece

If a connected non-root-deleting trim removes a nonempty portion of one
branch, minimality forces some target adjacency to rely on that portion.
When the adhesion is a clique, this other branch cannot itself meet the
adhesion, because that adjacency can then be witnessed by the two
adhesion vertices.
-/

namespace HadwigerLean.RootedDensity

universe u v

theorem minimal_hanger_has_boundary_free_neighbor
    {V : Type u} {I : Type v}
    [Fintype V] [Fintype I] [DecidableEq I]
    {K : SimpleGraph V} {H : SimpleGraph I} {root : I → V}
    (M : RootedMinorModel H K root)
    (hmin : ∀ N : RootedMinorModel H K root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (Z : Set V)
    (hclique : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → K.Adj z w)
    (i : I) (D : Set V)
    (hDsub : D ⊆ M.branch i)
    (hDnonempty : D.Nonempty)
    (hCconn : (K.induce (M.branch i \ D)).Connected)
    (hrootC : root i ∈ M.branch i \ D)
    (hcenter : ∃ z ∈ M.branch i \ D, z ∈ Z) :
    ∃ j : I, H.Adj i j ∧
      (∀ y ∈ M.branch j, y ∉ Z) ∧
      ∃ x ∈ D, ∃ y ∈ M.branch j, K.Adj x y := by
  classical
  by_contra hnone
  have hno (j : I) (hij : H.Adj i j)
      (hfree : ∀ y ∈ M.branch j, y ∉ Z)
      (x : V) (hx : x ∈ D) (y : V)
      (hy : y ∈ M.branch j) : ¬ K.Adj x y := by
    intro hxy
    exact hnone ⟨j,hij,hfree,x,hx,y,hy,hxy⟩
  have hproper : M.branch i \ D ⊂ M.branch i := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨Set.sdiff_subset,?_⟩
    intro heq
    obtain ⟨x,hx⟩ := hDnonempty
    have hxC : x ∈ M.branch i \ D := by
      rw [heq]
      exact hDsub hx
    exact hxC.2 hx
  have hadj (j : I) (hij : H.Adj i j) :
      ∃ x ∈ M.branch i \ D, ∃ y ∈ M.branch j,
        K.Adj x y := by
    by_cases htouch : ∃ z ∈ M.branch j, z ∈ Z
    · obtain ⟨z,hzC,hzZ⟩ := hcenter
      obtain ⟨w,hwM,hwZ⟩ := htouch
      have hzw : z ≠ w := by
        intro heq
        exact (Set.disjoint_left.mp (M.disjoint hij.ne))
          hzC.1 (heq ▸ hwM)
      exact ⟨z,hzC,w,hwM,hclique z hzZ w hwZ hzw⟩
    · have hfree : ∀ y ∈ M.branch j, y ∉ Z := by
        intro y hy hyZ
        exact htouch ⟨y,hy,hyZ⟩
      obtain ⟨x,hx,y,hy,hxy⟩ := M.adjacent hij
      have hxNotD : x ∉ D :=
        fun hxD => hno j hij hfree x hxD y hy hxy
      exact ⟨x,⟨hx,hxNotD⟩,y,hy,hxy⟩
  exact minimal_rooted_model_no_trim M hmin i
    (M.branch i \ D) hproper hCconn hrootC hadj

end HadwigerLean.RootedDensity
