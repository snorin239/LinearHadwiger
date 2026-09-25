import HadwigerLean.Graph.RootedCliqueMinor.SeparatorRestriction

/-!
# Gluing a right-torso separation to the original graph

The original near shore is added wholesale to the near shore of a torso
separation. Its boundary is exactly the torso separation's boundary.
-/

namespace HadwigerLean

namespace VertexSeparation

/-- Glue a separation of the completed right torso back to the original
graph, assuming that the completed boundary lies on the torso's left. -/
def glueRight {V : Type*} [Fintype V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    (T : VertexSeparation S.torso)
    (hX : ∀ x : S.right, (x : V) ∈ S.left → x ∈ T.left) :
    VertexSeparation G where
  left := {x | x ∈ S.left ∨ ∃ hx : x ∈ S.right, (⟨x, hx⟩ : S.right) ∈ T.left}
  right := {x | ∃ hx : x ∈ S.right, (⟨x, hx⟩ : S.right) ∈ T.right}
  cover := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      have hxcover : x ∈ S.left ∪ S.right := by
        rw [S.cover]
        trivial
      rcases hxcover with hxL | hxR
      · exact Or.inl (Or.inl hxL)
      · have ht : (⟨x, hxR⟩ : S.right) ∈ T.left ∪ T.right := by
          rw [T.cover]
          trivial
        rcases ht with htL | htR
        · exact Or.inl (Or.inr ⟨hxR, htL⟩)
        · exact Or.inr ⟨hxR, htR⟩
  no_cross := by
    intro x y hxL hxNR hyR hyNL hxy
    obtain ⟨hyS, hyT⟩ := hyR
    have hyNotSL : y ∉ S.left := by
      intro h
      exact hyNL (Or.inl h)
    have hyNotTL : (⟨y, hyS⟩ : S.right) ∉ T.left := by
      intro h
      exact hyNL (Or.inr ⟨hyS, h⟩)
    have crossT (hxS : x ∈ S.right)
        (hxT : (⟨x, hxS⟩ : S.right) ∈ T.left) : False := by
      have hxNotTR : (⟨x, hxS⟩ : S.right) ∉ T.right := by
        intro h
        exact hxNR ⟨hxS, h⟩
      exact T.no_cross hxT hxNotTR hyT hyNotTL (Or.inl hxy)
    rcases hxL with hxSL | ⟨hxS, hxT⟩
    · by_cases hxS : x ∈ S.right
      · exact crossT hxS (hX ⟨x, hxS⟩ hxSL)
      · exact S.no_cross hxSL hxS hyS hyNotSL hxy
    · exact crossT hxS hxT

/-- Gluing does not change the boundary order. -/
theorem glueRight_separatorFinset_card {V : Type*} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} (S : VertexSeparation G)
    [Fintype S.right] (T : VertexSeparation S.torso)
    (hX : ∀ x : S.right, (x : V) ∈ S.left → x ∈ T.left) :
    (S.glueRight T hX).separatorFinset.card = T.separatorFinset.card := by
  classical
  have hsep : (S.glueRight T hX).separatorFinset =
      T.separatorFinset.image Subtype.val := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxL, hxR⟩ :=
        ((S.glueRight T hX).mem_separatorFinset x).mp hx
      obtain ⟨hxS, hxTR⟩ := hxR
      have hxTL : (⟨x, hxS⟩ : S.right) ∈ T.left := by
        rcases hxL with hxSL | ⟨_, hTL⟩
        · exact hX ⟨x, hxS⟩ hxSL
        · exact hTL
      apply Finset.mem_image.mpr
      exact ⟨⟨x, hxS⟩,
        (T.mem_separatorFinset _).mpr ⟨hxTL, hxTR⟩, rfl⟩
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hyL, hyR⟩ := (T.mem_separatorFinset y).mp hy
      apply ((S.glueRight T hX).mem_separatorFinset y).mpr
      exact ⟨Or.inr ⟨y.property, hyL⟩, ⟨y.property, hyR⟩⟩
  rw [hsep]
  exact Finset.card_image_of_injective _ Subtype.val_injective

/-- Strict far-side vertices of a torso separation remain strictly far
+after the separation is glued to the original graph. -/
theorem strictRight_glueRight {V : Type*} [Fintype V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    (T : VertexSeparation S.torso)
    (hX : ∀ x : S.right, (x : V) ∈ S.left → x ∈ T.left)
    (x : S.right) (hx : x ∈ T.strictRight) :
    (x : V) ∈ (S.glueRight T hX).strictRight := by
  refine ⟨⟨x.property, hx.1⟩, ?_⟩
  intro hxL
  rcases hxL with hxSL | ⟨_, hxTL⟩
  · exact hx.2 (hX x hxSL)
  · exact hx.2 hxTL
/-- If a restricted model branch is strictly beyond a torso separation,
its whole original branch is strictly beyond the glued separation. -/
theorem completed_branch_strictRight_glueRight
    {V : Type*} [Fintype V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    (R : Set V) (hR : R ⊆ S.left)
    {W : Type*} {H : SimpleGraph W}
    (M : MinorModel H (completeRoots G R))
    (hmeet : ∀ i, ∃ x ∈ M.branch i, x ∈ S.right)
    (T : VertexSeparation S.torso)
    (hX : ∀ x : S.right, (x : V) ∈ S.left → x ∈ T.left)
    (j : W)
    (hfar : (S.restrictCompletedRootModel R hR M hmeet).branch j ⊆
      T.strictRight) :
    M.branch j ⊆ (S.glueRight T hX).strictRight := by
  let S' : VertexSeparation (completeRoots G R) := S.completeLeftRoots R hR
  have hbranch : M.branch j ⊆ S.right := by
    intro v hv
    by_contra hnot
    obtain ⟨c, hcB, hcL, hcR⟩ :=
      S'.connected_set_meets_separator (M.branch j) (M.connected j)
        (hmeet j) ⟨v, hv, hnot⟩
    have hcT : (⟨c, hcR⟩ : S.right) ∈ T.strictRight := hfar hcB
    exact hcT.2 (hX ⟨c, hcR⟩ hcL)
  intro v hv
  let w : S.right := ⟨v, hbranch hv⟩
  have hw : w ∈ T.strictRight := hfar hv
  exact S.strictRight_glueRight T hX w hw
end VertexSeparation

end HadwigerLean
