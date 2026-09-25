import HadwigerLean.Graph.RootedCliqueMinor.ABSeparation
import HadwigerLean.Graph.RootedCliqueMinor.DichotomyReduction

/-!
# Gluing a separator on the near shore across a critical separation

If Q separates original roots from the old boundary inside the near shore,
the whole far shore can be attached to the new far side. The glued boundary
has exactly |Q| vertices and retains the original far clique branch.
-/

namespace HadwigerLean

namespace VertexSeparation

/-- Glue a separation of the induced left shore to the original graph,
placing the original right shore on the new right side. -/
def glueLeft {V : Type*} [Fintype V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    (T : VertexSeparation (G.induce S.left))
    (hX : ∀ x : S.left, (x : V) ∈ S.right → x ∈ T.right) :
    VertexSeparation G where
  left := {x | ∃ hx : x ∈ S.left, (⟨x, hx⟩ : S.left) ∈ T.left}
  right := {x | x ∈ S.right ∨ ∃ hx : x ∈ S.left,
    (⟨x, hx⟩ : S.left) ∈ T.right}
  cover := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      have hx : x ∈ S.left ∪ S.right := by
        rw [S.cover]
        trivial
      rcases hx with hxL | hxR
      · have ht : (⟨x, hxL⟩ : S.left) ∈ T.left ∪ T.right := by
          rw [T.cover]
          trivial
        rcases ht with htL | htR
        · exact Or.inl ⟨hxL, htL⟩
        · exact Or.inr (Or.inr ⟨hxL, htR⟩)
      · exact Or.inr (Or.inl hxR)
  no_cross := by
    intro x y hxL hxNR hyR hyNL hxy
    obtain ⟨hxSL, hxTL⟩ := hxL
    have hxTR : (⟨x, hxSL⟩ : S.left) ∉ T.right := by
      intro h
      exact hxNR (Or.inr ⟨hxSL, h⟩)
    have hxNotSR : x ∉ S.right := by
      intro h
      exact hxNR (Or.inl h)
    have crossT (hySL : y ∈ S.left)
        (hyTR : (⟨y, hySL⟩ : S.left) ∈ T.right) : False := by
      have hyNotTL : (⟨y, hySL⟩ : S.left) ∉ T.left := by
        intro h
        exact hyNL ⟨hySL, h⟩
      exact T.no_cross hxTL hxTR hyTR hyNotTL hxy
    rcases hyR with hySR | ⟨hySL, hyTR⟩
    · by_cases hySL : y ∈ S.left
      · exact crossT hySL (hX ⟨y, hySL⟩ hySR)
      · exact S.no_cross hxSL hxNotSR hySR hySL hxy
    · exact crossT hySL hyTR

/-- The glued boundary is precisely the image of the new near-shore
boundary, so its order is unchanged. -/
theorem glueLeft_separatorFinset_card {V : Type*} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} (S : VertexSeparation G)
    [Fintype S.left] (T : VertexSeparation (G.induce S.left))
    (hX : ∀ x : S.left, (x : V) ∈ S.right → x ∈ T.right) :
    (S.glueLeft T hX).separatorFinset.card = T.separatorFinset.card := by
  classical
  have hsep : (S.glueLeft T hX).separatorFinset =
      T.separatorFinset.image Subtype.val := by
    ext x
    constructor
    · intro hx
      obtain ⟨⟨hxSL, hxTL⟩, hxR⟩ :=
        ((S.glueLeft T hX).mem_separatorFinset x).mp hx
      have hxTR : (⟨x, hxSL⟩ : S.left) ∈ T.right := by
        rcases hxR with hxSR | ⟨_, hxTR⟩
        · exact hX ⟨x, hxSL⟩ hxSR
        · exact hxTR
      exact Finset.mem_image.mpr
        ⟨⟨x, hxSL⟩, (T.mem_separatorFinset _).mpr ⟨hxTL, hxTR⟩, rfl⟩
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hyL, hyR⟩ := (T.mem_separatorFinset y).mp hy
      apply ((S.glueLeft T hX).mem_separatorFinset y).mpr
      exact ⟨⟨y.property, hyL⟩, Or.inr ⟨y.property, hyR⟩⟩
  rw [hsep]
  exact Finset.card_image_of_injective _ Subtype.val_injective

/-- The original strict far shore remains strictly far after gluing. -/
theorem strictRight_glueLeft {V : Type*} [Fintype V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    (T : VertexSeparation (G.induce S.left))
    (hX : ∀ x : S.left, (x : V) ∈ S.right → x ∈ T.right)
    {x : V} (hx : x ∈ S.strictRight) :
    x ∈ (S.glueLeft T hX).strictRight := by
  refine ⟨Or.inl hx.1, ?_⟩
  rintro ⟨hxL, _⟩
  exact hx.2 hxL

end VertexSeparation

/-- A small root-to-boundary separator inside the near shore yields the
small-separator outcome of the rooted-clique dichotomy. -/
theorem RootCliqueCriticalSeparation.outcome_of_left_ABSeparator
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r : ℕ}
    {root : Fin r → V}
    {M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots G (Set.range root))}
    {a b : V} (C : RootCliqueCriticalSeparation G root M a b)
    [Fintype C.sep.left] [DecidableEq C.sep.left]
    (A B Q : Finset C.sep.left)
    (hQ : Q.card < r)
    (hAB : SetMenger.IsABSeparator (G.induce C.sep.left) A B Q)
    (hA : ∀ i, (⟨root i, C.roots_left i⟩ : C.sep.left) ∈ A)
    (hB : ∀ x : C.sep.left, (x : V) ∈ C.sep.right → x ∈ B) :
    Nonempty (RootCliqueSeparatorOutcome G root M) := by
  let T := SetMenger.reachableSeparation (G.induce C.sep.left) A Q
  have hX : ∀ x : C.sep.left, (x : V) ∈ C.sep.right → x ∈ T.right := by
    intro x hx
    exact SetMenger.reachableSeparation_right_of_ABSeparator
      (G.induce C.sep.left) A Q B hAB x (hB x hx)
  let U := C.sep.glueLeft T hX
  have hsmall : U.separatorFinset.card < r := by
    rw [C.sep.glueLeft_separatorFinset_card T hX]
    rw [SetMenger.reachableSeparation_separatorFinset]
    exact hQ
  refine ⟨⟨U, hsmall, ?_, ?_⟩⟩
  · intro i
    exact ⟨C.roots_left i,
      SetMenger.reachableSeparation_left_of_mem
        (G.induce C.sep.left) A Q _ (hA i)⟩
  · obtain ⟨j, hj⟩ := C.branch_far
    exact ⟨j, fun x hx =>
      C.sep.strictRight_glueLeft T hX (hj hx)⟩

end HadwigerLean
