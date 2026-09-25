import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Tactic

/-! The finite two-color bipartite matching device of Appendix F.1. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- Two matchings with disjoint endpoints. Every left vertex not covered
by color 2 has all neighbors covered on the right by color 1. -/
structure TwoColorMatching {U : Type u} {W : Type v}
    (R : U → W → Prop) [DecidableEq U] [DecidableEq W] where
  color1Right : Finset W
  color2Left : Finset U
  match1 : ↥color1Right ↪ U
  match2 : ↥color2Left ↪ W
  match1_rel : ∀ w, R (match1 w) (w : W)
  match2_rel : ∀ u : ↥color2Left, R (u : U) (match2 u)
  match1_avoid_color2 : ∀ w, match1 w ∉ color2Left
  match2_avoid_color1 : ∀ u, match2 u ∉ color1Right
  cover : ∀ u, u ∉ color2Left → ∀ w, R u w → w ∈ color1Right

private def bipartiteCover {U : Type u} {W : Type v}
    (R : U → W → Prop) [DecidableEq U] [DecidableEq W]
    (A : Finset U) (B : Finset W) : Prop :=
  ∀ u w, R u w → u ∈ A ∨ w ∈ B

/-- Every finite bipartite relation has the two-color matching device.
The proof minimizes a vertex cover and applies Hall separately on its two
color classes. -/
theorem exists_twoColorMatching
    {U : Type u} {W : Type v} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W]
    (R : U → W → Prop) : Nonempty (TwoColorMatching R) := by
  classical
  let Cover := bipartiteCover R
  have hex : ∃ n : ℕ, ∃ A : Finset U, ∃ B : Finset W,
      Cover A B ∧ A.card + B.card = n := by
    refine ⟨(Finset.univ : Finset U).card, Finset.univ, ∅, ?_, by simp⟩
    intro u w _
    exact Or.inl (Finset.mem_univ u)
  obtain ⟨A, B, hcover, hsize⟩ := Nat.find_spec hex
  have hmin (A' : Finset U) (B' : Finset W)
      (hcover' : Cover A' B') : A.card + B.card ≤ A'.card + B'.card := by
    have hfind := Nat.find_min' hex
      (show ∃ C : Finset U, ∃ D : Finset W,
        Cover C D ∧ C.card + D.card = A'.card + B'.card from
          ⟨A', B', hcover', rfl⟩)
    simpa [hsize] using hfind
  let rel1 : ↥B → U → Prop := fun w u => u ∉ A ∧ R u (w : W)
  have hall1 : ∀ S : Finset ↥B,
      S.card ≤ ({u : U | ∃ w ∈ S, rel1 w u} : Finset U).card := by
    intro S
    let N : Finset U := {u : U | ∃ w ∈ S, rel1 w u}
    let S₀ : Finset W := S.image Subtype.val
    have hS₀B : S₀ ⊆ B := by
      intro w hw
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hw
      exact z.property
    have hcover' : Cover (A ∪ N) (B \ S₀) := by
      intro u w huw
      by_cases huA : u ∈ A
      · exact Or.inl (Finset.mem_union.mpr (Or.inl huA))
      have hwB := (hcover u w huw).resolve_left huA
      by_cases hwS : w ∈ S₀
      · obtain ⟨z, hzS, hzEq⟩ := Finset.mem_image.mp hwS
        have huN : u ∈ N := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, z, hzS, huA, ?_⟩
          simpa [hzEq] using huw
        exact Or.inl (Finset.mem_union.mpr (Or.inr huN))
      · exact Or.inr (Finset.mem_sdiff.mpr ⟨hwB, hwS⟩)
    have hS₀card : S₀.card = S.card := by
      exact Finset.card_image_of_injective _ Subtype.val_injective
    have hUnion : (A ∪ N).card ≤ A.card + N.card :=
      Finset.card_union_le A N
    have hDiff : (B \ S₀).card + S₀.card = B.card :=
      Finset.card_sdiff_add_card_eq_card hS₀B
    have hbound := hmin (A ∪ N) (B \ S₀) hcover'
    change S.card ≤ N.card
    omega
  let rel2 : ↥A → W → Prop := fun u w => w ∉ B ∧ R (u : U) w
  have hall2 : ∀ S : Finset ↥A,
      S.card ≤ ({w : W | ∃ u ∈ S, rel2 u w} : Finset W).card := by
    intro S
    let N : Finset W := {w : W | ∃ u ∈ S, rel2 u w}
    let S₀ : Finset U := S.image Subtype.val
    have hS₀A : S₀ ⊆ A := by
      intro u hu
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hu
      exact z.property
    have hcover' : Cover (A \ S₀) (B ∪ N) := by
      intro u w huw
      by_cases hwB : w ∈ B
      · exact Or.inr (Finset.mem_union.mpr (Or.inl hwB))
      have huA := (hcover u w huw).resolve_right hwB
      by_cases huS : u ∈ S₀
      · obtain ⟨z, hzS, hzEq⟩ := Finset.mem_image.mp huS
        have hwN : w ∈ N := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, z, hzS, hwB, ?_⟩
          simpa [hzEq] using huw
        exact Or.inr (Finset.mem_union.mpr (Or.inr hwN))
      · exact Or.inl (Finset.mem_sdiff.mpr ⟨huA, huS⟩)
    have hS₀card : S₀.card = S.card := by
      exact Finset.card_image_of_injective _ Subtype.val_injective
    have hUnion : (B ∪ N).card ≤ B.card + N.card :=
      Finset.card_union_le B N
    have hDiff : (A \ S₀).card + S₀.card = A.card :=
      Finset.card_sdiff_add_card_eq_card hS₀A
    have hbound := hmin (A \ S₀) (B ∪ N) hcover'
    change S.card ≤ N.card
    omega
  obtain ⟨f₁, hf₁, hrel₁⟩ :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective rel1).mp hall1
  obtain ⟨f₂, hf₂, hrel₂⟩ :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective rel2).mp hall2
  exact ⟨{
    color1Right := B
    color2Left := A
    match1 := ⟨f₁, hf₁⟩
    match2 := ⟨f₂, hf₂⟩
    match1_rel := fun w => (hrel₁ w).2
    match2_rel := fun u => (hrel₂ u).2
    match1_avoid_color2 := fun w => (hrel₁ w).1
    match2_avoid_color1 := fun u => (hrel₂ u).1
    cover := by
      intro u hu w huw
      exact (hcover u w huw).resolve_left hu
  }⟩

end HadwigerLean.RootedDensity


