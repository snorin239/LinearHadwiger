import HadwigerLean.Woven.ThreeChildResidualGN
import HadwigerLean.Bootstrap.Palette

/-!
# Chromatic cost of selecting parent roots and connector starts

The `a` roots and `2a` connector starts consume at most `3a` colors.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertex set left after removing every chosen parent root and start. -/
def parentResidual {a : ℕ} (root : Fin a → V)
    (start : Fin (2 * a) → V) : Finset V :=
  (Finset.univ.image root ∪ Finset.univ.image start)ᶜ

theorem root_not_mem_parentResidual {a : ℕ}
    (root : Fin a → V) (start : Fin (2 * a) → V)
    (i : Fin a) : root i ∉ parentResidual root start := by
  intro hi
  simp only [parentResidual, Finset.mem_compl] at hi
  exact hi (Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

theorem start_not_mem_parentResidual {a : ℕ}
    (root : Fin a → V) (start : Fin (2 * a) → V)
    (q : Fin (2 * a)) : start q ∉ parentResidual root start := by
  intro hq
  simp only [parentResidual, Finset.mem_compl] at hq
  exact hq (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩))

/-- Removing the parent roots and their `2a` connector starts lowers
chromatic number by at most `3a`. -/
theorem chromatic_le_parentResidual_add_three_mul
    (G : SimpleGraph V) {a : ℕ}
    (root : Fin a → V) (start : Fin (2 * a) → V) :
    chromatic G ≤
      chromatic (G.induce (parentResidual root start : Set V)) + 3 * a := by
  classical
  let R : Finset V := Finset.univ.image root
  let S : Finset V := Finset.univ.image start
  let D : Finset V := R ∪ S
  have hcover : (parentResidual root start : Set V) ∪
      (D : Set V) = Set.univ := by
    change ((Dᶜ : Finset V) : Set V) ∪ (D : Set V) = Set.univ
    ext x
    simp
  have hcolor := Bootstrap.chromatic_le_add_induce G
    (parentResidual root start : Set V) (D : Set V) hcover
  have hDχ : chromatic (G.induce (D : Set V)) ≤ D.card := by
    simpa using chromatic_le_card (G.induce (D : Set V))
  have hR : R.card ≤ a := by
    calc
      R.card ≤ (Finset.univ : Finset (Fin a)).card := Finset.card_image_le
      _ = a := by simp
  have hS : S.card ≤ 2 * a := by
    calc
      S.card ≤ (Finset.univ : Finset (Fin (2 * a))).card :=
        Finset.card_image_le
      _ = 2 * a := by simp
  have hD : D.card ≤ R.card + S.card := Finset.card_union_le R S
  omega

end Woven
end HadwigerLean
