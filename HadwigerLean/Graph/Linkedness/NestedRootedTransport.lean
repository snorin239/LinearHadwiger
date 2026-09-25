import HadwigerLean.Graph.Linkedness.RootedLinkedIso
import Mathlib.Tactic

/-!
# Transporting rooted linkedness through two induced subgraphs
-/

namespace HadwigerLean
namespace Linkedness

/-- A rooted-linked core inside a residual induced graph remains a
rooted-linked induced core in the ambient graph. -/
theorem rootedLinked_induce_image_of_nested
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (R : Set V) (S : Finset R)
    (k : ℕ)
    (h : ∀ Y : Finset (S : Set R), Y.card ≤ 2 * k →
      RootedLinked ((G.induce R).induce (S : Set R)) Y) :
    let T : Finset V := S.image Subtype.val
    ∀ Y : Finset (T : Set V), Y.card ≤ 2 * k →
      RootedLinked (G.induce (T : Set V)) Y := by
  classical
  intro T Y hY
  have hTset : (T : Set V) = Subtype.val '' (S : Set R) := by
    ext v
    simp [T]
  let e : (G.induce R).induce (S : Set R) ≃g G.induce (T : Set V) := {
    toEquiv := (Equiv.Set.image (fun x : R => (x : V)) (S : Set R)
      Subtype.val_injective).trans (Equiv.setCongr hTset.symm)
    map_rel_iff' := by
      intro x y
      rfl
  }
  let X : Finset (S : Set R) := Y.image e.symm
  have hXcard : X.card ≤ 2 * k :=
    (Finset.card_image_le).trans hY
  have hXY : ∀ x, x ∈ X ↔ e x ∈ Y := by
    intro x
    constructor
    · intro hx
      obtain ⟨y,hy,hyeq⟩ := Finset.mem_image.mp hx
      have heq : y = e x := by
        calc
          y = e (e.symm y) := (e.apply_symm_apply y).symm
          _ = e x := congrArg e hyeq
      exact heq ▸ hy
    · intro hx
      exact Finset.mem_image.mpr ⟨e x,hx,e.symm_apply_apply x⟩
  exact rootedLinked_of_iso e X Y hXY (h X hXcard)

end Linkedness
end HadwigerLean
