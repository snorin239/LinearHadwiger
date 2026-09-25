import HadwigerLean.Graph.Linkedness.RootedLinkedIso
import Mathlib.Tactic

namespace HadwigerLean
namespace Linkedness

/-- Rooted linkedness of an ambient induced core transfers into a larger
induced region that contains that core. -/
theorem rootedLinked_nested_of_ambient
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (R : Set V) (J : Finset V)
    (hJR : ∀ x ∈ J, x ∈ R) (k : ℕ)
    (h : ∀ Y : Finset (J : Set V), Y.card ≤ 2 * k →
      RootedLinked (G.induce (J : Set V)) Y) :
    let T : Finset R := @Finset.subtype V R (Classical.decPred R) J
    ∀ Y : Finset (T : Set R), Y.card ≤ 2 * k →
      RootedLinked ((G.induce R).induce (T : Set R)) Y := by
  classical

  intro T Y hY
  have hJset : (J : Set V) = Subtype.val '' (T : Set R) := by
    ext v
    constructor
    · intro hv
      refine ⟨⟨v,hJR v hv⟩, ?_, rfl⟩
      exact (Finset.mem_subtype).2 hv
    · rintro ⟨x,hx,rfl⟩
      exact (Finset.mem_subtype).1 hx
  let e : (G.induce R).induce (T : Set R) ≃g G.induce (J : Set V) := {
    toEquiv := (Equiv.Set.image (fun x : R => (x : V)) (T : Set R)
      Subtype.val_injective).trans (Equiv.setCongr hJset.symm)
    map_rel_iff' := by
      intro x y
      rfl
  }
  let X : Finset (J : Set V) := Y.image e
  have hXcard : X.card ≤ 2 * k := (Finset.card_image_le).trans hY
  have hXY : ∀ x, x ∈ Y ↔ e x ∈ X := by
    intro x
    constructor
    · intro hx
      exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
    · intro hx
      obtain ⟨y,hy,hyeq⟩ := Finset.mem_image.mp hx
      exact e.injective hyeq ▸ hy
  have hXY' : ∀ x : (J : Set V), x ∈ X ↔ e.symm x ∈ Y := by
    intro x
    simpa only [e.apply_symm_apply] using (hXY (e.symm x)).symm
  exact rootedLinked_of_iso e.symm X Y hXY' (h X hXcard)

end Linkedness
end HadwigerLean
