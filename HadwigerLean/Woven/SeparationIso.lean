import HadwigerLean.Bootstrap.Definitions
import Mathlib.Tactic

/-!
# Chromatic separability across graph isomorphisms
-/

namespace HadwigerLean
namespace Woven

universe u v

private noncomputable def separabilityInducedPreimageIso
    {V : Type u} {W : Type v}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (A : Set W) :
    G.induce (e ⁻¹' A) ≃g H.induce A := by
  let f : (e ⁻¹' A : Set V) ≃ A := {
    toFun := fun x => ⟨e x.1, x.2⟩
    invFun := fun y => ⟨e.symm y.1, by simpa using y.2⟩
    left_inv := by intro x; apply Subtype.ext; simp
    right_inv := by intro y; apply Subtype.ext; simp
  }
  exact {
    toEquiv := f
    map_rel_iff' := by
      intro x y
      exact e.map_rel_iff
  }

/-- Chromatic separability is invariant under a graph isomorphism. -/
theorem chromaticSeparable_of_iso
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (s : ℕ)
    (h : Bootstrap.ChromaticSeparable H s) :
    Bootstrap.ChromaticSeparable G s := by
  classical
  obtain ⟨A,B,hdis,hA,hB⟩ := h
  have hχ : chromatic G = chromatic H := by
    unfold chromatic
    exact congrArg ENat.toNat (SimpleGraph.chromaticNumber_congr e)
  have hχA : chromatic (G.induce (e ⁻¹' A)) =
      chromatic (H.induce A) := by
    unfold chromatic
    exact congrArg ENat.toNat
      (SimpleGraph.chromaticNumber_congr
        (separabilityInducedPreimageIso e A))
  have hχB : chromatic (G.induce (e ⁻¹' B)) =
      chromatic (H.induce B) := by
    unfold chromatic
    exact congrArg ENat.toNat
      (SimpleGraph.chromaticNumber_congr
        (separabilityInducedPreimageIso e B))
  refine ⟨e ⁻¹' A, e ⁻¹' B, ?_, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro x hxA hxB
    exact (Set.disjoint_left.mp hdis) hxA hxB
  · simpa only [hχ, hχA] using hA
  · simpa only [hχ, hχB] using hB

end Woven
end HadwigerLean
