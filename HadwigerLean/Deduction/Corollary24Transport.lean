import HadwigerLean.Deduction.ExternalInputs
import HadwigerLean.Graph.MinorFree
import Mathlib.Tactic

namespace HadwigerLean.Deduction

open HadwigerLean.Bootstrap

universe u v

/-- An isomorphism restricts to an isomorphism of any induced set and its
preimage. -/
noncomputable def inducedPreimageIso
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
    (h : ChromaticSeparable H s) :
    ChromaticSeparable G s := by
  classical
  obtain ⟨A,B,hdis,hA,hB⟩ := h
  have hχ : chromatic G = chromatic H := by
    unfold chromatic
    exact congrArg ENat.toNat (SimpleGraph.chromaticNumber_congr e)
  have hχA : chromatic (G.induce (e ⁻¹' A)) =
      chromatic (H.induce A) := by
    unfold chromatic
    exact congrArg ENat.toNat
      (SimpleGraph.chromaticNumber_congr (inducedPreimageIso e A))
  have hχB : chromatic (G.induce (e ⁻¹' B)) =
      chromatic (H.induce B) := by
    unfold chromatic
    exact congrArg ENat.toNat
      (SimpleGraph.chromaticNumber_congr (inducedPreimageIso e B))
  refine ⟨e ⁻¹' A, e ⁻¹' B, ?_, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro x hxA hxB
    exact (Set.disjoint_left.mp hdis) hxA hxB
  · simpa only [hχ, hχA] using hA
  · simpa only [hχ, hχB] using hB

/-- The Corollary 24 separation premise passes to every induced graph. -/
theorem outerSeparation_induce
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (T d : ℕ)
    (h : OuterSeparation G T d) (U : Set V) [Fintype U] :
    OuterSeparation (G.induce U) T d := by
  classical
  intro a hscale hcut Y
  let Z : Set V := Subtype.val '' Y
  let e : ((G.induce U).induce Y) ≃g G.induce Z := {
    toEquiv := Equiv.Set.image (fun x : U => (x : V)) Y
      Subtype.val_injective
    map_rel_iff' := by intro x y; rfl
  }
  have hχ : chromatic ((G.induce U).induce Y) =
      chromatic (G.induce Z) := by
    unfold chromatic
    exact congrArg ENat.toNat (SimpleGraph.chromaticNumber_congr e)
  intro hminor hlarge
  have hminorZ : ¬ HasCliqueMinor (G.induce Z) (14 * a) := by
    intro hminor'
    exact hminor (hasCliqueMinor_map e.symm.toHom e.symm.injective hminor')
  have hlargeZ : 28 * d * a < chromatic (G.induce Z) := by
    rwa [hχ] at hlarge
  have hsepZ := h a hscale hcut Z hminorZ hlargeZ
  exact chromaticSeparable_of_iso e (14 * d * a) hsepZ

end HadwigerLean.Deduction
