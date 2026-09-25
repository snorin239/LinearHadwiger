import HadwigerLean.Graph.RootedDensity.ColoredMatching
import HadwigerLean.Graph.RootedDensity.RigidLabels

/-! Partial and full adhesion labels from the F.1 two-color matching. -/

namespace HadwigerLean.RootedDensity

universe u v w x y

/-- Label all used adhesion vertices: centers get their owner labels and
color-2 hangers get the corresponding matched boundary-free labels. -/
theorem exists_partial_adhesion_labels_of_twoColorMatching
    {C : Type u} {U : Type v} {W : Type w} {V : Type x} {I : Type y}
    [Fintype C] [Fintype U] [Fintype W] [Fintype V]
    [DecidableEq U] [DecidableEq W] [DecidableEq V]
    (Z : Finset V)
    (center : C ↪ V) (owner : C ↪ I)
    (hanger : U ↪ V) (free : W ↪ I)
    (hcZ : ∀ c, center c ∈ Z) (hhZ : ∀ u, hanger u ∈ Z)
    (hvertexDisjoint : ∀ c u, center c ≠ hanger u)
    (hlabelDisjoint : ∀ c w, owner c ≠ free w)
    (R : U → W → Prop) (M : TwoColorMatching R) :
    ∃ A : Finset V, ∃ f : ↥(A : Set V) → I,
      A ⊆ Z ∧ Function.Injective f ∧
      (∀ c : C, ∃ hc : center c ∈ A,
        f ⟨center c, hc⟩ = owner c) ∧
      (∀ u : ↥M.color2Left, ∃ hu : hanger u.1 ∈ A,
        f ⟨hanger u.1, hu⟩ = free (M.match2 u)) := by
  classical
  let e : C ⊕ ↥M.color2Left ↪ V := {
    toFun := fun x => match x with
      | .inl c => center c
      | .inr u => hanger u.1
    inj' := by
      intro x y hxy
      cases x with
      | inl c =>
        cases y with
        | inl d =>
          exact congrArg Sum.inl (center.injective hxy)
        | inr t =>
          exact False.elim (hvertexDisjoint c t.1 hxy)
      | inr s =>
        cases y with
        | inl d =>
          exact False.elim (hvertexDisjoint d s.1 hxy.symm)
        | inr t =>
          exact congrArg Sum.inr (Subtype.ext (hanger.injective hxy))
  }
  let label : C ⊕ ↥M.color2Left ↪ I := {
    toFun := fun x => match x with
      | .inl c => owner c
      | .inr u => free (M.match2 u)
    inj' := by
      intro x y hxy
      cases x with
      | inl c =>
        cases y with
        | inl d =>
          exact congrArg Sum.inl (owner.injective hxy)
        | inr t =>
          exact False.elim (hlabelDisjoint c (M.match2 t) hxy)
      | inr s =>
        cases y with
        | inl d =>
          exact False.elim (hlabelDisjoint d (M.match2 s) hxy.symm)
        | inr t =>
          exact congrArg Sum.inr (M.match2.injective (free.injective hxy))
  }
  let A : Finset V := Finset.univ.image e
  have hAZ : A ⊆ Z := by
    intro a ha
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
    cases x with
    | inl c => exact hcZ c
    | inr t => exact hhZ t.1
  have hA : (A : Set V) = Set.range e := by
    ext a
    simp [A]
  let eqv : (C ⊕ ↥M.color2Left) ≃ ↥(A : Set V) :=
    (Equiv.ofInjective e e.injective).trans (Equiv.setCongr hA.symm)
  let f : ↥(A : Set V) → I := fun a => label (eqv.symm a)
  have hf : Function.Injective f :=
    label.injective.comp eqv.symm.injective
  refine ⟨A, f, hAZ, hf, ?_, ?_⟩
  · intro c
    have hc : center c ∈ A :=
      Finset.mem_image.mpr ⟨Sum.inl c, Finset.mem_univ _, rfl⟩
    refine ⟨hc, ?_⟩
    have he : eqv (Sum.inl c) = ⟨center c, hc⟩ := by
      apply Subtype.ext
      rfl
    change label (eqv.symm ⟨center c, hc⟩) = owner c
    rw [← he]
    simp [label]
  · intro t
    have ht : hanger t.1 ∈ A :=
      Finset.mem_image.mpr ⟨Sum.inr t, Finset.mem_univ _, rfl⟩
    refine ⟨ht, ?_⟩
    have he : eqv (Sum.inr t) = ⟨hanger t.1, ht⟩ := by
      apply Subtype.ext
      rfl
    change label (eqv.symm ⟨hanger t.1, ht⟩) = free (M.match2 t)
    rw [← he]
    simp [label]

/-- Extend the center and color-2-hanger labels injectively across an
entire adhesion of size at most the target order. -/
theorem exists_full_adhesion_labels_of_twoColorMatching
    {C : Type u} {U : Type v} {W : Type w} {V : Type x} {I : Type y}
    [Fintype C] [Fintype U] [Fintype W] [Fintype V] [Fintype I]
    [DecidableEq U] [DecidableEq W] [DecidableEq V]
    (Z : Finset V) (hsize : Z.card ≤ Fintype.card I)
    (center : C ↪ V) (owner : C ↪ I)
    (hanger : U ↪ V) (free : W ↪ I)
    (hcZ : ∀ c, center c ∈ Z) (hhZ : ∀ u, hanger u ∈ Z)
    (hvertexDisjoint : ∀ c u, center c ≠ hanger u)
    (hlabelDisjoint : ∀ c w, owner c ≠ free w)
    (R : U → W → Prop) (M : TwoColorMatching R) :
    ∃ g : ↥(Z : Set V) ↪ I,
      (∀ c : C, g ⟨center c, hcZ c⟩ = owner c) ∧
      (∀ t : ↥M.color2Left,
        g ⟨hanger t.1, hhZ t.1⟩ = free (M.match2 t)) := by
  classical
  obtain ⟨A, f, hAZ, hf, hcenter, hhanger⟩ :=
    exists_partial_adhesion_labels_of_twoColorMatching
      Z center owner hanger free hcZ hhZ hvertexDisjoint hlabelDisjoint R M
  obtain ⟨g, hg⟩ := extend_adhesion_labels Z A hAZ f hf hsize
  refine ⟨g, ?_, ?_⟩
  · intro c
    obtain ⟨hc, hfc⟩ := hcenter c
    calc
      g ⟨center c, hcZ c⟩ = f ⟨center c, hc⟩ := hg ⟨center c, hc⟩
      _ = owner c := hfc
  · intro t
    obtain ⟨ht, hft⟩ := hhanger t
    calc
      g ⟨hanger t.1, hhZ t.1⟩ =
          f ⟨hanger t.1, ht⟩ := hg ⟨hanger t.1, ht⟩
      _ = free (M.match2 t) := hft

end HadwigerLean.RootedDensity

