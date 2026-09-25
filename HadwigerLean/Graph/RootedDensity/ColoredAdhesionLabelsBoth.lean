import HadwigerLean.Graph.RootedDensity.ColoredAdhesionLabels

/-! Adhesion labeling preserving both colors of the finite matching. -/

namespace HadwigerLean.RootedDensity

universe u v w x y

private def disjointSumEmbedding
    {A : Type u} {B : Type v} {T : Type x}
    (f : A ↪ T) (g : B ↪ T) (h : ∀ a b, f a ≠ g b) : A ⊕ B ↪ T where
  toFun := fun z => match z with
    | .inl a => f a
    | .inr b => g b
  inj' := by
    intro a b hab
    cases a with
    | inl x =>
      cases b with
      | inl y => exact congrArg Sum.inl (f.injective hab)
      | inr y => exact False.elim (h x y hab)
    | inr x =>
      cases b with
      | inl y => exact False.elim (h y x hab.symm)
      | inr y => exact congrArg Sum.inr (g.injective hab)

/-- On the hanger side, color 2 uses its own left vertex and color 1
uses the left endpoint of `match1`. These sets are disjoint. -/
private def hangerIndexEmbedding
    {U : Type u} {W : Type v} [DecidableEq U] [DecidableEq W]
    {R : U → W → Prop} (M : TwoColorMatching R) :
    ↥M.color2Left ⊕ ↥M.color1Right ↪ U where
  toFun := fun z => match z with
    | .inl a => a.1
    | .inr b => M.match1 b
  inj' := by
    intro a b hab
    cases a with
    | inl x =>
      cases b with
      | inl y => exact congrArg Sum.inl (Subtype.ext hab)
      | inr y =>
        change x.1 = M.match1 y at hab
        exact False.elim ((M.match1_avoid_color2 y) (hab ▸ x.2))
    | inr x =>
      cases b with
      | inl y =>
        change M.match1 x = y.1 at hab
        exact False.elim ((M.match1_avoid_color2 x) (hab.symm ▸ y.2))
      | inr y => exact congrArg Sum.inr (M.match1.injective hab)

/-- On the free-label side, color 2 uses the right endpoint of `match2`
and color 1 uses its own right vertex. These sets are disjoint. -/
private def freeIndexEmbedding
    {U : Type u} {W : Type v} [DecidableEq U] [DecidableEq W]
    {R : U → W → Prop} (M : TwoColorMatching R) :
    ↥M.color2Left ⊕ ↥M.color1Right ↪ W where
  toFun := fun z => match z with
    | .inl a => M.match2 a
    | .inr b => b.1
  inj' := by
    intro a b hab
    cases a with
    | inl x =>
      cases b with
      | inl y => exact congrArg Sum.inl (M.match2.injective hab)
      | inr y =>
        change M.match2 x = y.1 at hab
        exact False.elim ((M.match2_avoid_color1 x) (hab.symm ▸ y.2))
    | inr x =>
      cases b with
      | inl y =>
        change x.1 = M.match2 y at hab
        exact False.elim ((M.match2_avoid_color1 y) (hab ▸ x.2))
      | inr y => exact congrArg Sum.inr (Subtype.ext hab)

/-- Centers and both matched hanger colors form an injectively labeled
subset of the adhesion. -/
theorem exists_partial_adhesion_labels_allColors
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
        f ⟨hanger u.1, hu⟩ = free (M.match2 u)) ∧
      (∀ w : ↥M.color1Right, ∃ hw : hanger (M.match1 w) ∈ A,
        f ⟨hanger (M.match1 w), hw⟩ = free w.1) := by
  classical
  let hIdx := hangerIndexEmbedding M
  let fIdx := freeIndexEmbedding M
  let e : C ⊕ (↥M.color2Left ⊕ ↥M.color1Right) ↪ V :=
    disjointSumEmbedding center (hIdx.trans hanger)
      (fun c t => hvertexDisjoint c (hIdx t))
  let label : C ⊕ (↥M.color2Left ⊕ ↥M.color1Right) ↪ I :=
    disjointSumEmbedding owner (fIdx.trans free)
      (fun c t => hlabelDisjoint c (fIdx t))
  let A : Finset V := Finset.univ.image e
  have hAZ : A ⊆ Z := by
    intro a ha
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp ha
    cases t with
    | inl c => exact hcZ c
    | inr t =>
      cases t with
      | inl u => exact hhZ u.1
      | inr w => exact hhZ (M.match1 w)
  have hA : (A : Set V) = Set.range e := by
    ext a
    simp [A]
  let eqv : (C ⊕ (↥M.color2Left ⊕ ↥M.color1Right)) ≃ ↥(A : Set V) :=
    (Equiv.ofInjective e e.injective).trans (Equiv.setCongr hA.symm)
  let f : ↥(A : Set V) → I := fun a => label (eqv.symm a)
  have hf : Function.Injective f := label.injective.comp eqv.symm.injective
  have hlookup (t : C ⊕ (↥M.color2Left ⊕ ↥M.color1Right)) :
      ∃ ht : e t ∈ A, f ⟨e t, ht⟩ = label t := by
    have ht : e t ∈ A :=
      Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
    refine ⟨ht, ?_⟩
    have he : eqv t = ⟨e t, ht⟩ := by
      apply Subtype.ext
      rfl
    change label (eqv.symm ⟨e t, ht⟩) = label t
    rw [← he]
    simp
  refine ⟨A, f, hAZ, hf, ?_, ?_, ?_⟩
  · intro c
    simpa [e, label, disjointSumEmbedding] using hlookup (Sum.inl c)
  · intro t
    simpa [e, label, disjointSumEmbedding, hIdx, fIdx,
      hangerIndexEmbedding, freeIndexEmbedding] using
        hlookup (Sum.inr (Sum.inl t))
  · intro t
    simpa [e, label, disjointSumEmbedding, hIdx, fIdx,
      hangerIndexEmbedding, freeIndexEmbedding] using
        hlookup (Sum.inr (Sum.inr t))

/-- The partial labeling of centers and both matching colors extends
injectively to the full adhesion. -/
theorem exists_full_adhesion_labels_allColors
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
        g ⟨hanger t.1, hhZ t.1⟩ = free (M.match2 t)) ∧
      (∀ t : ↥M.color1Right,
        g ⟨hanger (M.match1 t), hhZ (M.match1 t)⟩ = free t.1) := by
  classical
  obtain ⟨A, f, hAZ, hf, hcenter, htwo, hone⟩ :=
    exists_partial_adhesion_labels_allColors
      Z center owner hanger free hcZ hhZ hvertexDisjoint hlabelDisjoint R M
  obtain ⟨g, hg⟩ := extend_adhesion_labels Z A hAZ f hf hsize
  refine ⟨g, ?_, ?_, ?_⟩
  · intro c
    obtain ⟨hc, hfc⟩ := hcenter c
    calc
      g ⟨center c, hcZ c⟩ = f ⟨center c, hc⟩ := hg ⟨center c, hc⟩
      _ = owner c := hfc
  · intro t
    obtain ⟨ht, hft⟩ := htwo t
    calc
      g ⟨hanger t.1, hhZ t.1⟩ = f ⟨hanger t.1, ht⟩ :=
        hg ⟨hanger t.1, ht⟩
      _ = free (M.match2 t) := hft
  · intro t
    obtain ⟨ht, hft⟩ := hone t
    calc
      g ⟨hanger (M.match1 t), hhZ (M.match1 t)⟩ =
          f ⟨hanger (M.match1 t), ht⟩ :=
        hg ⟨hanger (M.match1 t), ht⟩
      _ = free t.1 := hft

end HadwigerLean.RootedDensity

