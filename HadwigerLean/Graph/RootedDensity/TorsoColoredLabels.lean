import HadwigerLean.Graph.RootedDensity.TorsoHangerInjection
import HadwigerLean.Graph.RootedDensity.ColoredAdhesionLabelsBoth

/-! The two-color matching labels the full adhesion of a rigid torso. -/

namespace HadwigerLean.RootedDensity

universe u v

noncomputable def torsoCenterAdhesion
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N) :
    TorsoTouchIndex S M ↪ S.right := {
  toFun := fun t =>
    ⟨(torsoCenterBoundary G S H root M hmin t : V),
      (chosenTorsoStar G S H root M hmin t).center_boundary⟩
  inj' := by
    intro a b hab
    apply torsoCenterBoundary_injective G S H root M hmin
    exact Subtype.ext (congrArg (fun z : S.right => (z : V)) hab)
}

noncomputable def torsoHangerAdhesion
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N) :
    TorsoHangerIndex G S H root M hmin ↪ S.right := {
  toFun := fun w =>
    ⟨(torsoHangerBoundary G S H root M hmin w : V), w.2.2.1⟩
  inj' := by
    intro a b hab
    apply torsoHangerBoundary_injective G S H root M hmin
    exact Subtype.ext (congrArg (fun z : S.right => (z : V)) hab)
}

/-- A chosen two-color matching of hanging pieces against boundary-free
labels gives an injective target labeling of the entire torso adhesion.
It assigns both colors of matched hanger vertices exactly as needed for
the rigid-side rooted model. -/
theorem exists_torso_colored_adhesion_labels
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    [DecidableEq (TorsoHangerIndex G S H root M hmin)]
    [DecidableEq (TorsoFreeIndex S M)]
    (hsize : (Linkedness.separationBoundaryFinset S).card ≤ Fintype.card I)
    (P : TwoColorMatching
      (TorsoHangerRel G S H root M hmin)) :
    let c := torsoCenterAdhesion G S H root M hmin
    let d := torsoHangerAdhesion G S H root M hmin
    let Z := Linkedness.separationBoundaryFinset S
    ∃ φ : ↥(Z : Set S.right) ↪ I,
      (∀ t : TorsoTouchIndex S M,
        ∀ hc : c t ∈ Z, φ ⟨c t, hc⟩ = t.1) ∧
      (∀ w : ↥P.color2Left,
        ∀ hw : d w.1 ∈ Z,
          φ ⟨d w.1, hw⟩ = (P.match2 w).1) ∧
      (∀ j : ↥P.color1Right,
        ∀ hj : d (P.match1 j) ∈ Z,
          φ ⟨d (P.match1 j), hj⟩ = j.1.1) := by
  classical
  letI : Fintype S.right := Fintype.ofFinite S.right
  letI : Finite (TorsoTouchIndex S M) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (TorsoTouchIndex S M) := Fintype.ofFinite _
  letI : Finite (TorsoFreeIndex S M) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (TorsoFreeIndex S M) := Fintype.ofFinite _
  letI : Finite (TorsoHangerIndex G S H root M hmin) :=
    Finite.of_injective (torsoHangerBoundary G S H root M hmin)
      (torsoHangerBoundary_injective G S H root M hmin)
  letI : Fintype (TorsoHangerIndex G S H root M hmin) := Fintype.ofFinite _
  let c := torsoCenterAdhesion G S H root M hmin
  let d := torsoHangerAdhesion G S H root M hmin
  let Z := Linkedness.separationBoundaryFinset S
  have hcZ : ∀ t : TorsoTouchIndex S M, c t ∈ Z := by
    intro t
    exact (Linkedness.mem_separationBoundaryFinset S (c t)).mpr
      (torsoCenterBoundary G S H root M hmin t).2
  have hdZ : ∀ w : TorsoHangerIndex G S H root M hmin,
      d w ∈ Z := by
    intro w
    exact (Linkedness.mem_separationBoundaryFinset S (d w)).mpr
      (torsoHangerBoundary G S H root M hmin w).2
  have hcd : ∀ t w, c t ≠ d w := by
    intro t w heq
    exact torsoCenter_ne_hangerBoundary G S H root M hmin t w
      (Subtype.ext (congrArg (fun z : S.right => (z : V)) heq))
  let owner : TorsoTouchIndex S M ↪ I :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let free : TorsoFreeIndex S M ↪ I :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hof : ∀ t j, owner t ≠ free j := by
    intro t j heq
    change t.1 = j.1 at heq
    exact j.2 (heq ▸ t.2)
  obtain ⟨φ, hcenter, htwo, hone⟩ :=
    exists_full_adhesion_labels_allColors Z hsize c owner d free
      hcZ hdZ hcd hof
      (TorsoHangerRel G S H root M hmin) P
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro t hc
    have h := hcenter t
    change φ ⟨c t, hcZ t⟩ = t.1 at h
    have heq : (⟨c t, hcZ t⟩ : ↥(Z : Set S.right)) = ⟨c t, hc⟩ :=
      Subtype.ext rfl
    simpa only [heq] using h
  · intro w hw
    have h := htwo w
    change φ ⟨d w.1, hdZ w.1⟩ = (P.match2 w).1 at h
    have heq : (⟨d w.1, hdZ w.1⟩ : ↥(Z : Set S.right)) = ⟨d w.1, hw⟩ :=
      Subtype.ext rfl
    simpa only [heq] using h
  · intro j hj
    have h := hone j
    change φ ⟨d (P.match1 j), hdZ (P.match1 j)⟩ = j.1.1 at h
    have heq : (⟨d (P.match1 j), hdZ (P.match1 j)⟩ : ↥(Z : Set S.right)) =
        ⟨d (P.match1 j), hj⟩ := Subtype.ext rfl
    simpa only [heq] using h

end HadwigerLean.RootedDensity



