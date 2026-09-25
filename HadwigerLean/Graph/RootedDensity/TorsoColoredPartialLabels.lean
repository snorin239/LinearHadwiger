import HadwigerLean.Graph.RootedDensity.TorsoColoredLabels
import Mathlib.Tactic

/-! The used adhesion vertices in a colored torso lift can be labeled in
a larger ambient target, without requiring enough torso labels for the
whole adhesion. -/

namespace HadwigerLean.RootedDensity

universe u v w

theorem exists_torso_colored_partial_labels
    {V : Type u} {I : Type v} {W : Type w}
    [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] [Fintype W]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    [DecidableEq (TorsoHangerIndex G S H root M hmin)]
    [DecidableEq (TorsoFreeIndex S M)]
    (P : TwoColorMatching
      (TorsoHangerRel G S H root M hmin))
    (e : I ↪ W) :
    ∃ A : Finset S.right, ∃ f : ↥(A : Set S.right) → W,
      A ⊆ Linkedness.separationBoundaryFinset S ∧
      Function.Injective f ∧
      (∀ t : TorsoTouchIndex S M,
        ∃ ht : torsoCenterAdhesion G S H root M hmin t ∈ A,
          f ⟨torsoCenterAdhesion G S H root M hmin t, ht⟩ = e t.1) ∧
      (∀ z : ↥P.color2Left,
        ∃ hz : torsoHangerAdhesion G S H root M hmin z.1 ∈ A,
          f ⟨torsoHangerAdhesion G S H root M hmin z.1, hz⟩ =
            e (P.match2 z).1) ∧
      (∀ j : ↥P.color1Right,
        ∃ hj : torsoHangerAdhesion G S H root M hmin
          (P.match1 j) ∈ A,
          f ⟨torsoHangerAdhesion G S H root M hmin
            (P.match1 j), hj⟩ = e j.1.1) := by
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
  have hdZ : ∀ z : TorsoHangerIndex G S H root M hmin,
      d z ∈ Z := by
    intro z
    exact (Linkedness.mem_separationBoundaryFinset S (d z)).mpr
      (torsoHangerBoundary G S H root M hmin z).2
  have hcd : ∀ t z, c t ≠ d z := by
    intro t z heq
    exact torsoCenter_ne_hangerBoundary G S H root M hmin t z
      (Subtype.ext (congrArg (fun x : S.right => (x : V)) heq))
  let owner : TorsoTouchIndex S M ↪ I :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let free : TorsoFreeIndex S M ↪ I :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hof : ∀ t j, owner t ≠ free j := by
    intro t j heq
    change t.1 = j.1 at heq
    exact j.2 (heq ▸ t.2)
  obtain ⟨A, f, hAZ, hf, hcenter, htwo, hone⟩ :=
    exists_partial_adhesion_labels_allColors Z c owner d free
      hcZ hdZ hcd hof (TorsoHangerRel G S H root M hmin) P
  refine ⟨A, e ∘ f, hAZ, e.injective.comp hf, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨ht, hft⟩ := hcenter t
    refine ⟨ht, ?_⟩
    change e (f ⟨c t, ht⟩) = e t.1
    exact congrArg e hft
  · intro z
    obtain ⟨hz, hfz⟩ := htwo z
    refine ⟨hz, ?_⟩
    change e (f ⟨d z.1, hz⟩) = e (P.match2 z).1
    exact congrArg e hfz
  · intro j
    obtain ⟨hj, hfj⟩ := hone j
    refine ⟨hj, ?_⟩
    change e (f ⟨d (P.match1 j), hj⟩) = e j.1.1
    exact congrArg e hfj

end HadwigerLean.RootedDensity
