import HadwigerLean.Graph.RootedDensity.RigidTruncation
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic

/-!
# Extending labels across a rigid adhesion

The prescribed labels of boundary vertices used by a torso model extend
to distinct labels of the entire adhesion whenever the target has enough
vertices. A permutation of the target aligns an arbitrary full embedding
with the prescribed partial injection.
-/

namespace HadwigerLean.RootedDensity

universe u v

/-- Extend an injective labeling of a subset of a finite adhesion to an
injective labeling of the whole adhesion. -/
theorem extend_adhesion_labels
    {V : Type u} {W : Type v} [Fintype V] [DecidableEq V] [Fintype W]
    (Z A : Finset V) (hAZ : A ⊆ Z)
    (f : ↥(A : Set V) → W) (hf : Function.Injective f)
    (hsize : Z.card ≤ Fintype.card W) :
    ∃ g : ↥(Z : Set V) ↪ W,
      ∀ a : ↥(A : Set V),
        g ⟨a.1, hAZ a.2⟩ = f a := by
  classical
  have hcard : Fintype.card ↥(Z : Set V) ≤ Fintype.card W := by
    simpa using hsize
  obtain ⟨g₀⟩ := Function.Embedding.nonempty_of_card_le hcard
  let eAZ : ↥(A : Set V) ↪ ↥(Z : Set V) := {
    toFun := fun a => ⟨a.1, hAZ a.2⟩
    inj' := by
      intro a b hab
      exact Subtype.ext (congrArg (fun z : ↥(Z : Set V) => (z : V)) hab)
  }
  have h0 : Function.Injective (fun a : ↥(A : Set V) => g₀ (eAZ a)) :=
    g₀.injective.comp eAZ.injective
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun a : ↥(A : Set V) => g₀ (eAZ a)) f h0 hf
  let g : ↥(Z : Set V) ↪ W := g₀.trans σ.toEmbedding
  refine ⟨g, ?_⟩
  intro a
  exact hσ a


/-- An injective assignment of target labels to every adhesion vertex
produces the corresponding rooted model on a universal rigid shore. -/
theorem rigid_shore_model_of_labels
    {V : Type u} {W : Type v} [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) (S : VertexSeparation G) (H : SimpleGraph W)
    (huni : UniversalAtRightShore H S)
    (φ : ↥(Linkedness.separationBoundaryFinset S : Set S.right) ↪ W) :
    ∃ (Y : Finset W) (root : ↥(Y : Set W) → S.right),
      Nonempty (RootedMinorModel (H.induce (Y : Set W))
        (G.induce S.right) root) ∧
      ∀ z : ↥(Linkedness.separationBoundaryFinset S : Set S.right),
        ∃ hz : φ z ∈ Y, root ⟨φ z, hz⟩ = z.1 := by
  classical
  let Z := Linkedness.separationBoundaryFinset S
  let Y : Finset W := Finset.univ.image φ
  have hY : (Y : Set W) = Set.range φ := by
    ext w
    simp [Y]
  let e₀ := Equiv.ofInjective φ φ.injective
  let e : ↥(Z : Set S.right) ≃ ↥(Y : Set W) :=
    e₀.trans (Equiv.setCongr hY.symm)
  let root : ↥(Y : Set W) → S.right := fun y => (e.symm y).1
  have hinj : Function.Injective root :=
    Subtype.val_injective.comp e.symm.injective
  have hrange : Set.range root = (Z : Set S.right) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact (e.symm y).2
    · intro hz
      exact ⟨e ⟨z, hz⟩, by simp [root]⟩
  have hm : Nonempty (RootedMinorModel (H.induce (Y : Set W))
      (G.induce S.right) root) := by
    change UniversalAt (G.induce S.right) H Z at huni
    exact huni Y root hinj hrange
  refine ⟨Y, root, hm, ?_⟩
  intro z
  have hz : φ z ∈ Y := by simp [Y]
  refine ⟨hz, ?_⟩
  have he : e z = ⟨φ z, hz⟩ := by
    apply Subtype.ext
    rfl
  change (e.symm ⟨φ z, hz⟩).1 = z.1
  rw [← he]
  simp

/-- A partial injective target labeling of adhesion vertices extends to a
rooted model in a universal rigid shore while preserving every prescribed
label and root. -/
theorem rigid_shore_model_of_partial_labels
    {V : Type u} {W : Type v} [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) (S : VertexSeparation G) (H : SimpleGraph W)
    (huni : UniversalAtRightShore H S)
    (A : Finset S.right)
    (hAZ : A ⊆ Linkedness.separationBoundaryFinset S)
    (f : ↥(A : Set S.right) → W) (hf : Function.Injective f)
    (hsize : (Linkedness.separationBoundaryFinset S).card ≤ Fintype.card W) :
    ∃ (Y : Finset W) (root : ↥(Y : Set W) → S.right),
      Nonempty (RootedMinorModel (H.induce (Y : Set W))
        (G.induce S.right) root) ∧
      ∀ a : ↥(A : Set S.right),
        ∃ ha : f a ∈ Y, root ⟨f a, ha⟩ = a.1 := by
  classical
  obtain ⟨φ, hφ⟩ := extend_adhesion_labels
    (Linkedness.separationBoundaryFinset S) A hAZ f hf hsize
  obtain ⟨Y, root, hm, hroot⟩ :=
    rigid_shore_model_of_labels G S H huni φ
  refine ⟨Y, root, hm, ?_⟩
  intro a
  have hz := hroot ⟨a.1, hAZ a.2⟩
  rw [hφ a] at hz
  exact hz

/-- Restrict a rooted model to any induced subgraph of its target. -/
def rooted_model_restrict
    {I : Type u} {V : Type v} {H : SimpleGraph I} {G : SimpleGraph V}
    {root : I → V} (M : RootedMinorModel H G root) (T : Set I) :
    RootedMinorModel (H.induce T) G (root ∘ Subtype.val) where
  toMinorModel := {
    branch := fun i => M.branch i.1
    connected := fun i => M.connected i.1
    disjoint := by
      intro i j hij
      exact M.disjoint (by
        intro heq
        apply hij
        exact Subtype.ext heq)
    adjacent := by
      intro i j hij
      exact M.adjacent hij
  }
  root_mem := fun i => M.root_mem i.1
/-- Restrict a rooted model of an induced target to a smaller set of labels. -/
def rooted_model_restrict_to_subset
    {I : Type u} {V : Type v} {H : SimpleGraph I} {G : SimpleGraph V}
    {Y : Set I} {root : Y → V}
    (M : RootedMinorModel (H.induce Y) G root)
    (T : Set I) (hTY : T ⊆ Y) :
    RootedMinorModel (H.induce T) G
      (fun i : T => root ⟨i.1, hTY i.2⟩) where
  toMinorModel := {
    branch := fun i => M.branch ⟨i.1, hTY i.2⟩
    connected := fun i => M.connected ⟨i.1, hTY i.2⟩
    disjoint := by
      intro i j hij
      apply M.disjoint
      intro heq
      apply hij
      exact Subtype.ext (congrArg (fun x : Y => (x : I)) heq)
    adjacent := by
      intro i j hij
      exact M.adjacent hij
  }
  root_mem := fun i => M.root_mem ⟨i.1, hTY i.2⟩end HadwigerLean.RootedDensity