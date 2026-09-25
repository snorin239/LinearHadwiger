import HadwigerLean.Inseparability.StageSourceEnumeration
import HadwigerLean.Graph.RootedMinor
import Mathlib.Tactic

/-!
# Source enumeration from disjoint rooted models

The old model and the child models themselves supply the injectivity and
cross-model disjointness needed to enumerate all reserved starts.
-/

namespace HadwigerLean.Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ciSourceRole_injective_of_models
    (p x : ℕ) (G : SimpleGraph V)
    (oldRoot : Fin p × Fin x → V)
    (A : RootedMinorModel
      (SimpleGraph.completeGraph (Fin p × Fin x)) G oldRoot)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (M : ∀ i, RootedMinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G (childRoot i))
    (hAChild : ∀ i,
      Disjoint A.toMinorModel.vertices (M i).toMinorModel.vertices)
    (hChildChild : ∀ i j, i ≠ j →
      Disjoint (M i).toMinorModel.vertices
        (M j).toMinorModel.vertices) :
    Function.Injective
      (fun q : CISourceRole p x =>
        match q with
        | .inl z => oldRoot z
        | .inr (i,z) => childRoot i z) := by
  intro q q' h
  cases q with
  | inl z =>
      cases q' with
      | inl w =>
          exact congrArg Sum.inl (A.root_injective h)
      | inr iw =>
          obtain ⟨i,w⟩ := iw
          change oldRoot z = childRoot i w at h
          have hz : oldRoot z ∈ A.toMinorModel.vertices :=
            Set.mem_iUnion.mpr ⟨z,A.root_mem z⟩
          have hw : childRoot i w ∈ (M i).toMinorModel.vertices :=
            Set.mem_iUnion.mpr ⟨w,(M i).root_mem w⟩
          exact False.elim ((Set.disjoint_left.mp (hAChild i))
            (h ▸ hz) hw)
  | inr iz =>
      obtain ⟨i,z⟩ := iz
      cases q' with
      | inl w =>
          change childRoot i z = oldRoot w at h
          have hz : childRoot i z ∈ (M i).toMinorModel.vertices :=
            Set.mem_iUnion.mpr ⟨z,(M i).root_mem z⟩
          have hw : oldRoot w ∈ A.toMinorModel.vertices :=
            Set.mem_iUnion.mpr ⟨w,A.root_mem w⟩
          exact False.elim ((Set.disjoint_left.mp (hAChild i))
            hw (h ▸ hz))
      | inr jw =>
          obtain ⟨j,w⟩ := jw
          by_cases hij : i = j
          · subst j
            have hzw : z = w := (M i).root_injective h
            simp [hzw]
          · change childRoot i z = childRoot j w at h
            have hz : childRoot i z ∈ (M i).toMinorModel.vertices :=
              Set.mem_iUnion.mpr ⟨z,(M i).root_mem z⟩
            have hw : childRoot j w ∈ (M j).toMinorModel.vertices :=
              Set.mem_iUnion.mpr ⟨w,(M j).root_mem w⟩
            exact False.elim ((Set.disjoint_left.mp
              (hChildChild i j hij)) (h ▸ hz) hw)

theorem ciSourceValue_injective_of_models
    (p x : ℕ) (G : SimpleGraph V)
    (oldRoot : Fin p × Fin x → V)
    (A : RootedMinorModel
      (SimpleGraph.completeGraph (Fin p × Fin x)) G oldRoot)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (M : ∀ i, RootedMinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G (childRoot i))
    (hAChild : ∀ i,
      Disjoint A.toMinorModel.vertices (M i).toMinorModel.vertices)
    (hChildChild : ∀ i j, i ≠ j →
      Disjoint (M i).toMinorModel.vertices
        (M j).toMinorModel.vertices) :
    Function.Injective (ciSourceValue p x oldRoot childRoot) := by
  intro k l h
  apply (ciSourceRoleEquiv p x).injective
  exact ciSourceRole_injective_of_models p x G oldRoot A childRoot M
    hAChild hChildChild h

/-- The old and child rooted models determine the exact finite source
set and its path-slot enumeration. -/
noncomputable def ciSourceEquivOfModels
    (p x : ℕ) (G : SimpleGraph V)
    (oldRoot : Fin p × Fin x → V)
    (A : RootedMinorModel
      (SimpleGraph.completeGraph (Fin p × Fin x)) G oldRoot)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (M : ∀ i, RootedMinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G (childRoot i))
    (hAChild : ∀ i,
      Disjoint A.toMinorModel.vertices (M i).toMinorModel.vertices)
    (hChildChild : ∀ i j, i ≠ j →
      Disjoint (M i).toMinorModel.vertices
        (M j).toMinorModel.vertices) :
    Fin (3 * p * x) ≃
      (Finset.univ.image (ciSourceValue p x oldRoot childRoot) : Finset V) := by
  classical
  let f : Fin (3 * p * x) →
      (Finset.univ.image (ciSourceValue p x oldRoot childRoot) : Finset V) :=
    fun q => ⟨ciSourceValue p x oldRoot childRoot q,
      Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro q r h
    exact ciSourceValue_injective_of_models p x G oldRoot A childRoot M
      hAChild hChildChild (congrArg Subtype.val h)
  · rintro ⟨v,hv⟩
    obtain ⟨q,-,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨q,rfl⟩

@[simp] theorem ciSourceEquivOfModels_apply
    (p x : ℕ) (G : SimpleGraph V)
    (oldRoot : Fin p × Fin x → V)
    (A : RootedMinorModel
      (SimpleGraph.completeGraph (Fin p × Fin x)) G oldRoot)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (M : ∀ i, RootedMinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G (childRoot i))
    (hAChild : ∀ i,
      Disjoint A.toMinorModel.vertices (M i).toMinorModel.vertices)
    (hChildChild : ∀ i j, i ≠ j →
      Disjoint (M i).toMinorModel.vertices
        (M j).toMinorModel.vertices)
    (q : Fin (3 * p * x)) :
    ((ciSourceEquivOfModels p x G oldRoot A childRoot M
      hAChild hChildChild q) : V) =
        ciSourceValue p x oldRoot childRoot q := by
  rfl

theorem ciSourceEquivOfModels_old
    (p x : ℕ) (G : SimpleGraph V)
    (oldRoot : Fin p × Fin x → V)
    (A : RootedMinorModel
      (SimpleGraph.completeGraph (Fin p × Fin x)) G oldRoot)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (M : ∀ i, RootedMinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G (childRoot i))
    (hAChild : ∀ i,
      Disjoint A.toMinorModel.vertices (M i).toMinorModel.vertices)
    (hChildChild : ∀ i j, i ≠ j →
      Disjoint (M i).toMinorModel.vertices
        (M j).toMinorModel.vertices)
    (i : Fin p) (r : Fin x) :
    ((ciSourceEquivOfModels p x G oldRoot A childRoot M
      hAChild hChildChild
      (ciSourceBlock p x ⟨i.val, by omega⟩ r)) : V) =
        oldRoot (i,r) := by
  rw [ciSourceEquivOfModels_apply]
  exact ciSourceValue_old p x oldRoot childRoot i r

theorem ciSourceEquivOfModels_child
    (p x : ℕ) (G : SimpleGraph V)
    (oldRoot : Fin p × Fin x → V)
    (A : RootedMinorModel
      (SimpleGraph.completeGraph (Fin p × Fin x)) G oldRoot)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (M : ∀ i, RootedMinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G (childRoot i))
    (hAChild : ∀ i,
      Disjoint A.toMinorModel.vertices (M i).toMinorModel.vertices)
    (hChildChild : ∀ i j, i ≠ j →
      Disjoint (M i).toMinorModel.vertices
        (M j).toMinorModel.vertices)
    (i : Fin p) (d : Fin 2) (r : Fin x) :
    ((ciSourceEquivOfModels p x G oldRoot A childRoot M
      hAChild hChildChild
      (ciSourceBlock p x ⟨p + 2 * i.val + d.val, by omega⟩ r)) : V) =
        childRoot i (d,r) := by
  rw [ciSourceEquivOfModels_apply]
  exact ciSourceValue_child p x oldRoot childRoot i d r

theorem ciSourceFinset_card_of_models
    (p x : ℕ) (G : SimpleGraph V)
    (oldRoot : Fin p × Fin x → V)
    (A : RootedMinorModel
      (SimpleGraph.completeGraph (Fin p × Fin x)) G oldRoot)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (M : ∀ i, RootedMinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G (childRoot i))
    (hAChild : ∀ i,
      Disjoint A.toMinorModel.vertices (M i).toMinorModel.vertices)
    (hChildChild : ∀ i j, i ≠ j →
      Disjoint (M i).toMinorModel.vertices
        (M j).toMinorModel.vertices) :
    (Finset.univ.image (ciSourceValue p x oldRoot childRoot)).card =
      3 * p * x := by
  have h := Fintype.card_congr
    (ciSourceEquivOfModels p x G oldRoot A childRoot M
      hAChild hChildChild)
  simpa only [Fintype.card_coe, Fintype.card_fin] using h.symm

end HadwigerLean.Inseparability
