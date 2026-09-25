import HadwigerLean.Inseparability.StageSourceModels

/-!
# Placement of the reserved CI source set

The source set is exactly the old tangencies and the chosen child roots.
Pointwise region membership and avoidance transfer to the whole set.
-/

namespace HadwigerLean.Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ciSourceFinset_subset
    (p x : ℕ)
    (oldRoot : Fin p × Fin x → V)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (R : Finset V)
    (hOld : ∀ z, oldRoot z ∈ R)
    (hChild : ∀ i z, childRoot i z ∈ R) :
    Finset.univ.image (ciSourceValue p x oldRoot childRoot) ⊆ R := by
  intro v hv
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hv
  cases h : ciSourceRoleEquiv p x k with
  | inl z =>
      simpa [ciSourceValue, h] using hOld z
  | inr iz =>
      obtain ⟨i,z⟩ := iz
      simpa [ciSourceValue, h] using hChild i z

theorem ciSourceFinset_disjoint
    (p x : ℕ)
    (oldRoot : Fin p × Fin x → V)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (D : Finset V)
    (hOld : ∀ z, oldRoot z ∉ D)
    (hChild : ∀ i z, childRoot i z ∉ D) :
    Disjoint (Finset.univ.image
      (ciSourceValue p x oldRoot childRoot)) D := by
  apply Finset.disjoint_left.mpr
  intro v hvZ hvD
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hvZ
  cases h : ciSourceRoleEquiv p x k with
  | inl z =>
      have hnot : ciSourceValue p x oldRoot childRoot k ∉ D := by
        simpa [ciSourceValue, h] using hOld z
      exact hnot hvD
  | inr iz =>
      obtain ⟨i,z⟩ := iz
      have hnot : ciSourceValue p x oldRoot childRoot k ∉ D := by
        simpa [ciSourceValue, h] using hChild i z
      exact hnot hvD

end HadwigerLean.Inseparability

