import HadwigerLean.Inseparability.StageSourcePieces

/-!
# The source vertices lie in the old tangencies or child pieces
-/

namespace HadwigerLean.Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ciSourceFinset_subset_old_roots_union_children
    (p x : ℕ)
    (oldRoot : Fin p × Fin x → V)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (J : Fin p → Finset V)
    (hrootJ : ∀ i z, childRoot i z ∈ J i) :
    Finset.univ.image (ciSourceValue p x oldRoot childRoot) ⊆
      Finset.univ.image oldRoot ∪
        (Finset.univ : Finset (Fin p)).biUnion J := by
  intro v hv
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hv
  cases h : ciSourceRoleEquiv p x q with
  | inl z =>
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr
        ⟨z,Finset.mem_univ _,by simp [ciSourceValue,h]⟩
  | inr iz =>
      obtain ⟨i,z⟩ := iz
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr
        ⟨i,Finset.mem_univ i,by simpa [ciSourceValue,h] using hrootJ i z⟩

theorem ciSourceFinset_disjoint_of_old_and_children
    (p x : ℕ)
    (oldRoot : Fin p × Fin x → V)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (J : Fin p → Finset V)
    (hrootJ : ∀ i z, childRoot i z ∈ J i)
    (D : Finset V)
    (hOldD : Disjoint (Finset.univ.image oldRoot) D)
    (hJD : ∀ i, Disjoint (J i) D) :
    Disjoint
      (Finset.univ.image (ciSourceValue p x oldRoot childRoot)) D := by
  apply Finset.disjoint_left.mpr
  intro v hvZ hvD
  rcases Finset.mem_union.mp
      (ciSourceFinset_subset_old_roots_union_children p x oldRoot
        childRoot J hrootJ hvZ) with hvOld | hvJ
  · exact (Finset.disjoint_left.mp hOldD) hvOld hvD
  · obtain ⟨i,_,hvi⟩ := Finset.mem_biUnion.mp hvJ
    exact (Finset.disjoint_left.mp (hJD i)) hvi hvD

end HadwigerLean.Inseparability
