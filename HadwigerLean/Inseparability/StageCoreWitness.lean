import HadwigerLean.Inseparability.StageCoreAssembly

/-!
# Core witnesses for the CI raw model

The old clique edges retain their old-core witnesses. Every child branch
lies in its small piece, so all child clique edges have witnesses in the
new core as well.
-/

namespace HadwigerLean.Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ciNextCore_old_witness
    (p x : ℕ) (G : SimpleGraph V)
    (oldCore : Finset V) (J : Fin p → Finset V) (D : Finset V)
    (root : CIRawIndex p x → V)
    (oldRoot : Fin p × Fin x → V)
    (A : RootedMinorModel
      (SimpleGraph.completeGraph (Fin p × Fin x)) G oldRoot)
    (hOld : ∀ z w, z ≠ w →
      ∃ a ∈ A.branch z, ∃ b ∈ A.branch w,
        a ∈ oldCore ∧ b ∈ oldCore ∧ G.Adj a b) :
    ∀ z w, z ≠ w →
      ∃ a ∈ A.branch z, ∃ b ∈ A.branch w,
        a ∈ ciNextCore p x oldCore J D root ∧
        b ∈ ciNextCore p x oldCore J D root ∧ G.Adj a b := by
  intro z w hzw
  obtain ⟨a,ha,b,hb,haCore,hbCore,hab⟩ := hOld z w hzw
  exact ⟨a,ha,b,hb,
    ciNextCore_old_subset p x oldCore J D root haCore,
    ciNextCore_old_subset p x oldCore J D root hbCore,hab⟩

theorem ciNextCore_child_branch_subset
    (p x : ℕ) (G : SimpleGraph V)
    (oldCore : Finset V) (J : Fin p → Finset V) (D : Finset V)
    (root : CIRawIndex p x → V)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (M : ∀ i, RootedMinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G (childRoot i))
    (hM : ∀ i, (M i).toMinorModel.vertices ⊆ (J i : Set V)) :
    ∀ i z, (M i).branch z ⊆
      (ciNextCore p x oldCore J D root : Set V) := by
  intro i z v hv
  exact ciNextCore_piece_subset p x oldCore J D root i
    (hM i (Set.mem_iUnion.mpr ⟨z,hv⟩))

end HadwigerLean.Inseparability
