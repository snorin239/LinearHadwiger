import HadwigerLean.Inseparability.StageRawFromPieces
import HadwigerLean.Inseparability.StageNormalizeRoots
import HadwigerLean.Inseparability.StageTangentDeletion

/-!
# Reindex the previous CI stage into child-and-offset branch names

The nonzero raw construction uses `Fin p × Fin x`, whereas the stage
invariant stores the same `p*x` branches under a single `Fin` index.
-/

namespace HadwigerLean.Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {p x k m coreBound : ℕ}

def StageState.ciOldRoot
    (S : StageState G (p * x) k m coreBound) :
    Fin p × Fin x → V := S.root ∘ finProdFinEquiv

def StageState.ciOldModel
    (S : StageState G (p * x) k m coreBound) :
    RootedMinorModel
      (SimpleGraph.completeGraph (Fin p × Fin x)) G S.ciOldRoot :=
  rootedCliqueModel_reindex S.model finProdFinEquiv

theorem StageState.ciOldModel_tangent
    (S : StageState G (p * x) k m coreBound)
    (hrootregion : ∀ i, S.root i ∈ S.region) :
    ∀ z, S.ciOldModel.branch z ∩ (S.region : Set V) =
      {S.ciOldRoot z} := by
  intro z
  apply Set.Subset.antisymm
  · intro v hv
    obtain ⟨w,hw,hunique⟩ := S.tangent (finProdFinEquiv z)
    have hrootEq : S.root (finProdFinEquiv z) = w :=
      hunique _ ⟨S.model.root_mem _,hrootregion _⟩
    have hvEq : v = w := hunique v hv
    simp [StageState.ciOldRoot, hvEq, hrootEq]
  · intro v hv
    have hvEq : v = S.ciOldRoot z := by simpa using hv
    subst v
    exact ⟨S.ciOldModel.root_mem z,hrootregion _⟩

theorem StageState.ciOldModel_core_witness
    (S : StageState G (p * x) k m coreBound) :
    ∀ z w, z ≠ w →
      ∃ a ∈ S.ciOldModel.branch z,
        ∃ b ∈ S.ciOldModel.branch w,
          a ∈ S.core ∧ b ∈ S.core ∧ G.Adj a b := by
  intro z w hzw
  exact S.core_witness (finProdFinEquiv z) (finProdFinEquiv w)
    (fun h => hzw (finProdFinEquiv.injective h))

theorem StageState.ciOldModel_disjoint_piece
    (S : StageState G (p * x) k m coreBound)
    (hrootregion : ∀ i, S.root i ∈ S.region)
    (J : Finset V)
    (hJ : J ⊆ S.region \ S.tangentFinset) :
    Disjoint S.ciOldModel.toMinorModel.vertices (J : Set V) := by
  have hOldDis := S.model_disjoint_region_without_tangencies hrootregion
  apply Set.disjoint_left.mpr
  intro v hvA hvJ
  obtain ⟨z,hvz⟩ := Set.mem_iUnion.mp hvA
  have hvS : v ∈ S.model.toMinorModel.vertices :=
    Set.mem_iUnion.mpr ⟨finProdFinEquiv z,hvz⟩
  exact (Set.disjoint_left.mp hOldDis) hvS (hJ hvJ)


theorem StageState.ciOldRoot_image_eq_tangentFinset
    (S : StageState G (p * x) k m coreBound) :
    Finset.univ.image S.ciOldRoot = S.tangentFinset := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr
      ⟨finProdFinEquiv z,Finset.mem_univ _,rfl⟩
  · intro hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr
      ⟨finProdFinEquiv.symm i,Finset.mem_univ _,
        by change S.root (finProdFinEquiv (finProdFinEquiv.symm i)) = S.root i
           rw [Equiv.apply_symm_apply]⟩
end HadwigerLean.Inseparability




