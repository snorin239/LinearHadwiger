import HadwigerLean.Inseparability.StageDeletion
import Mathlib.Tactic

/-!
# Remove the old model's unique tangency vertices

The first move of a nonzero inseparability stage deletes exactly one vertex
per old branch from the highly connected region. The residual is disjoint
from the entire old model.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {s k m coreBound : ℕ}

def StageState.tangentFinset
    (S : StageState G s k m coreBound) : Finset V :=
  Finset.univ.image S.root

theorem StageState.tangentFinset_card
    (S : StageState G s k m coreBound) :
    S.tangentFinset.card = s := by
  classical
  simp [StageState.tangentFinset,
    Finset.card_image_of_injective _ S.root_injective]

theorem StageState.tangentFinset_subset_region
    (S : StageState G s k m coreBound)
    (hrootregion : ∀ i, S.root i ∈ S.region) :
    S.tangentFinset ⊆ S.region := by
  intro v hv
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
  exact hrootregion i

theorem StageState.model_disjoint_region_without_tangencies
    (S : StageState G s k m coreBound)
    (hrootregion : ∀ i, S.root i ∈ S.region) :
    Disjoint S.model.toMinorModel.vertices
      ((S.region \ S.tangentFinset : Finset V) : Set V) := by
  classical
  apply Set.disjoint_left.mpr
  intro v hvM hvR
  obtain ⟨i,hvi⟩ := Set.mem_iUnion.mp hvM
  have hvRegion : v ∈ S.region := (Finset.mem_sdiff.mp hvR).1
  obtain ⟨w, _, huniq⟩ := S.tangent i
  have hvEq : v = w := huniq v ⟨hvi,hvRegion⟩
  have hrEq : S.root i = w :=
    huniq (S.root i) ⟨S.model.root_mem i,hrootregion i⟩
  have hvD : v ∈ S.tangentFinset := by
    rw [hvEq, ← hrEq]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  exact (Finset.mem_sdiff.mp hvR).2 hvD

/-- The exact deletion package used before selecting the small connected
pieces for the next stage. -/
theorem StageState.after_remove_tangencies
    (S : StageState G s k m coreBound)
    (hrootregion : ∀ i, S.root i ∈ S.region)
    (ℓ : ℕ) (hbudget : s + ℓ ≤ k) :
    VertexConnected
      (G.induce ((S.region \ S.tangentFinset : Finset V) : Set V)) ℓ ∧
    chromatic G ≤
      chromatic (G.induce
        ((S.region \ S.tangentFinset : Finset V) : Set V)) + m + s ∧
    Disjoint S.model.toMinorModel.vertices
      ((S.region \ S.tangentFinset : Finset V) : Set V) := by
  classical
  have hD := S.after_delete S.tangentFinset
    (S.tangentFinset_subset_region hrootregion) ℓ
    (by rw [S.tangentFinset_card]; exact hbudget)
  refine ⟨hD.1, ?_, S.model_disjoint_region_without_tangencies hrootregion⟩
  rw [S.tangentFinset_card] at hD
  exact hD.2

end Inseparability
end HadwigerLean
