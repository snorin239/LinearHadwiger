import HadwigerLean.Inseparability.RawModelAssembly
import HadwigerLean.Inseparability.Stages
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Reindexing a raw CI model into a stage state

The geometric construction naturally uses old and new branch names.
This module converts those names to the Fin index expected by the
sequential invariant and transports the tangency and core witnesses.
-/

namespace HadwigerLean.Inseparability

/-- The old and new branch names form exactly the next stage's index set. -/
def ciStageIndexEquiv (p x : ℕ) :
    Fin ((p + 1) * x) ≃ Sum (Fin p × Fin x) (Fin x) :=
  (finCongr (by simp [add_mul] : (p + 1) * x = p * x + x)).trans
    ((finSumFinEquiv.symm).trans
      (Equiv.sumCongr finProdFinEquiv.symm (Equiv.refl (Fin x))))

/-- Package an assembled raw model as a sequential stage once the
chromatic, connectivity, and cardinality estimates have been proved. -/
theorem stageState_of_raw_model
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (p x k m coreBound : ℕ)
    (root : Sum (Fin p × Fin x) (Fin x) → V)
    (M : RootedMinorModel
      (SimpleGraph.completeGraph (Sum (Fin p × Fin x) (Fin x))) G root)
    (S H : Finset V)
    (hHconnected : VertexConnected (G.induce (H : Set V)) k)
    (hreserve : chromatic G ≤ chromatic (G.induce (H : Set V)) + m)
    (hcore : S.card ≤ coreBound)
    (htangent : ∀ i, M.branch i ∩ (H : Set V) = {root i})
    (hcoreWitness : ∀ i j, i ≠ j →
      ∃ a ∈ M.branch i, ∃ b ∈ M.branch j,
        a ∈ S ∧ b ∈ S ∧ G.Adj a b)
    (hintersection : M.toMinorModel.vertices ∩ (H : Set V) ⊆ (S : Set V)) :
    Nonempty (StageState G ((p + 1) * x) k m coreBound) := by
  let e := ciStageIndexEquiv p x
  let M' := rootedCliqueModel_reindex M e
  refine ⟨{
    root := root ∘ e
    root_injective := M'.root_injective
    model := M'
    core := S
    region := H
    region_connected := hHconnected
    chromatic_reserve := hreserve
    core_card_le := hcore
    tangent := ?_
    intersection_in_core := ?_
    core_witness := ?_
  }⟩
  · intro i
    refine ⟨root (e i), ?_, ?_⟩
    · have hmem : root (e i) ∈ M.branch (e i) ∩ (H : Set V) := by
        rw [htangent]
        simp
      exact hmem
    · intro v hv
      have hv' : v ∈ ({root (e i)} : Set V) := by
        rw [← htangent (e i)]
        exact hv
      simpa using hv'
  · intro v hv
    obtain ⟨i,hvi⟩ := Set.mem_iUnion.mp hv.1
    apply hintersection
    refine ⟨?_,hv.2⟩
    exact Set.mem_iUnion.mpr ⟨e i,hvi⟩
  · intro i j hij
    have heij : e i ≠ e j := fun h => hij (e.injective h)
    exact hcoreWitness (e i) (e j) heij

end HadwigerLean.Inseparability
