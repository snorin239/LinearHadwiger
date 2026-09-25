import HadwigerLean.Graph.ChromaticConnectivity.Theorem
import HadwigerLean.Woven.Basic

/-!
# The sequential chromatic-inseparability invariant

A stage records a rooted clique model, a small core containing witnesses for
all clique edges and all tangencies, and a highly chromatic connected region.
The zero stage includes a genuine connected region obtained from the additive
chromatic connectivity theorem.
-/

namespace HadwigerLean
namespace Inseparability

universe u

/-- The paper's sequential stage invariant, with chromatic and core budgets
left as parameters for the numerical part of the induction. -/
structure StageState {V : Type u} (G : SimpleGraph V)
    (s k chromaticLoss coreBound : ℕ) where
  root : Fin s → V
  root_injective : Function.Injective root
  model : RootedMinorModel (SimpleGraph.completeGraph (Fin s)) G root
  core : Finset V
  region : Finset V
  region_connected : VertexConnected (G.induce (region : Set V)) k
  chromatic_reserve :
    chromatic G ≤ chromatic (G.induce (region : Set V)) + chromaticLoss
  core_card_le : core.card ≤ coreBound
  tangent : ∀ i, ∃! v, v ∈ model.branch i ∧ v ∈ region
  intersection_in_core :
    model.toMinorModel.vertices ∩ (region : Set V) ⊆ (core : Set V)
  core_witness : ∀ i j, i ≠ j →
    ∃ x ∈ model.branch i, ∃ y ∈ model.branch j,
      x ∈ core ∧ y ∈ core ∧ G.Adj x y

/-- The zero stage uses an empty model and empty core, but still extracts the
highly chromatic `k`-connected region required by the induction. -/
theorem exists_stage_zero
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k m : ℕ)
    (hk : 0 < k) (hχ : 7 * k ≤ chromatic G)
    (hm : 12 * k ≤ m) :
    Nonempty (StageState G 0 k (m / 2) 0) := by
  classical
  obtain ⟨H,hconn,hχH⟩ :=
    exists_chromatic_connected_induced G k hk hχ
  have hbudget : 6 * k ≤ m / 2 := by omega
  let root : Fin 0 → V := Fin.elim0
  let model : RootedMinorModel
      (SimpleGraph.completeGraph (Fin 0)) G root := {
    toMinorModel := {
      branch := Fin.elim0
      connected := fun i => i.elim0
      disjoint := by intro i; exact i.elim0
      adjacent := by intro i; exact i.elim0
    }
    root_mem := fun i => i.elim0
  }
  refine ⟨{
    root := root
    root_injective := by intro i; exact i.elim0
    model := model
    core := ∅
    region := H
    region_connected := hconn
    chromatic_reserve := ?_
    core_card_le := by simp
    tangent := by intro i; exact i.elim0
    intersection_in_core := ?_
    core_witness := by intro i; exact i.elim0
  }⟩
  · omega
  · intro x hx
    obtain ⟨i,_⟩ := Set.mem_iUnion.mp hx.1
    exact i.elim0

end Inseparability
end HadwigerLean

