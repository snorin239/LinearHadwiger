import HadwigerLean.Inseparability.Stages
import Mathlib.Tactic

/-!
# Use the unique region tangencies as the roots of a stage

The stage invariant records a rooted model and a unique tangency for each
branch. Re-rooting each branch at its tangency aligns the two roles without
changing any branch set, core, or region.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {s k m coreBound : ℕ}

noncomputable def StageState.tangentRoot
    (S : StageState G s k m coreBound) (i : Fin s) : V :=
  (S.tangent i).choose

theorem StageState.tangentRoot_mem_branch
    (S : StageState G s k m coreBound) (i : Fin s) :
    S.tangentRoot i ∈ S.model.branch i :=
  (S.tangent i).choose_spec.1.1

theorem StageState.tangentRoot_mem_region
    (S : StageState G s k m coreBound) (i : Fin s) :
    S.tangentRoot i ∈ S.region :=
  (S.tangent i).choose_spec.1.2

theorem StageState.tangentRoot_mem_core
    (S : StageState G s k m coreBound) (i : Fin s) :
    S.tangentRoot i ∈ S.core :=
  S.intersection_in_core
    ⟨Set.mem_iUnion.mpr ⟨i,S.tangentRoot_mem_branch i⟩,
      S.tangentRoot_mem_region i⟩

theorem StageState.tangentRoot_injective
    (S : StageState G s k m coreBound) :
    Function.Injective S.tangentRoot := by
  intro i j heq
  by_contra hij
  exact (Set.disjoint_left.mp (S.model.disjoint hij))
    (S.tangentRoot_mem_branch i)
    (heq ▸ S.tangentRoot_mem_branch j)

/-- Re-root a stage model at its actual tangency vertices. The model's
branches and all budgets are unchanged. -/
noncomputable def StageState.normalizeRoots
    (S : StageState G s k m coreBound) :
    StageState G s k m coreBound where
  root := S.tangentRoot
  root_injective := S.tangentRoot_injective
  model := {
    toMinorModel := S.model.toMinorModel
    root_mem := S.tangentRoot_mem_branch
  }
  core := S.core
  region := S.region
  region_connected := S.region_connected
  chromatic_reserve := S.chromatic_reserve
  core_card_le := S.core_card_le
  tangent := S.tangent
  intersection_in_core := S.intersection_in_core
  core_witness := S.core_witness

theorem StageState.normalizeRoots_root_in_core
    (S : StageState G s k m coreBound) (i : Fin s) :
    S.normalizeRoots.root i ∈ S.normalizeRoots.core :=
  S.tangentRoot_mem_core i

theorem StageState.normalizeRoots_root_in_region
    (S : StageState G s k m coreBound) (i : Fin s) :
    S.normalizeRoots.root i ∈ S.normalizeRoots.region :=
  S.tangentRoot_mem_region i

end Inseparability
end HadwigerLean
