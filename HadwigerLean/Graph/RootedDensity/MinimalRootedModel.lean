import HadwigerLean.Graph.RootedDensity.Definitions
import Mathlib.Tactic

/-!
# A branch-minimal rooted torso model

Every finite rooted minor model has a companion minimizing the total
number of vertices in its branches. This is the extremal choice used
by reverse rigid truncation.
-/

namespace HadwigerLean.RootedDensity

universe u v

noncomputable def rootedModelOrder
    {V : Type u} {I : Type v} [Fintype V] [Fintype I]
    {G : SimpleGraph V} {H : SimpleGraph I} {root : I → V}
    (M : RootedMinorModel H G root) : ℕ :=
  ∑ i, (M.branch i).ncard

theorem exists_minimal_rooted_model
    {V : Type u} {I : Type v} [Fintype V] [Fintype I]
    {G : SimpleGraph V} {H : SimpleGraph I} {root : I → V}
    (hex : Nonempty (RootedMinorModel H G root)) :
    ∃ M : RootedMinorModel H G root,
      ∀ N : RootedMinorModel H G root,
        rootedModelOrder M ≤ rootedModelOrder N := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ M : RootedMinorModel H G root, rootedModelOrder M = n
  have hP : ∃ n, P n := by
    obtain ⟨M⟩ := hex
    exact ⟨rootedModelOrder M, M, rfl⟩
  obtain ⟨M,hM⟩ := Nat.find_spec hP
  refine ⟨M,?_⟩
  intro N
  have hmin := Nat.find_min' hP
    (show P (rootedModelOrder N) from ⟨N,rfl⟩)
  simpa only [hM] using hmin

end HadwigerLean.RootedDensity
