import HadwigerLean.Graph.RootedDensity.RigidLabels
import Mathlib.Tactic

/-! Restrict and relabel a far-shore model supplied by ambient target
universality to the labels used by a torso model. -/

namespace HadwigerLean.RootedDensity

universe u v w

def rooted_model_pullback_induced_target
    {I : Type u} {W : Type v} {V : Type w}
    [Fintype I] [Fintype W] [Fintype V]
    (H : SimpleGraph W) (J : SimpleGraph V)
    (e : I ↪ W) (T : Finset I) (Z : Finset W)
    (hTZ : ∀ i ∈ T, e i ∈ Z)
    (q : ↥(Z : Set W) → V)
    (N : RootedMinorModel (H.induce (Z : Set W)) J q) :
    RootedMinorModel ((H.comap e).induce (T : Set I)) J
      (fun i : ↥(T : Set I) => q ⟨e i.1, hTZ i.1 i.2⟩) := by
  classical
  let f : ↥(T : Set I) → ↥(Z : Set W) :=
    fun i => ⟨e i.1, hTZ i.1 i.2⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply e.injective
    exact congrArg Subtype.val hij
  exact {
    toMinorModel := {
      branch := fun i => N.branch (f i)
      connected := fun i => N.connected (f i)
      disjoint := by
        intro i j hij
        exact N.disjoint (fun h => hij (hf h))
      adjacent := by
        intro i j hij
        apply N.adjacent
        simpa [f, SimpleGraph.induce, SimpleGraph.comap] using hij
    }
    root_mem := fun i => N.root_mem (f i)
  }

end HadwigerLean.RootedDensity
