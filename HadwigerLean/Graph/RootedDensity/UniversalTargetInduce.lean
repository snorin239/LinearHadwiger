import HadwigerLean.Graph.RootedDensity.Universal
import Mathlib.Tactic

/-! Restricting the target graph preserves rooted universality. -/

namespace HadwigerLean.RootedDensity

universe u v

theorem UniversalAt.target_induce
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {X : Finset V}
    (h : UniversalAt G H X) (Y : Set W) [Fintype Y] :
    UniversalAt G (H.induce Y) X := by
  classical
  intro T root hinj hrange
  let Z : Finset W := T.image Subtype.val
  let e₀ : ↥(T : Set Y) → ↥(Z : Set W) := fun i =>
    ⟨(i.1 : W), Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩⟩
  have heinj : Function.Injective e₀ := by
    intro i j hij
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(Z : Set W) => (z : W)) hij
  have hesurj : Function.Surjective e₀ := by
    intro z
    obtain ⟨y, hy, hyz⟩ := Finset.mem_image.mp z.2
    refine ⟨⟨y, hy⟩, ?_⟩
    exact Subtype.ext hyz
  let e : ↥(T : Set Y) ≃ ↥(Z : Set W) :=
    Equiv.ofBijective e₀ ⟨heinj, hesurj⟩
  let rootZ : ↥(Z : Set W) → V := root ∘ e.symm
  have hinjZ : Function.Injective rootZ := hinj.comp e.symm.injective
  have hrangeZ : Set.range rootZ = (X : Set V) := by
    rw [← hrange]
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨e.symm z, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e i, by simp [rootZ]⟩
  obtain ⟨M⟩ := h Z rootZ hinjZ hrangeZ
  refine ⟨{
    toMinorModel := {
      branch := fun i => M.branch (e i)
      connected := fun i => M.connected (e i)
      disjoint := ?_
      adjacent := ?_
    }
    root_mem := ?_
  }⟩
  · intro i j hij
    exact M.disjoint (fun heq => hij (e.injective heq))
  · intro i j hij
    apply M.adjacent
    simpa [e, e₀, SimpleGraph.induce] using hij
  · intro i
    simpa [rootZ] using M.root_mem (e i)

end HadwigerLean.RootedDensity
