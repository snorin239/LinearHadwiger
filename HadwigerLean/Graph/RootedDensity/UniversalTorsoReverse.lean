import HadwigerLean.Graph.RootedDensity.MinimalRootedModel
import HadwigerLean.Graph.Linkedness.RigidTorso
import Mathlib.Tactic

/-! Transporting universality across a near-side torso once individual
rooted models can be lifted through its universal far shore. -/

namespace HadwigerLean.RootedDensity

universe u v

theorem universalAt_of_torso_of_model_lift
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left] (H : SimpleGraph W) (X : Finset V)
    (hX : (X : Set V) ⊆ S.left)
    (htorso : UniversalAt (Linkedness.torsoGraph G S) H
      (Linkedness.torsoRootFinset S X))
    (hlift : ∀ (Y : Finset W) (root : ↥(Y : Set W) → S.left)
      (_M : RootedMinorModel (H.induce (Y : Set W))
        (Linkedness.torsoGraph G S) root),
      Nonempty (RootedMinorModel (H.induce (Y : Set W)) G
        (Subtype.val ∘ root))) :
    UniversalAt G H X := by
  classical
  intro Y root hinj hrange
  let nearRoot : ↥(Y : Set W) → S.left :=
    fun i => ⟨root i, hX (by
      rw [← hrange]
      exact Set.mem_range_self i)⟩
  have hnearInj : Function.Injective nearRoot := by
    intro i j hij
    apply hinj
    exact congrArg Subtype.val hij
  have hnearRange :
      Set.range nearRoot =
        (Linkedness.torsoRootFinset S X : Set S.left) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      apply (Linkedness.mem_torsoRootFinset S X _).2
      change root i ∈ (X : Set V)
      rw [← hrange]
      exact Set.mem_range_self i
    · intro hz
      have hx : (z : V) ∈ X :=
        (Linkedness.mem_torsoRootFinset S X _).1 hz
      change (z : V) ∈ (X : Set V) at hx
      rw [← hrange] at hx
      obtain ⟨i, hi⟩ := hx
      refine ⟨i, ?_⟩
      apply Subtype.ext
      exact hi
  obtain ⟨M⟩ := htorso Y nearRoot hnearInj hnearRange
  simpa [nearRoot, Function.comp_def] using hlift Y nearRoot M

end HadwigerLean.RootedDensity
