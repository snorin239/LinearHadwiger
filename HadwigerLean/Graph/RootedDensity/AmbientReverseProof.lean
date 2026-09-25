import HadwigerLean.Graph.RootedDensity.TorsoColoredLift
import HadwigerLean.Graph.RootedDensity.UniversalTorsoReverse
import HadwigerLean.Graph.RootedDensity.F1AmbientReverse

/-! Unconditional reverse transport of partial rooted models across a
rigid torso, and the resulting Appendix F principle. -/

namespace HadwigerLean.RootedDensity

universe u v

theorem ambientRigidReverse_proved
    {W : Type v} [Fintype W] (H : SimpleGraph W) :
    AmbientRigidReversePrinciple.{u,v} H := by
  classical
  intro V instV decV G S instS X hX hsize huni htorso
  letI : Fintype V := instV
  letI : DecidableEq V := decV
  letI : Fintype S.left := instS
  apply universalAt_of_torso_of_model_lift G S H X hX htorso
  intro Y root M
  letI : DecidableEq ↥(Y : Set W) := Classical.decEq _
  let e : ↥(Y : Set W) ↪ W :=
    ⟨Subtype.val, Subtype.val_injective⟩
  obtain ⟨N,hmin⟩ := exists_minimal_rooted_model ⟨M⟩
  exact rooted_model_lift_torso_colored G S H e root N hmin huni hsize

end HadwigerLean.RootedDensity
