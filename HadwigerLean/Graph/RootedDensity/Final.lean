import HadwigerLean.Graph.RootedDensity.AmbientReverseProof
import HadwigerLean.Graph.RootedDensity.F1AmbientReverse

/-! The proved arbitrary-target rooted density theorem of Appendix F. -/

namespace HadwigerLean.RootedDensity

universe u v

theorem massedUniversal_sharp
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (c : ℝ) (hc : 1 < c)
    (hforces : DensityForcesMinor.{u,v} H c)
    (hh : 3 ≤ Fintype.card W) :
    MassedUniversalPrinciple.{u,v} H
      (12 * c + 5000 * (Fintype.card W : ℝ)) := by
  exact massedUniversal_of_ambientReverse H c hc hforces hh
    (ambientRigidReverse_proved H)

theorem rootedDensity_sharp
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (c : ℝ) (hc : 1 < c)
    (hforces : DensityForcesMinor.{u,v} H c)
    (hh : 3 ≤ Fintype.card W) :
    RootedDensityConclusion.{u,v} H
      (12 * c + 5000 * (Fintype.card W : ℝ)) := by
  exact rootedDensity_of_ambientReverse H c hc hforces hh
    (ambientRigidReverse_proved H)

end HadwigerLean.RootedDensity
