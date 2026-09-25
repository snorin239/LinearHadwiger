import HadwigerLean.Graph.RootedDensity.SmallRoots
import HadwigerLean.Graph.RootedDensity.Reduction

/-! The two-label rooted-density conclusion needs only connectivity. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- Every 2-connected graph is universal for any two-label target at every
prescribed pair of roots, independent of the density parameter. -/
theorem rootedDensity_of_target_card_two
    {W : Type v} [Fintype W] (H : SimpleGraph W) (α : ℝ)
    (hh : Fintype.card W = 2) :
    RootedDensityConclusion.{u,v} H α := by
  intro V _ G X hX hconn _
  classical
  have hXtwo : X.card = 2 := hX.trans hh
  obtain ⟨x,y,hxy,hXpair⟩ := Finset.card_eq_two.mp hXtwo
  subst X
  have hconnG : G.Connected := hconn.connected (by omega)
  have hreach : G.Reachable x y := hconnG.preconnected x y
  intro Y root hinj hrange
  have hroot : ∀ i : ↥(Y : Set W), root i = x ∨ root i = y := by
    intro i
    have hi : root i ∈ Set.range root := ⟨i,rfl⟩
    rw [hrange] at hi
    simpa using hi
  exact rooted_minor_of_two_reachable G (H.induce (Y : Set W))
    x y hxy hreach root hroot hinj

end HadwigerLean.RootedDensity
