import HadwigerLean.Graph.RootedDensity.Massed
import HadwigerLean.Graph.RootedDensity.Universal
import Mathlib.Tactic

/-! The exact massed-pair reduction for Appendix F's rooted-density theorem. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- The central structural assertion of Appendix F. It is kept as an
explicit proposition until its extremal proof is implemented. -/
def MassedUniversalPrinciple {W : Type v} [Fintype W]
    (H : SimpleGraph W) (α : ℝ) : Prop :=
  ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (X : Finset V),
    X.card ≤ Fintype.card W →
    MassedPair G (X : Set V) α →
    UniversalAt G H X

/-- The structural assertion is immediate for target graphs of order at
most one, independently of the massed-pair inequalities. -/
theorem massedUniversal_of_target_card_le_one
    {W : Type v} [Fintype W] (H : SimpleGraph W) (α : ℝ)
    (hh : Fintype.card W ≤ 1) :
    MassedUniversalPrinciple.{u,v} H α := by
  intro V _ G X hX _
  exact UniversalAt.of_card_le_one G H X (by omega)
/-- The structural massed-pair assertion yields the rooted-density bound
of Appendix F, including every assignment of the target labels. -/
theorem rootedDensity_of_massedUniversal
    {W : Type v} [Fintype W] (H : SimpleGraph W) (c : ℝ)
    (hh : 3 ≤ Fintype.card W) (hc : 0 ≤ c)
    (hmassed : MassedUniversalPrinciple.{u,v} H
      (12 * c + 5000 * (Fintype.card W : ℝ))) :
    RootedDensityConclusion.{u,v} H
      (12 * c + 5000 * (Fintype.card W : ℝ)) := by
  intro V _ G X hX hconn hedge
  have hm := massed_of_rooted_density G X (Fintype.card W) c
    hh hc hX hconn hedge
  exact hmassed V G X (by omega) hm

/-- The full-size conclusion supplies a model rooted at a prescribed
injective target-to-host map. -/
theorem rootedMinor_of_rootedDensity
    {W : Type v} [Fintype W] (H : SimpleGraph W) (α : ℝ)
    (h : RootedDensityConclusion.{u,v} H α)
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hconn : VertexConnected G (Fintype.card W))
    (hedge : α * (Fintype.card V : ℝ) ≤ (edgeCount G : ℝ))
    (root : W → V) (hroot : Function.Injective root) :
    Nonempty (RootedMinorModel H G root) := by
  classical
  let X : Finset V := Finset.univ.image root
  have hX : X.card = Fintype.card W := by
    rw [Finset.card_image_of_injective _ hroot]
    simp [X]
  have hrange : Set.range root = (X : Set V) := by
    ext x
    simp [X]
  exact (h V G X hX hconn hedge).full root hroot hrange

end HadwigerLean.RootedDensity

