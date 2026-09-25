import HadwigerLean.Graph.RootedDensity.RigidAdhesionReduction
import HadwigerLean.Graph.RootedDensity.UniversalRigidFanNear
import HadwigerLean.Graph.RootedDensity.UniversalRigidSaturated

/-! The F.a adhesion reduction with both fan transports discharged. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- Any H-rigid shore containing the roots can be ruled out once
lower-adhesion H-rigid shores have been excluded. -/
theorem no_rigid_of_lower_rigid_exclusion
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (X : Finset V)
    (hbad : ¬ UniversalAt G H X)
    (hlower : ∀ S : VertexSeparation G,
      (X : Set V) ⊆ S.left →
      S.strictRight.Nonempty →
      Nat.card S.separator < X.card →
      UniversalAtRightShore H S → False) :
    ∀ S : VertexSeparation G,
      (X : Set V) ⊆ S.left →
      RigidSeparation H S → False := by
  classical
  apply no_rigid_of_lower_rigid_exclusion_and_fans G H X hbad hlower
  · intro S _ hroot n P L hstarts hfinish hsize huni
    exact universalAt_of_rigid_full_near_fan
      G S H huni hsize X hroot P L hstarts hfinish
  · intro S _ T hBoundary q C F hstarts hfinish hpathT hfirst hsize huni
    exact universalAt_glueLeft_of_saturated_fan
      S T hBoundary H huni hsize C F hstarts hfinish hpathT hfirst

end HadwigerLean.RootedDensity
