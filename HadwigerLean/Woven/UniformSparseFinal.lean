import HadwigerLean.Woven.UniformSparseF1
import HadwigerLean.Graph.RootedDensity.Final

/-! The sharp uniform woven theorem used by chromatic inseparability. -/

namespace HadwigerLean.Woven

open HadwigerLean.RootedDensity

universe u

theorem woven_of_sharp_connectivity
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (a b K : ℕ) (ha : 2 ≤ a)
    (hconn : VertexConnected G K)
    (hK : 1000000 * cliqueMatchingScale a b ≤ (K : ℝ)) :
    Woven G a b := by
  apply woven_of_ambientReverse G a b K ha hconn hK
  intro j _
  exact ambientRigidReverse_proved (cliqueMatchingGraph a j)

end HadwigerLean.Woven
