import HadwigerLean.ReedSeymour.Conclusion
import HadwigerLean.ReedSeymour.ConnectorLift

/-!
# Reed--Seymour's fractional Hadwiger bound

The two local improvement branches now close the maximal-support argument.
The resulting egg decomposition supplies a weighted independent set, and
finite linear-programming duality gives the fractional chromatic bound.
-/

namespace HadwigerLean
namespace ReedSeymour

variable {V : Type*} [Fintype V]

/-- The odd terminal connector in a minimal induced central set triggers
the checked fusion improvement. -/
theorem hasOddConnectorImprovement (G : SimpleGraph V) :
    HasOddConnectorImprovement G := by
  classical
  intro n P i₀ w U hU _hmin hP hnot hno
  obtain ⟨i, j, _, a, b, p, hp, hodd⟩ :=
    exists_odd_connector_of_not_no_odd hno
  let q : G.Walk a.1 b.1 := CentralSplit.liftInducedWalk p
  have hq : IsTerminalConnector (terminalSet P i₀) i.1 j.1 q :=
    lift_induced_terminal_connector P i₀ (U : Set V) i j p hp
  have hqodd : Odd q.length := by
    rw [liftInducedWalk_length]
    exact hodd
  have hinside : ∀ v, v ∈ q.support → v ∈ P.block i₀ := by
    intro v hv
    exact hU.1 (liftInducedWalk_support_subset p v hv)
  exact CentralSplit.improve_of_odd_terminal_connector P i₀ w hP hnot
    i.2 j.2 q hq hqodd hinside

/-- The Reed--Seymour theorem: the fractional chromatic number is at most
twice the clique-minor number for every finite simple graph. -/
theorem reed_seymour_bound [DecidableEq V] (G : SimpleGraph V) :
    fractionalChromaticNumber G ≤ 2 * (cliqueMinorNumber G : ℝ) :=
  reed_seymour_bound_of_odd_connector_improvement G
    (hasOddConnectorImprovement G)

end ReedSeymour
end HadwigerLean
