import HadwigerLean.ReedSeymour.Strategy
import HadwigerLean.ReedSeymour.Maximal
import HadwigerLean.ReedSeymour.Bound

/-!
# Conditional closure of the Reed--Seymour proof

The no-odd-connector improvement is checked in `Strategy`. The remaining
odd-connector branch is stated here as one explicit hypothesis. From that
hypothesis, finite maximal support gives an all-egg decomposition, and the
checked LP bridge gives the fractional chromatic bound.
-/

namespace HadwigerLean
namespace ReedSeymour

variable {V : Type*} [Fintype V]

/-- The one remaining local improvement obligation: when a minimum terminal
connector contains an odd induced connector, improve egg support. Its inputs
retain the chosen partition, central block, weight, and minimum connector. -/
def HasOddConnectorImprovement (G : SimpleGraph V) : Prop :=
  ∀ (n : ℕ) (P : ConnectedPartition G (Fin n)) (i₀ : Fin n)
    (w : V → ℝ) (U : Finset V)
    (_hU : IsTerminalHittingSet P i₀ U)
    (_hmin : ∀ T : Finset V, T ⊂ U → ¬ IsTerminalHittingSet P i₀ T)
    (_hP : IsPartialEggDecomposition P w)
    (_hnot : ¬ IsEgg G w (P.block i₀)),
    ¬ NoOddConnector (G.induce (U : Set V))
      (inducedTerminalSet P i₀ (U : Set V)) →
    ∃ m : ℕ, ∃ Q : ConnectedPartition G (Fin m),
      IsPartialEggDecomposition Q w ∧ eggSupport P w ⊂ eggSupport Q w

/-- The odd-case improvement and the checked even-case strategy together
improve every non-egg block. -/
theorem hasEggSupportImprovement_of_odd_connector_improvement
    (G : SimpleGraph V) (w : V → ℝ)
    (hOdd : HasOddConnectorImprovement G) :
    HasEggSupportImprovement G w := by
  intro n P hP i₀ hnot
  obtain ⟨U, hU, hmin⟩ := exists_inclusion_minimal_terminal_connector P i₀
  by_cases hno : NoOddConnector (G.induce (U : Set V))
      (inducedTerminalSet P i₀ (U : Set V))
  · exact improve_of_no_odd_connector P i₀ w hP hnot hU hmin hno
  · exact hOdd n P i₀ w U hU hmin hP hnot hno

/-- Conditional all-egg decomposition for every real vertex weight. -/
theorem exists_all_egg_partition_of_odd_connector_improvement
    (G : SimpleGraph V) (w : V → ℝ)
    (hOdd : HasOddConnectorImprovement G) :
    ∃ n : ℕ, ∃ P : ConnectedPartition G (Fin n),
      (∀ i, IsEgg G w (P.block i)) ∧
        HasSimplicialElimination P.touchingQuotient :=
  exists_all_egg_partition_of_improvement G w
    (hasEggSupportImprovement_of_odd_connector_improvement G w hOdd)

/-- Reed--Seymour's bound follows from the explicit odd-connector
improvement hypothesis. The empty graph is included. -/
theorem reed_seymour_bound_of_odd_connector_improvement
    [DecidableEq V] (G : SimpleGraph V)
    (hOdd : HasOddConnectorImprovement G) :
    fractionalChromaticNumber G ≤ 2 * (cliqueMinorNumber G : ℝ) := by
  by_cases hV : Nonempty V
  · letI : Nonempty V := hV
    exact reed_seymour_bound_of_egg_decompositions G
      (fun w _ => exists_all_egg_partition_of_odd_connector_improvement G w hOdd)
  · letI : IsEmpty V := not_nonempty_iff.mp hV
    exact reed_seymour_bound_empty G

end ReedSeymour
end HadwigerLean
