import HadwigerLean.ReedSeymour.Decomposition
import HadwigerLean.ReedSeymour.ParityConclusion
import HadwigerLean.ReedSeymour.Reindex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# The no-odd-connector branch of Reed--Seymour improvement

When the minimal terminal-hitting subset has no odd induced connector,
the parity theorem makes it bipartite. Its heavier color class is a yolk,
and the central split strictly enlarges egg support.
-/

namespace HadwigerLean
namespace ReedSeymour

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I]
  {G : SimpleGraph V}

/-- If the induced minimal terminal connector has no odd terminal path,
the central block can be replaced by an egg and connected remainder pieces. -/
theorem improve_of_no_odd_connector
    (P : ConnectedPartition G I) (i₀ : I) (w : V → ℝ)
    (hP : IsPartialEggDecomposition P w)
    (hnot : ¬ IsEgg G w (P.block i₀))
    {U : Finset V}
    (hU : IsTerminalHittingSet P i₀ U)
    (hmin : ∀ T : Finset V, T ⊂ U → ¬ IsTerminalHittingSet P i₀ T)
    (hno : NoOddConnector (G.induce (U : Set V))
      (inducedTerminalSet P i₀ (U : Set V))) :
    ∃ m : ℕ, ∃ Q : ConnectedPartition G (Fin m),
      IsPartialEggDecomposition Q w ∧
        eggSupport P w ⊂ eggSupport Q w := by
  classical
  have htrans : IsMinimalConnectedTransversal
      (G.induce (U : Set V))
      (inducedTerminalSet P i₀ (U : Set V)) :=
    minimal_hitting_set_is_minimal_transversal P i₀ hU hmin
  have hcolor : (G.induce (U : Set V)).Colorable 2 :=
    colorable_two_of_minimal_connected_transversal htrans hno
  have hEgg : IsEgg G w (U : Set V) :=
    egg_of_colorable_two w hU.2.1 hcolor
  have htouch : ∀ k, P.touchingQuotient.Adj i₀ k →
      ∃ x ∈ (U : Set V), ∃ y ∈ P.block k, G.Adj x y :=
    touches_neighbors_of_meets_terminals P i₀ (U : Set V) hU.2.2
  let S := CentralSplit.ofComponents P i₀ (U : Set V) hEgg.connected hU.1
  have hQ : IsPartialEggDecomposition S.partition w ∧
      eggSupport P w ⊂ eggSupport S.partition w :=
    CentralSplit.ofComponents_partial_and_support P i₀ w
      (U : Set V) hU.1 hEgg hP hnot htouch
  obtain ⟨m, Q, hQpartial, hQsupport⟩ :=
    S.partition.exists_fin_relabel w hQ.1
  exact ⟨m, Q, hQpartial, by simpa only [hQsupport] using hQ.2⟩


/-- Failure of the parity obstruction produces a concrete induced odd path
with distinct terminal labels. -/
theorem exists_odd_connector_of_not_no_odd {W I : Type*}
    {H : SimpleGraph W} {N : I → Set W}
    (hnot : ¬ NoOddConnector H N) :
    ∃ i j : I, i ≠ j ∧
      ∃ (a b : W) (p : H.Walk a b),
        IsTerminalConnector N i j p ∧ Odd p.length := by
  classical
  by_contra hn
  apply hnot
  intro i j hij a b p hp
  by_contra heven
  exact hn ⟨i, j, hij, a, b, p, hp,
    (Nat.not_even_iff_odd).mp heven⟩
end ReedSeymour
end HadwigerLean
