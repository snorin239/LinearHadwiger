import HadwigerLean.Woven.NormalizedConstruction
import HadwigerLean.Graph.RootedCliqueMinor.Dichotomy
import HadwigerLean.Graph.Linkedness.Massed

/-!
# The normalized clique-minor base of the woven induction

The minor and connectivity tests are on the graph after deleting all
original role vertices. Distinct adjacent proxies serve as roots there.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]
  {a j : ℕ}

/-- A sufficiently connected normalized graph with a large clique minor
supplies a woven solution for arbitrary original roles, including repeats
and singleton terminal pairs. -/
theorem exists_solution_of_normalized_clique_minor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (root : Fin a → V) (P : IndexedPairs (Fin j) V)
    [Fintype (normalizedSet root P)]
    (hroot : Function.Injective root)
    (hP : P.DisjointTerminals)
    (hdegree : ∀ i, 2 * (a + 2 * j) ≤ G.degree (originalRoleFin root P i))
    (hconn : VertexConnected (G.induce (normalizedSet root P)) (a + 2 * j))
    (hminor : HasCliqueMinor
      (G.induce (normalizedSet root P)) (2 * (a + 2 * j))) :
    Nonempty (WovenSolution G root P) := by
  classical
  obtain ⟨proxy, hproxy, hadj⟩ :=
    exists_normalized_proxies G root P hdegree
  have hrooted : HasRootedCliqueMinor
      (G.induce (normalizedSet root P)) proxy :=
    rootedCliqueMinor_of_connected_cliqueMinor hconn hminor proxy hproxy
  exact exists_solution_of_normalized_proxy_minor G root P hroot hP
    proxy hadj hrooted

/-- The ambient connectivity budget guarantees connectivity of the graph
after deleting the occupied roles. -/
theorem normalized_connected_of_budget
    {G : SimpleGraph V}
    (root : Fin a → V) (P : IndexedPairs (Fin j) V)
    {K : ℕ} (hconn : VertexConnected G K)
    (hbudget : 2 * (a + 2 * j) ≤ K) :
    ∃ inst : Fintype (normalizedSet root P),
      @VertexConnected (normalizedSet root P) inst
        (G.induce (normalizedSet root P)) (a + 2 * j) := by
  classical
  have hcard := occupiedRoles_card_le root P
  have hbudget' : (occupiedRoles root P).card + (a + 2 * j) ≤ K := by
    omega
  exact ⟨(inferInstance : Fintype (↥(((occupiedRoles root P : Finset V) : Set V)ᶜ))),
    hconn.induce_compl (occupiedRoles root P) (a + 2 * j) hbudget'⟩

/-- The normalized clique-minor case follows from ambient connectivity:
connectivity supplies distinct proxy neighbors and survives deletion of all
original role vertices. -/
theorem exists_solution_of_ambient_normalized_minor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (root : Fin a → V) (P : IndexedPairs (Fin j) V)
    (hroot : Function.Injective root)
    (hP : P.DisjointTerminals)
    {K : ℕ} (hconn : VertexConnected G K)
    (hbudget : 2 * (a + 2 * j) ≤ K)
    (hminor : HasCliqueMinor
      (G.induce (normalizedSet root P)) (2 * (a + 2 * j))) :
    Nonempty (WovenSolution G root P) := by
  classical
  obtain ⟨inst, hnorm⟩ := normalized_connected_of_budget root P hconn hbudget
  letI : Fintype (normalizedSet root P) := inst
  have hdegree : ∀ i, 2 * (a + 2 * j) ≤ G.degree (originalRoleFin root P i) := by
    intro i
    exact hbudget.trans (Linkedness.degree_ge_of_vertexConnected hconn _)
  exact exists_solution_of_normalized_clique_minor G root P hroot hP
    hdegree hnorm hminor

end Woven
end HadwigerLean