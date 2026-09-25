import HadwigerLean.Woven.NormalizedConstruction
import HadwigerLean.Graph.RootedDensity.ConnectivityDensity
import HadwigerLean.Graph.CliqueDensity.Theorem
import HadwigerLean.Graph.CliqueMinorOrder
import Mathlib.Tactic

/-!
# Wovenness through a rooted clique minor on normalized proxies

This checked route uses a complete minor on every proxy slot. It is useful
when the terminal budget is small enough for the clique-density threshold.
The sparse-target argument of Appendix F is needed for the sharper bound
linear in an arbitrarily large terminal budget.
-/

namespace HadwigerLean.Woven

universe u

/-- A high enough connectivity and clique-density reserve yields the
up-to-`b` woven property through the normalized proxy construction. -/
theorem woven_of_clique_threshold
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (a b K q : ℕ) (ha : 1 ≤ a)
    (hconn : VertexConnected G K)
    (hproxy : 2 * (a + 2 * b) ≤ K)
    (hresidual : (a + 2 * b) + 2 * q ≤ K)
    (hrootconn : a + 2 * b ≤ 2 * q)
    (hKT : 30 * ((2 * (a + 2 * b) : ℕ) : ℝ) *
      Real.sqrt (Real.log ((2 * (a + 2 * b) : ℕ) : ℝ)) ≤ (q : ℝ)) :
    Woven G a b := by
  classical
  intro root hroot j hj P hP
  let r := a + 2 * j
  let R := a + 2 * b
  have hrR : r ≤ R := by dsimp [r, R]; omega
  have hdegree : ∀ i, 2 * r ≤ G.degree (originalRoleFin root P i) := by
    intro i
    have hd := HadwigerLean.Linkedness.degree_ge_of_vertexConnected hconn
      (originalRoleFin root P i)
    omega
  obtain ⟨proxy, hinj, hadj⟩ := exists_normalized_proxies G root P hdegree
  have hcost : (occupiedRoles root P).card + 2 * q ≤ K := by
    have hU := occupiedRoles_card_le root P
    omega
  have hex : ∃ inst : Fintype (normalizedSet root P),
      @VertexConnected (normalizedSet root P) inst
        (G.induce (normalizedSet root P)) (2 * q) := by
    exact ⟨(inferInstance : Fintype
      (↥((((occupiedRoles root P : Finset V) : Set V)ᶜ)))),
      hconn.induce_compl (occupiedRoles root P) (2 * q) hcost⟩
  obtain ⟨inst, hJconn⟩ := hex
  letI : Fintype (normalizedSet root P) := inst
  let J := G.induce (normalizedSet root P)
  have hqDensity : (q : ℝ) ≤ edgeDensity J := by
    have hhalf := RootedDensity.half_connectivity_le_edgeDensity J (2 * q) hJconn
    norm_num at hhalf ⊢
    exact hhalf
  have hR : 2 ≤ 2 * R := by dsimp [R]; omega
  have hKTJ : 30 * ((2 * R : ℕ) : ℝ) *
      Real.sqrt (Real.log ((2 * R : ℕ) : ℝ)) ≤ edgeDensity J :=
    hKT.trans hqDensity
  have hbig : HasCliqueMinor J (2 * R) :=
    hasCliqueMinor_of_edgeDensity_ge J (2 * R) hR hKTJ
  have hsmall : HasCliqueMinor J (2 * r) :=
    hasCliqueMinor_of_le hbig (by omega)
  have hJroot : VertexConnected J r :=
    hJconn.of_le (by dsimp [r, R] at *; omega)
  have hminor : HasRootedCliqueMinor J proxy :=
    rootedCliqueMinor_of_connected_cliqueMinor hJroot hsmall proxy hinj
  exact exists_solution_of_normalized_proxy_minor
    G root P hroot hP proxy hadj hminor

end HadwigerLean.Woven



