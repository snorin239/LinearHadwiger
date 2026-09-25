import HadwigerLean.Woven.UniformSparseModel
import HadwigerLean.Graph.RootedDensity.Reduction
import HadwigerLean.Graph.RootedDensity.ConnectivityDensity
import Mathlib.Tactic

/-! A uniform woven reduction to rooted density for clique-plus-matching targets. -/

namespace HadwigerLean.Woven

open HadwigerLean.RootedDensity

universe u

/-- If every `K_a + j K₂` target satisfies the sharp rooted-density
conclusion at its Appendix F threshold, a common connectivity and density
budget gives the up-to-`b` woven property. -/
theorem woven_of_cliqueMatching_rootedDensity
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (a b K q : ℕ)
    (hconn : VertexConnected G K)
    (hproxy : ∀ j ≤ b, 2 * (a + 2 * j) ≤ K)
    (hcost : ∀ j ≤ b, (a + 2 * j) + q ≤ K)
    (hroot : ∀ j ≤ b, a + 2 * j ≤ q)
    (hdensity : ∀ j ≤ b,
      12 * cliqueMatchingThreshold a j +
        5000 * (Fintype.card (CliqueMatchingLabels a j) : ℝ) ≤
        (q : ℝ) / 2)
    (hRD : ∀ j ≤ b, RootedDensityConclusion.{u,0}
      (cliqueMatchingGraph a j)
      (12 * cliqueMatchingThreshold a j +
        5000 * (Fintype.card (CliqueMatchingLabels a j) : ℝ))) :
    Woven G a b := by
  classical
  intro root hrootinj j hj P hP
  let r := a + 2 * j
  have hdegree : ∀ i, 2 * r ≤ G.degree (originalRoleFin root P i) := by
    intro i
    exact (hproxy j hj).trans
      (HadwigerLean.Linkedness.degree_ge_of_vertexConnected hconn _)
  obtain ⟨proxy, hinj, hadj⟩ := exists_normalized_proxies G root P hdegree
  have hUcost : (occupiedRoles root P).card + q ≤ K := by
    have hU := occupiedRoles_card_le root P
    have hc := hcost j hj
    omega
  have hex : ∃ inst : Fintype (normalizedSet root P),
      @VertexConnected (normalizedSet root P) inst
        (G.induce (normalizedSet root P)) q := by
    exact ⟨(inferInstance : Fintype
      (↥((((occupiedRoles root P : Finset V) : Set V)ᶜ)))),
      hconn.induce_compl (occupiedRoles root P) q hUcost⟩
  obtain ⟨inst, hJconn⟩ := hex
  letI : Fintype (normalizedSet root P) := inst
  let J := G.induce (normalizedSet root P)
  have hJroot : VertexConnected J (Fintype.card (CliqueMatchingLabels a j)) :=
    hJconn.of_le (by rw [cliqueMatchingLabels_card]; exact hroot j hj)
  have hJdensity :
      12 * cliqueMatchingThreshold a j +
        5000 * (Fintype.card (CliqueMatchingLabels a j) : ℝ) ≤
        edgeDensity J :=
    (hdensity j hj).trans
      (RootedDensity.half_connectivity_le_edgeDensity J q hJconn)
  have hn : (0 : ℝ) < Fintype.card (normalizedSet root P) := by
    exact_mod_cast (Nat.zero_lt_of_lt hJconn.order_gt)
  have hJedges :
      (12 * cliqueMatchingThreshold a j +
        5000 * (Fintype.card (CliqueMatchingLabels a j) : ℝ)) *
        (Fintype.card (normalizedSet root P) : ℝ) ≤
        (edgeCount J : ℝ) := by
    exact (le_div_iff₀ hn).1 (by simpa [edgeDensity] using hJdensity)
  have hroleInj : Function.Injective (cliqueMatchingProxyRole root P proxy) := by
    intro x y hxy
    exact (cliqueMatchingRoleEquiv a j).symm.injective
      ((distinctRoleEquiv a j).injective (hinj hxy))
  have hminor := RootedDensity.rootedMinor_of_rootedDensity.{u,0}
    (cliqueMatchingGraph a j)
    (12 * cliqueMatchingThreshold a j +
      5000 * (Fintype.card (CliqueMatchingLabels a j) : ℝ))
    (hRD j hj) J hJroot hJedges
    (cliqueMatchingProxyRole root P proxy) hroleInj
  exact exists_solution_of_normalized_sparse_minor
    G root P hrootinj hP proxy hinj hadj hminor

end HadwigerLean.Woven

