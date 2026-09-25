import HadwigerLean.Graph.RootedDensity.SamplingAvoid
import HadwigerLean.Graph.RootedDensity.HighConnectivity
import Mathlib.Tactic

/-! The dense-sample and linked-complement branch of Appendix F.2. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- A dense sample in the complement of a prescribed root set yields
universality when the ambient connectivity and degree budgets can attach it.
This isolates the quantitative high-connectivity branch of Appendix F.2. -/
theorem universalAt_of_sampled_high_connectivity
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (c : ℝ) (hc : 0 ≤ c) (hforces : DensityForcesMinor.{u,v} H c)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V)
    (hn : 2 ≤ Fintype.card ↥((X : Set V)ᶜ))
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hbudget : c * (p * (Fintype.card ↥((X : Set V)ᶜ) : ℝ) + 2) <
      p ^ 2 * (edgeCount (G.induce (X : Set V)ᶜ) : ℝ))
    (k : ℕ) (hconn : VertexConnected G k)
    (hreserve : p * (Fintype.card ↥((X : Set V)ᶜ) : ℝ) + 2 +
      16 * (Fintype.card W : ℝ) ≤ (k : ℝ))
    (hdegree : ∀ x : V, p * (Fintype.card ↥((X : Set V)ᶜ) : ℝ) + 2 +
      2 * (Fintype.card W : ℝ) ≤ (G.degree x : ℝ)) :
    UniversalAt G H X := by
  classical
  obtain ⟨S, hXS, hSsize, ⟨M⟩⟩ :=
    exists_induced_minor_avoiding_of_sampling_budget H c hc hforces G X
      hn p hp hp1 hbudget
  have hk : S.card + 16 * Fintype.card W ≤ k := by
    have hreal : ((S.card + 16 * Fintype.card W : ℕ) : ℝ) ≤ (k : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hreal
  have hd : ∀ x ∈ S,
      S.card + 2 * Fintype.card W ≤ G.degree x := by
    intro x hx
    have hreal : ((S.card + 2 * Fintype.card W : ℕ) : ℝ) ≤
        (G.degree x : ℝ) := by
      push_cast
      linarith [hdegree x]
    exact_mod_cast hreal
  exact universalAt_of_induced_minor_high_connectivity H G X S hXS M
    k hconn hk hd

end HadwigerLean.RootedDensity
