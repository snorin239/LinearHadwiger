import HadwigerLean.Graph.RootedDensity.SamplingConnected
import HadwigerLean.Graph.CliqueDensity.Reduction
import Mathlib.Tactic

/-! Numerical closure of Appendix F.2's highly connected neighborhood case. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- A real minimum-degree bound supplies the real handshake lower bound. -/
theorem twice_edgeCount_ge_real_min_degree
    {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℝ) (hmin : ∀ x : V, d ≤ (G.degree x : ℝ)) :
    d * (Fintype.card V : ℝ) ≤ 2 * (edgeCount G : ℝ) := by
  classical
  have hsum : (∑ x : V, d) ≤ ∑ x : V, (G.degree x : ℝ) := by
    apply Finset.sum_le_sum
    intro x _
    exact hmin x
  have hhand : (∑ x : V, (G.degree x : ℝ)) =
      2 * (edgeCount G : ℝ) := by
    exact_mod_cast sum_degree_eq_two_edgeCount G
  simpa [hhand, mul_comm] using hsum

/-- If a graph has the size, minimum degree, and connectivity supplied by
(F.5), the `p=1/5` sample attaches a rooted target model at every `h`-set. -/
theorem universalAt_of_high_branch_bounds
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (c : ℝ) (hc : 1 < c) (hforces : DensityForcesMinor.{u,v} H c)
    (hh : 3 ≤ Fintype.card W)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V)
    (hX : X.card = Fintype.card W)
    (horder : (Fintype.card V : ℝ) ≤
      24 * c + 10000 * (Fintype.card W : ℝ) + 1)
    (hmin : ∀ x : V,
      12 * c + 4999 * (Fintype.card W : ℝ) ≤ (G.degree x : ℝ))
    (k : ℕ) (hconn : VertexConnected G k)
    (hkappa : 5 * c + 2200 * (Fintype.card W : ℝ) ≤ (k : ℝ)) :
    UniversalAt G H X := by
  classical
  let h := Fintype.card W
  let n := Fintype.card ↥((X : Set V)ᶜ)
  have hncard : n + h = Fintype.card V := by
    have heq : n = (Xᶜ : Finset V).card := by
      apply Fintype.card_of_finset' (Xᶜ)
      intro x
      simp
    rw [heq]
    calc
      (Xᶜ : Finset V).card + h = (Xᶜ : Finset V).card + X.card := by simp [h, hX]
      _ = Fintype.card V := Finset.card_compl_add_card X
  have hnlower : 100 ≤ (n : ℝ) := by
    have horder' := hconn.order_gt
    have hkreal : (k : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast horder'
    have hncardR : (n : ℝ) + (h : ℝ) = (Fintype.card V : ℝ) := by
      exact_mod_cast hncard
    have hhreal : (3 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  have hn2 : 2 ≤ n := by exact_mod_cast (show (2 : ℝ) ≤ n by linarith)
  have horderN : (n : ℝ) ≤ 24 * c + 10000 * (h : ℝ) + 1 := by
    have hnle : n ≤ Fintype.card V := by omega
    exact le_trans (by exact_mod_cast hnle) horder
  let Q := G.induce (X : Set V)ᶜ
  have hQmin : ∀ x : ↥((X : Set V)ᶜ),
      12 * c + 4998 * (h : ℝ) ≤ (Q.degree x : ℝ) := by
    intro x
    have hcut := degree_le_degree_induce_compl_add_card G X (x : V) x.property
    have hcutR : (G.degree (x : V) : ℝ) ≤ (Q.degree x : ℝ) + h := by
      exact_mod_cast (by simpa [hX] using hcut)
    linarith [hmin x]
  have hEdge : (12 * c + 4998 * (h : ℝ)) * (n : ℝ) ≤
      2 * (edgeCount Q : ℝ) :=
    twice_edgeCount_ge_real_min_degree Q _ hQmin
  have hbudget : c * ((1/5 : ℝ) * (n : ℝ) + 2) <
      (1/5 : ℝ) ^ 2 * (edgeCount Q : ℝ) := by
    have hhreal : (3 : ℝ) ≤ h := by exact_mod_cast hh
    nlinarith [mul_nonneg (show 0 ≤ c by linarith)
      (show 0 ≤ (n : ℝ) - 100 by linarith)]
  have hreserve : (1/5 : ℝ) * (n : ℝ) + 2 + 16 * (h : ℝ) ≤
      (k : ℝ) := by
    have hhreal : (3 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  have hdegree : ∀ x : V,
      (1/5 : ℝ) * (n : ℝ) + 2 + 2 * (h : ℝ) ≤ (G.degree x : ℝ) := by
    intro x
    have hhreal : (3 : ℝ) ≤ h := by exact_mod_cast hh
    linarith [hmin x]
  exact universalAt_of_sampled_high_connectivity H c (by linarith) hforces
    G X hn2 (1/5 : ℝ) (by norm_num) (by norm_num) hbudget
    k hconn hreserve hdegree

end HadwigerLean.RootedDensity



