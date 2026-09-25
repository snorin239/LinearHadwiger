import HadwigerLean.Graph.RootedDensity.CommonNeighbors
import HadwigerLean.Graph.RootedDensity.HighBranch
import Mathlib.Tactic

/-! Numerical closure of Appendix F.2's low-connectivity near shore. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- In the low-connectivity case, the small near shore is universal: sample
at `p=1/3`, then attach each root to its assigned branch by a fresh common
neighbor. These are the F.6--F.8 numerical bounds. -/
theorem universalAt_of_low_branch_bounds
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (c : ℝ) (hc : 1 < c) (hforces : DensityForcesMinor.{u,v} H c)
    (hh : 3 ≤ Fintype.card W)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V)
    (hX : X.card = Fintype.card W)
    (houtsideOrder : (Fintype.card ↥((X : Set V)ᶜ) : ℝ) ≤
      10 * c + 4000 * (Fintype.card W : ℝ))
    (houtsideLarge : 100 ≤ Fintype.card ↥((X : Set V)ᶜ))
    (hmin : ∀ x : V,
      7 * c + 2799 * (Fintype.card W : ℝ) - 1 ≤ (G.degree x : ℝ)) :
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
  have hncardR : (n : ℝ) + (h : ℝ) = (Fintype.card V : ℝ) := by
    exact_mod_cast hncard
  have hn2 : 2 ≤ n := by omega
  let Q := G.induce (X : Set V)ᶜ
  have hQmin : ∀ x : ↥((X : Set V)ᶜ),
      7 * c + 2798 * (h : ℝ) - 1 ≤ (Q.degree x : ℝ) := by
    intro x
    have hcut := degree_le_degree_induce_compl_add_card G X (x : V) x.property
    have hcutR : (G.degree (x : V) : ℝ) ≤ (Q.degree x : ℝ) + h := by
      exact_mod_cast (by simpa [hX] using hcut)
    linarith [hmin x]
  have hEdge : (7 * c + 2798 * (h : ℝ) - 1) * (n : ℝ) ≤
      2 * (edgeCount Q : ℝ) :=
    twice_edgeCount_ge_real_min_degree Q _ hQmin
  have hbudget : c * ((1/3 : ℝ) * (n : ℝ) + 2) <
      (1/3 : ℝ) ^ 2 * (edgeCount Q : ℝ) := by
    have hhreal : (3 : ℝ) ≤ h := by exact_mod_cast hh
    have hnreal : (100 : ℝ) ≤ n := by
      change (100 : ℝ) ≤ (Fintype.card ↥((X : Set V)ᶜ) : ℝ)
      exact_mod_cast houtsideLarge
    nlinarith [mul_nonneg (show 0 ≤ c by linarith)
      (show 0 ≤ (n : ℝ) - 100 by linarith)]
  have hoverlap : (Fintype.card V : ℝ) +
      ((1/3 : ℝ) * (n : ℝ) + 2) + (X.card : ℝ) + (h : ℝ) ≤
      2 * (7 * c + 2799 * (h : ℝ) - 1) := by
    have hhreal : (3 : ℝ) ≤ h := by exact_mod_cast hh
    have hXR : (X.card : ℝ) = h := by exact_mod_cast hX
    linarith
  exact universalAt_of_sampled_common_neighbors H c (by linarith) hforces
    G X hn2 (1/3 : ℝ) (by norm_num) (by norm_num) hbudget
    (7 * c + 2799 * (h : ℝ) - 1) hmin hoverlap

end HadwigerLean.RootedDensity

