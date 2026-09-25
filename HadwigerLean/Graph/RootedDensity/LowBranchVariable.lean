import HadwigerLean.Graph.RootedDensity.LowBranch
import Mathlib.Tactic

/-! The near-shore closure without padding a separating set to a fixed order. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- A low-order cut can be used at its actual order. The loss in the
near-shore size is compensated by the better minimum-degree bound, so the
artificial adhesion padding in the paper is unnecessary. -/
theorem universalAt_of_low_branch_variable_cut
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (c : ℝ) (hc : 1 < c) (hforces : DensityForcesMinor.{u,v} H c)
    (hh : 3 ≤ Fintype.card W)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V)
    (hX : X.card = Fintype.card W)
    (t : ℝ) (ht : t ≤ 5 * c + 2200 * (Fintype.card W : ℝ) + 1)
    (hsize : 2 * (Fintype.card V : ℝ) + t ≤
      24 * c + 10000 * (Fintype.card W : ℝ) + 1)
    (houtsideLarge : 100 ≤ Fintype.card ↥((X : Set V)ᶜ))
    (hmin : ∀ x : V,
      12 * c + 4999 * (Fintype.card W : ℝ) - t ≤ (G.degree x : ℝ)) :
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
      12 * c + 4998 * (h : ℝ) - t ≤ (Q.degree x : ℝ) := by
    intro x
    have hcut := degree_le_degree_induce_compl_add_card G X (x : V) x.property
    have hcutR : (G.degree (x : V) : ℝ) ≤ (Q.degree x : ℝ) + h := by
      exact_mod_cast (by simpa [hX] using hcut)
    linarith [hmin x]
  have hEdge : (12 * c + 4998 * (h : ℝ) - t) * (n : ℝ) ≤
      2 * (edgeCount Q : ℝ) :=
    twice_edgeCount_ge_real_min_degree Q _ hQmin
  have hEdge' : (7 * c + 2798 * (h : ℝ) - 1) * (n : ℝ) ≤
      2 * (edgeCount Q : ℝ) := by
    have hcoeff : 7 * c + 2798 * (h : ℝ) - 1 ≤
        12 * c + 4998 * (h : ℝ) - t := by linarith
    have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr hcoeff) hnnonneg]
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
      2 * (12 * c + 4999 * (h : ℝ) - t) := by
    have hhreal : (3 : ℝ) ≤ h := by exact_mod_cast hh
    have hXR : (X.card : ℝ) = h := by exact_mod_cast hX
    linarith
  exact universalAt_of_sampled_common_neighbors H c (by linarith) hforces
    G X hn2 (1/3 : ℝ) (by norm_num) (by norm_num) hbudget
    (12 * c + 4999 * (h : ℝ) - t) hmin hoverlap

end HadwigerLean.RootedDensity
