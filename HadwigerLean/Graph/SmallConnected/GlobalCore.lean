import HadwigerLean.Graph.SmallConnected.GlobalNumerics
import HadwigerLean.Graph.SmallConnected.GlobalTrimming
import HadwigerLean.Graph.SmallConnected.CrossGraph
import HadwigerLean.Graph.SmallConnected.KTBound
import HadwigerLean.Graph.SmallConnected.EdgePartition
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# The quotient graph has a trimmed dense residual set
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The global counting portion of Section 8: from a dense quotient with
a sufficiently small exceptional set, obtain the trimmed set satisfying
Equation (8.6). -/
theorem exists_trimmed_residual_set
    (Q : SimpleGraph V) [DecidableRel Q.Adj]
    (T : Finset V) (t k N : ℕ)
    (ht : 3 ≤ t) (htk : t ≤ k) (hN : 0 < N)
    (hminor : ¬ HasCliqueMinor Q t)
    (horder : Fintype.card V ≤ N)
    (hTcard : 10 * Real.log (t : ℝ) * (T.card : ℝ) ≤ (3 * N : ℝ))
    (hretained : (9 / 10 : ℝ) * (480 * 6400 * (k : ℝ)) * (N : ℝ) ≤
      (edgeCount Q : ℝ)) :
    ∃ S' : Finset V, S'.Nonempty ∧ S' ⊆ Tᶜ ∧
      (∀ v ∈ S', (4 * (48 * 6400 * k) : ℝ) ≤
        ((Q.neighborFinset v ∩ S').card : ℝ)) ∧
      (∀ v ∈ S', (Q.degree v : ℝ) ≤
        3 * ((Q.neighborFinset v ∩ S').card : ℝ)) := by
  classical
  let S : Finset V := Tᶜ
  let L : ℝ := Real.log (t : ℝ)
  let s : ℝ := S.card
  let q : ℝ := T.card
  let n : ℝ := N
  let eS : ℝ := edgeCount (Q.induce (S : Set V))
  let eT : ℝ := edgeCount (Q.induce (T : Set V))
  let eCross : ℝ := ∑ w ∈ T, ((Q.neighborFinset w ∩ S).card : ℝ)
  have hLone : 1 ≤ L := by
    have h3 : (1 : ℝ) < Real.log 3 := by
      have h := Real.log_three_gt_d9
      norm_num at h ⊢
      linarith
    have htR : (3 : ℝ) ≤ t := by exact_mod_cast ht
    exact (le_of_lt h3).trans (Real.log_le_log (by norm_num) htR)
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  have hq0 : 0 ≤ q := Nat.cast_nonneg _
  have hn0 : 0 < n := by change (0 : ℝ) < (N : ℝ); exact_mod_cast hN
  have hsN : s ≤ n := by
    have hcard : S.card ≤ N :=
      (Finset.card_le_univ S).trans horder
    change (S.card : ℝ) ≤ (N : ℝ)
    exact_mod_cast hcard
  have hdisj : Disjoint T S := by
    apply Finset.disjoint_left.mpr
    intro v hvT hvS
    exact (Finset.mem_compl.mp hvS) hvT
  have hminorT : ¬ HasCliqueMinor (Q.induce (T : Set V)) t := by
    intro h
    exact hminor (hasCliqueMinor_of_minor (induce_isMinor Q (T : Set V)) h)
  have heT := minor_free_edgeCount_le_kt (Q.induce (T : Set V))
    t (by omega) hminorT
  have hcardT : Fintype.card ↥(T : Set V) = T.card := by
    simpa using Fintype.card_coe T
  rw [hcardT] at heT
  have heCross := cross_edges_le_unbalanced_bound
    Q T S hdisj t ht hminor
  have hbalance := edgeCount_eq_inside_add_outside_add_cross Q S
  have hScompl : Sᶜ = T := by simp [S]
  rw [hScompl] at hbalance
  have hbalance' : (edgeCount Q : ℝ) = eS + eT + eCross := by
    simpa [eS, eT, eCross] using hbalance
  have hsubcast : ((t - 2 : ℕ) : ℝ) = (t : ℝ) - 2 := by
    exact Nat.cast_sub (by omega : 2 ≤ t)
  have hsqrtcomm : Real.sqrt ((T.card : ℝ) * (S.card : ℝ)) =
      Real.sqrt ((S.card : ℝ) * (T.card : ℝ)) := by rw [mul_comm]
  rw [hsubcast, hsqrtcomm] at heCross
  have hcrossNum : eCross ≤
      6400 * (t : ℝ) * Real.sqrt L * Real.sqrt (s * q) +
        ((t : ℝ) - 2) * (s + q) := by
    dsimp [eCross, L, s, q]
    convert heCross using 1 <;> ring
  have hnum := global_trimming_surplus_numerical
    s q n (t : ℝ) (k : ℝ) L eS eT eCross (edgeCount Q : ℝ)
    hs0 hsN hq0 hn0 (by exact_mod_cast ht) (by exact_mod_cast htk)
    hLone (by simpa [L, q, n] using hTcard)
    hcrossNum
    (by simpa [eT, q, L, mul_assoc] using heT)
    hbalance' (by simpa [n] using hretained)
  have hδ : (0 : ℝ) < (4 * (48 * 6400 * k) : ℝ) := by
    have hk : 0 < k := by omega
    exact_mod_cast (by positivity : 0 < 4 * (48 * 6400 * k))
  have hsurplus : (3 - 2 : ℝ) *
      (edgeCount (Q.induce (S : Set V)) : ℝ) >
      (3 - 1 : ℝ) * (4 * (48 * 6400 * k) : ℝ) * (S.card : ℝ) +
        ∑ w ∈ Sᶜ, ((Q.neighborFinset w ∩ S).card : ℝ) := by
    rw [hScompl]
    norm_num only [show (3 - 2 : ℝ) = 1 by norm_num,
      show (3 - 1 : ℝ) = 2 by norm_num, one_mul]
    dsimp [eS, s, eCross] at hnum
    nlinarith [hnum]
  obtain ⟨S', hne, hsub, hmin, hratio⟩ :=
    exists_trimmed_of_inside_cross_surplus Q S 3
      (4 * (48 * 6400 * k) : ℝ) (by norm_num) hδ hsurplus
  exact ⟨S', hne, hsub, hmin, hratio⟩

end HadwigerLean
