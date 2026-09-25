import Mathlib.Tactic

/-!
# Minimal-set trimming

The finite optimization argument used in Section 8. The graph-specific
instance takes `energy T` to be the edge count of the induced graph and
`inside T v` to be the number of neighbors of `v` in `T`.
-/

namespace HadwigerLean

universe u

/-- A positive surplus on a finite set can be trimmed to a set with both a
prescribed internal contribution and a prescribed fraction of each ambient
contribution, provided deleting one element subtracts precisely its internal
contribution. -/
theorem exists_minimal_positive_surplus_set
    {V : Type u} [DecidableEq V]
    (S : Finset V) (energy : Finset V → ℝ)
    (degree : V → ℝ) (inside : Finset V → V → ℝ)
    (r δ : ℝ) (hr : 2 < r) (hδ : 0 < δ)
    (hzero : energy ∅ = 0)
    (hdelete : ∀ T ⊆ S, ∀ v ∈ T,
      energy (T.erase v) + inside T v = energy T)
    (hinside : ∀ T ⊆ S, ∀ v ∈ T, inside T v ≤ degree v)
    (hscore : (r - 1) * δ * (S.card : ℝ) +
      (∑ v ∈ S, degree v) < r * energy S) :
    ∃ T : Finset V, T.Nonempty ∧ T ⊆ S ∧
      (∀ v ∈ T, δ ≤ inside T v) ∧
      (∀ v ∈ T, degree v ≤ r * inside T v) := by
  classical
  let P : ℕ → Prop := fun n => ∃ T : Finset V,
    T ⊆ S ∧ T.card = n ∧
      (r - 1) * δ * (T.card : ℝ) +
        (∑ v ∈ T, degree v) < r * energy T
  have hP : ∃ n, P n := ⟨S.card, S, Finset.Subset.rfl, rfl, hscore⟩
  obtain ⟨T, hTS, hcard, hTscore⟩ := Nat.find_spec hP
  have hminimal (v : V) (hv : v ∈ T) :
      ¬ ((r - 1) * δ * ((T.erase v).card : ℝ) +
        (∑ w ∈ T.erase v, degree w) < r * energy (T.erase v)) := by
    intro hbad
    have hlt : (T.erase v).card < Nat.find hP := by
      rw [← hcard]
      exact Finset.card_erase_lt_of_mem hv
    exact (Nat.find_min hP hlt)
      ⟨T.erase v, (Finset.erase_subset v T).trans hTS, rfl, hbad⟩
  have hTnonempty : T.Nonempty := by
    by_contra h
    have hempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst T
    simp [hzero] at hTscore
  refine ⟨T, hTnonempty, hTS, ?_, ?_⟩
  · intro v hv
    by_contra hlt
    have hz : inside T v < δ := lt_of_not_ge hlt
    have hdeg : inside T v ≤ degree v := hinside T hTS v hv
    have henergy := hdelete T hTS v hv
    have hsum := Finset.sum_erase_add T degree hv
    have hcardErase : (T.erase v).card + 1 = T.card := by
      rw [Finset.card_erase_of_mem hv]
      have hpos : 0 < T.card := Finset.card_pos.mpr ⟨v, hv⟩
      omega
    have hcardR : ((T.erase v).card : ℝ) + 1 = (T.card : ℝ) := by
      exact_mod_cast hcardErase
    have hdrop : 0 < (r - 1) * (δ - inside T v) := by
      apply mul_pos <;> linarith
    have hgap : 0 < (r - 1) * δ + degree v - r * inside T v := by
      nlinarith [hdrop, hdeg]
    have henergyScaled : r * energy (T.erase v) + r * inside T v =
        r * energy T := by rw [← henergy]; ring
    have hcardScaled : (r - 1) * δ * ((T.erase v).card : ℝ) +
        (r - 1) * δ = (r - 1) * δ * (T.card : ℝ) := by
      rw [← hcardR]
      ring
    apply hminimal v hv
    linarith
  · intro v hv
    by_contra hlt
    have hz : r * inside T v < degree v := lt_of_not_ge hlt
    have henergy := hdelete T hTS v hv
    have hsum := Finset.sum_erase_add T degree hv
    have hcardErase : (T.erase v).card + 1 = T.card := by
      rw [Finset.card_erase_of_mem hv]
      have hpos : 0 < T.card := Finset.card_pos.mpr ⟨v, hv⟩
      omega
    have hcardR : ((T.erase v).card : ℝ) + 1 = (T.card : ℝ) := by
      exact_mod_cast hcardErase
    have hnonneg : 0 ≤ (r - 1) * δ :=
      mul_nonneg (by linarith) hδ.le
    have hgap : 0 < (r - 1) * δ + degree v - r * inside T v := by
      linarith
    have henergyScaled : r * energy (T.erase v) + r * inside T v =
        r * energy T := by rw [← henergy]; ring
    have hcardScaled : (r - 1) * δ * ((T.erase v).card : ℝ) +
        (r - 1) * δ = (r - 1) * δ * (T.card : ℝ) := by
      rw [← hcardR]
      ring
    apply hminimal v hv
    linarith

end HadwigerLean