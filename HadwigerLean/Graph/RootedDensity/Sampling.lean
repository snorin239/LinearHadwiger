import HadwigerLean.Graph.RootedDensity.Definitions
import HadwigerLean.Probability.FiniteSampling
import Mathlib.Tactic

/-! The finite induced-density sampling step (F.4) for an arbitrary target. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- If the sampling edge budget exceeds the worst allowed sample order,
then a sampled induced graph contains the target minor. -/
theorem exists_induced_minor_of_sampling_budget
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (c : ℝ) (hc : 0 ≤ c) (hforces : DensityForcesMinor.{u,v} H c)
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hn : 2 ≤ Fintype.card V)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hbudget : c * (p * (Fintype.card V : ℝ) + 2) <
      p ^ 2 * (edgeCount G : ℝ)) :
    ∃ s : Finset V,
      (s.card : ℝ) ≤ p * (Fintype.card V : ℝ) + 2 ∧
      Nonempty (MinorModel H (G.induce (s : Set V))) := by
  classical
  obtain ⟨s, hsize, hedge⟩ :=
    FiniteSampling.exists_induced_sample G hn p hp hp1
  have hppos : 0 < p ^ 2 * (edgeCount G : ℝ) := by
    have hnnonneg : 0 ≤ p * (Fintype.card V : ℝ) + 2 := by positivity
    nlinarith
  have hsampleEpos : 0 < (edgeCount (G.induce (s : Set V)) : ℝ) :=
    lt_of_lt_of_le hppos hedge
  have hsne : s.Nonempty := by
    by_contra hnot
    have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    subst s
    simp [edgeCount] at hsampleEpos
  have hcard : Fintype.card (s : Set V) = s.card := by simp
  have hbudgetSample : c * (Fintype.card (s : Set V) : ℝ) ≤
      (edgeCount (G.induce (s : Set V)) : ℝ) := by
    rw [hcard]
    have hmul := mul_le_mul_of_nonneg_left hsize hc
    linarith
  refine ⟨s, hsize, ?_⟩
  exact hforces (s : Set V) (G.induce (s : Set V))
    (by simpa [hcard] using hsne.card_pos) hbudgetSample

end HadwigerLean.RootedDensity
