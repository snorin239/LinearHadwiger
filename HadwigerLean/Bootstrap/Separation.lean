import HadwigerLean.Bootstrap.Definitions
import HadwigerLean.Graph.MinorFree
import HadwigerLean.Coloring.FractionalLP
import HadwigerLean.ReedSeymour.Theorem
import Mathlib.Tactic

/-!
# Order bound used in chromatic separation

The fractional chromatic number bounds the vertex count divided by the
independence number. Combined with the checked Reed--Seymour bound, this is
the numerical step in paper Lemma 14.
-/

namespace HadwigerLean.Bootstrap

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Summing the covering constraints of an optimal fractional coloring gives
the first two inequalities in the paper's equation (5). -/
theorem card_le_independence_mul_fractional (G : SimpleGraph V) :
    (Fintype.card V : ℝ) ≤
      (HadwigerLean.independenceNumber G : ℝ) *
        HadwigerLean.fractionalChromaticNumber G := by
  classical
  obtain ⟨x, _, hx, _, _, hopt⟩ :=
    HadwigerLean.exists_fractional_primal_dual_optima G
  have hcover : (Fintype.card V : ℝ) ≤
      ∑ v : V, HadwigerLean.vertexLoad G x v := by
    have hsumOne : (∑ _v : V, (1 : ℝ)) = (Fintype.card V : ℝ) := by simp
    rw [← hsumOne]
    exact Finset.sum_le_sum (fun v _ => hx.2 v)
  have hsum : (∑ v : V, HadwigerLean.vertexLoad G x v) =
      ∑ S : HadwigerLean.StableSet G, x S * (S.1.card : ℝ) := by
    simpa using HadwigerLean.weighted_vertexLoad_eq G x (fun _ => 1)
  calc
    (Fintype.card V : ℝ) ≤
        ∑ v : V, HadwigerLean.vertexLoad G x v := hcover
    _ = ∑ S : HadwigerLean.StableSet G, x S * (S.1.card : ℝ) := hsum
    _ ≤ ∑ S : HadwigerLean.StableSet G,
          x S * (HadwigerLean.independenceNumber G : ℝ) := by
        apply Finset.sum_le_sum
        intro S _
        apply mul_le_mul_of_nonneg_left _ (hx.1 S)
        exact_mod_cast HadwigerLean.stable_card_le_independenceNumber G S.2.2
    _ = (HadwigerLean.independenceNumber G : ℝ) *
          HadwigerLean.fractionalCost G x := by
        simp [HadwigerLean.fractionalCost, Finset.mul_sum, mul_comm]
    _ = (HadwigerLean.independenceNumber G : ℝ) *
          HadwigerLean.fractionalChromaticNumber G := by rw [hopt]

/-- Equation (5) after applying the checked Reed--Seymour theorem. -/
theorem card_le_twice_independence_mul_cliqueMinorNumber (G : SimpleGraph V) :
    (Fintype.card V : ℝ) ≤
      2 * (HadwigerLean.independenceNumber G : ℝ) *
        (HadwigerLean.cliqueMinorNumber G : ℝ) := by
  calc
    (Fintype.card V : ℝ) ≤
        (HadwigerLean.independenceNumber G : ℝ) *
          HadwigerLean.fractionalChromaticNumber G :=
      card_le_independence_mul_fractional G
    _ ≤ (HadwigerLean.independenceNumber G : ℝ) *
          (2 * (HadwigerLean.cliqueMinorNumber G : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (HadwigerLean.ReedSeymour.reed_seymour_bound G)
        (Nat.cast_nonneg _)
    _ = 2 * (HadwigerLean.independenceNumber G : ℝ) *
          (HadwigerLean.cliqueMinorNumber G : ℝ) := by ring

/-- The numerical contradiction in paper Lemma 14: an excluded K_u minor
and a quadratic independence bound force order strictly below 2uk². -/
theorem card_lt_two_u_k_sq (G : SimpleGraph V) (u k : ℕ)
    (hk : 0 < k) (hminor : ¬ HadwigerLean.HasCliqueMinor G u)
    (hind : HadwigerLean.independenceNumber G ≤ k ^ 2) :
    Fintype.card V < 2 * u * k ^ 2 := by
  have hminor' : HadwigerLean.cliqueMinorNumber G < u :=
    (HadwigerLean.not_hasCliqueMinor_iff_cliqueMinorNumber_lt G u).mp hminor
  have hind' : (HadwigerLean.independenceNumber G : ℝ) ≤ (k ^ 2 : ℝ) := by
    exact_mod_cast hind
  have hminor'' : (HadwigerLean.cliqueMinorNumber G : ℝ) < (u : ℝ) := by
    exact_mod_cast hminor'
  have hk' : (0 : ℝ) < (k ^ 2 : ℝ) := by exact_mod_cast (pow_pos hk 2)
  have hbound : (Fintype.card V : ℝ) < (2 * u * k ^ 2 : ℝ) := by
    calc
      (Fintype.card V : ℝ) ≤
          2 * (HadwigerLean.independenceNumber G : ℝ) *
            (HadwigerLean.cliqueMinorNumber G : ℝ) :=
        card_le_twice_independence_mul_cliqueMinorNumber G
      _ ≤ 2 * (k ^ 2 : ℝ) *
            (HadwigerLean.cliqueMinorNumber G : ℝ) := by gcongr
      _ < 2 * (k ^ 2 : ℝ) * (u : ℝ) := by gcongr
      _ = (2 * u * k ^ 2 : ℝ) := by push_cast; ring
  exact_mod_cast hbound

end HadwigerLean.Bootstrap





