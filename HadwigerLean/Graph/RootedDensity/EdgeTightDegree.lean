import HadwigerLean.Graph.Linkedness.IncidenceHandshake
import Mathlib.Tactic

/-! The real-parameter F.3 handshake gives an outside vertex of low degree. -/

namespace HadwigerLean.RootedDensity

universe u

/-- Under the real F.3 edge-tight identity, one outward neighbor per root
and at least three roots force an outside vertex below degree `2α`. -/
theorem exists_outside_degree_lt_twice_of_floor_tight
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (α : ℝ) (hα : 0 ≤ α)
    (hX : 3 ≤ X.card)
    (htight : edgeIncidenceSetCount G (X : Set V)ᶜ =
      Nat.floor (α * ((Xᶜ).card : ℝ)) + 1)
    (hroot : ∀ x ∈ X, ∃ w ∉ X, G.Adj x w) :
    ∃ v ∈ Xᶜ, (G.degree v : ℝ) < 2 * α := by
  classical
  by_contra hnone
  push Not at hnone
  have hout : ∀ v ∈ Xᶜ, 2 * α ≤ (G.degree v : ℝ) := by
    intro v hv
    exact hnone v hv
  have hsumout : (∑ v ∈ Xᶜ, 2 * α) ≤
      (∑ v ∈ Xᶜ, (G.degree v : ℝ)) :=
    Finset.sum_le_sum (fun v hv => hout v hv)
  have hrootdeg : ∀ x ∈ X, 1 ≤ (G.neighborFinset x \ X).card := by
    intro x hx
    obtain ⟨w, hw, hxw⟩ := hroot x hx
    have hmem : w ∈ G.neighborFinset x \ X :=
      Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset x w).mpr hxw, hw⟩
    exact Finset.one_le_card.mpr ⟨w, hmem⟩
  have hsumroot : (∑ x ∈ X, (1 : ℝ)) ≤
      (∑ x ∈ X, ((G.neighborFinset x \ X).card : ℝ)) := by
    apply Finset.sum_le_sum
    intro x hx
    exact_mod_cast hrootdeg x hx
  have hhand : 2 * (edgeIncidenceSetCount G (X : Set V)ᶜ : ℝ) =
      (∑ v ∈ Xᶜ, (G.degree v : ℝ)) +
        (∑ x ∈ X, ((G.neighborFinset x \ X).card : ℝ)) := by
    exact_mod_cast Linkedness.edgeIncidenceSetCount_handshake G X
  have hfloor : (Nat.floor (α * ((Xᶜ).card : ℝ)) : ℝ) ≤
      α * ((Xᶜ).card : ℝ) := by
    exact Nat.floor_le (mul_nonneg hα (Nat.cast_nonneg _))
  have hXreal : (3 : ℝ) ≤ X.card := by exact_mod_cast hX
  rw [htight] at hhand
  simp only [Finset.sum_const, nsmul_eq_mul] at hsumout hsumroot
  push_cast at hsumout hsumroot hhand
  nlinarith

end HadwigerLean.RootedDensity

