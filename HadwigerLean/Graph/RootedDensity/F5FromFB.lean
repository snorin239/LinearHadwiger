import HadwigerLean.Graph.RootedDensity.ClosedNeighborhood
import Mathlib.Tactic

/-! The exact floor and root-neighbor arithmetic turning F.b into F.5. -/

namespace HadwigerLean.RootedDensity

universe u

/-- The common-neighbor estimates from F.b imply the uniform numerical
bound needed for the closed-neighborhood minimum degree. The root-edge
premise uses total common neighbors, so F.b's outside-root count implies it. -/
theorem commonNeighbors_ge_density_minus_roots_of_FB
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (h : ℕ) (α : ℝ) (hX : X.card ≤ h) (hh : 1 ≤ h)
    (v : V)
    (hout : ∀ w : V, G.Adj v w → w ∉ X →
      Nat.floor α ≤ Fintype.card (G.commonNeighbors v w))
    (hroot : ∀ w : V, G.Adj v w → w ∈ X →
      Nat.floor α ≤ Fintype.card (G.commonNeighbors v w) + (X.erase w).card) :
    ∀ w : V, G.Adj v w →
      α - (h : ℝ) ≤ (Fintype.card (G.commonNeighbors v w) : ℝ) := by
  intro w hvw
  have hfloor : α < (Nat.floor α : ℝ) + 1 := Nat.lt_floor_add_one α
  by_cases hw : w ∈ X
  · have hcard : (X.erase w).card + 1 = X.card := by
      simpa [Nat.add_comm] using Finset.card_erase_add_one hw
    have hbound := hroot w hvw hw
    have hboundR : (Nat.floor α : ℝ) ≤
        (Fintype.card (G.commonNeighbors v w) : ℝ) +
        ((X.erase w).card : ℝ) := by exact_mod_cast hbound
    have hX' : (X.card : ℝ) ≤ (h : ℝ) := by exact_mod_cast hX
    have hcardR : ((X.erase w).card : ℝ) + 1 = (X.card : ℝ) := by
      exact_mod_cast hcard
    linarith
  · have hbound := hout w hvw hw
    have hboundR : (Nat.floor α : ℝ) ≤
        (Fintype.card (G.commonNeighbors v w) : ℝ) := by
      exact_mod_cast hbound
    have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith

/-- F.b's edge estimates plus one neighbor of the center imply F.5 for
the induced closed neighborhood. -/
theorem closedNeighborhood_F5_of_FB
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (h : ℕ) (α : ℝ) (hX : X.card ≤ h) (hh : 1 ≤ h)
    (v : V) (hdeg : (G.degree v : ℝ) ≤ 2 * α)
    (hnonisolated : ∃ w : V, G.Adj v w)
    (hout : ∀ w : V, G.Adj v w → w ∉ X →
      Nat.floor α ≤ Fintype.card (G.commonNeighbors v w))
    (hroot : ∀ w : V, G.Adj v w → w ∈ X →
      Nat.floor α ≤ Fintype.card (G.commonNeighbors v w) + (X.erase w).card) :
    let D := closedNeighborhoodFinset G v
    D.Nonempty ∧
    (D.card : ℝ) ≤ 2 * α + 1 ∧
    ∀ x : ↥(D : Set V),
      α - (h : ℝ) ≤ ((G.induce (D : Set V)).degree x : ℝ) := by
  dsimp
  have hcommon := commonNeighbors_ge_density_minus_roots_of_FB G X h α hX hh v
    hout hroot
  obtain ⟨w, hvw⟩ := hnonisolated
  have hcenterN : Fintype.card (G.commonNeighbors v w) ≤ G.degree v :=
    G.card_commonNeighbors_le_degree_left v w
  have hcenterR : (Fintype.card (G.commonNeighbors v w) : ℝ) ≤
      (G.degree v : ℝ) := by exact_mod_cast hcenterN
  have hcenter : α - (h : ℝ) ≤ (G.degree v : ℝ) :=
    (hcommon w hvw).trans hcenterR
  refine ⟨Finset.insert_nonempty _ _, ?_, ?_⟩
  · rw [card_closedNeighborhoodFinset]
    have hcard : ((G.degree v + 1 : ℕ) : ℝ) = (G.degree v : ℝ) + 1 := by
      simp
    rw [hcard]
    linarith
  · exact min_degree_closedNeighborhood_of_commonNeighbors G v
      (α - (h : ℝ)) hcenter hcommon

end HadwigerLean.RootedDensity
