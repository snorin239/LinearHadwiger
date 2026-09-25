import HadwigerLean.Graph.RootedDensity.HighBranch
import HadwigerLean.Graph.RootedDensity.LowCase
import Mathlib.Tactic

/-! Completion of Appendix F.2 from the closed-neighborhood bounds. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- A graph satisfying F.5 either is H-universal or contains an induced
H-universal near shore. This is the full F.2 contradiction to F.c, with the
connectivity threshold rounded by at most one. -/
theorem universal_or_universal_induced_of_neighborhood_bounds
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (c : ℝ) (hc : 1 < c) (hforces : DensityForcesMinor.{u,v} H c)
    (hh : 3 ≤ Fintype.card W)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (horder : (Fintype.card V : ℝ) ≤
      24 * c + 10000 * (Fintype.card W : ℝ) + 1)
    (hmin : ∀ x : V,
      12 * c + 4999 * (Fintype.card W : ℝ) ≤ (G.degree x : ℝ))
    (k : ℕ)
    (hkLower : 5 * c + 2200 * (Fintype.card W : ℝ) ≤ (k : ℝ))
    (hkUpper : (k : ℝ) ≤ 5 * c + 2200 * (Fintype.card W : ℝ) + 1) :
    Universal G H ∨ ∃ N : Finset V, Universal (G.induce (N : Set V)) H := by
  classical
  by_cases hconn : VertexConnected G k
  · left
    constructor
    · have hkg : k < Fintype.card V := hconn.order_gt
      have hkreal : (Fintype.card W : ℝ) ≤ k := by
        have hhreal : (3 : ℝ) ≤ Fintype.card W := by exact_mod_cast hh
        linarith
      have hkNat : Fintype.card W ≤ k := by exact_mod_cast hkreal
      omega
    · intro X hX
      exact universalAt_of_high_branch_bounds H c hc hforces hh G X hX
        horder hmin k hconn hkLower
  · right
    have hkOrder : k < Fintype.card V := by
      let x : V := Classical.choice inferInstance
      have hdeglt := G.degree_lt_card_verts x
      have hhreal : (3 : ℝ) ≤ Fintype.card W := by exact_mod_cast hh
      have hdegltR : (G.degree x : ℝ) < (Fintype.card V : ℝ) := by
        exact_mod_cast hdeglt
      have hkreal : (k : ℝ) < (Fintype.card V : ℝ) := by
        linarith [hmin x]
      exact_mod_cast hkreal
    exact exists_universal_induced_of_low_connectivity H c hc hforces hh
      G horder hmin k hkOrder hkUpper hconn

/-- The canonical integer threshold for the F.2 case split. -/
theorem universal_or_universal_induced_of_F5
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (c : ℝ) (hc : 1 < c) (hforces : DensityForcesMinor.{u,v} H c)
    (hh : 3 ≤ Fintype.card W)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (horder : (Fintype.card V : ℝ) ≤
      24 * c + 10000 * (Fintype.card W : ℝ) + 1)
    (hmin : ∀ x : V,
      12 * c + 4999 * (Fintype.card W : ℝ) ≤ (G.degree x : ℝ)) :
    Universal G H ∨ ∃ N : Finset V, Universal (G.induce (N : Set V)) H := by
  classical
  let q : ℝ := 5 * c + 2200 * (Fintype.card W : ℝ)
  let k : ℕ := ⌈q⌉₊
  have hqnonneg : 0 ≤ q := by
    have hhreal : (0 : ℝ) ≤ Fintype.card W := Nat.cast_nonneg _
    dsimp [q]
    positivity
  have hkLower : q ≤ (k : ℝ) := Nat.le_ceil q
  have hkUpper : (k : ℝ) ≤ q + 1 := (Nat.ceil_lt_add_one hqnonneg).le
  exact universal_or_universal_induced_of_neighborhood_bounds H c hc
    hforces hh G horder hmin k hkLower hkUpper

end HadwigerLean.RootedDensity
