import HadwigerLean.Graph.RootedDensity.LowShore
import Mathlib.Tactic

/-! Failure of the neighborhood connectivity threshold produces a universal
induced near-shore graph. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- The low-connectivity branch of Appendix F.2, using the actual separator
order. A cut below the threshold yields an induced H-universal graph. -/
theorem exists_universal_induced_of_low_connectivity
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (c : ℝ) (hc : 1 < c) (hforces : DensityForcesMinor.{u,v} H c)
    (hh : 3 ≤ Fintype.card W)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (horder : (Fintype.card V : ℝ) ≤
      24 * c + 10000 * (Fintype.card W : ℝ) + 1)
    (hmin : ∀ x : V,
      12 * c + 4999 * (Fintype.card W : ℝ) ≤ (G.degree x : ℝ))
    (k : ℕ) (hkOrder : k < Fintype.card V)
    (hkUpper : (k : ℝ) ≤ 5 * c + 2200 * (Fintype.card W : ℝ) + 1)
    (hnotconn : ¬ VertexConnected G k) :
    ∃ N : Finset V, Universal (G.induce (N : Set V)) H := by
  classical
  obtain ⟨N, t, hNne, ht, hsmall, hdegLoss⟩ :=
    exists_small_strict_side_of_low_cut G k
      (lowCut_of_not_vertexConnected G k hkOrder hnotconn)
  let J := G.induce (N : Set V)
  have htR : (t : ℝ) ≤ 5 * c + 2200 * (Fintype.card W : ℝ) + 1 := by
    have htk : (t : ℝ) ≤ k := by exact_mod_cast (Nat.le_of_lt ht)
    linarith
  have hsmallR : 2 * (Fintype.card ↥(N : Set V) : ℝ) + (t : ℝ) ≤
      24 * c + 10000 * (Fintype.card W : ℝ) + 1 := by
    have hs : ((2 * N.card + t : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hsmall
    have hNcard : Fintype.card ↥(N : Set V) = N.card := by simp
    rw [hNcard]
    push_cast at hs
    linarith
  have hJmin : ∀ x : ↥(N : Set V),
      12 * c + 4999 * (Fintype.card W : ℝ) - (t : ℝ) ≤
        (J.degree x : ℝ) := by
    intro x
    have hd := hdegLoss x
    have hdR : (G.degree (x : V) : ℝ) ≤ (J.degree x : ℝ) + t := by
      exact_mod_cast hd
    linarith [hmin x]
  have hNsize : 100 + Fintype.card W ≤ Fintype.card ↥(N : Set V) := by
    obtain ⟨v, hv⟩ := hNne
    let x : ↥(N : Set V) := ⟨v, hv⟩
    have hlt := J.degree_lt_card_verts x
    have hltR : (J.degree x : ℝ) < (Fintype.card ↥(N : Set V) : ℝ) := by
      exact_mod_cast hlt
    have hhR : (3 : ℝ) ≤ Fintype.card W := by exact_mod_cast hh
    have hleR : (100 : ℝ) + (Fintype.card W : ℝ) ≤
        (Fintype.card ↥(N : Set V) : ℝ) := by
      linarith [hJmin x]
    exact_mod_cast hleR
  refine ⟨N, ?_⟩
  constructor
  · omega
  intro Y hY
  have hYoutside : 100 ≤ Fintype.card ↥((Y : Set ↥(N : Set V))ᶜ) := by
    have hcomp : Fintype.card ↥((Y : Set ↥(N : Set V))ᶜ) + Y.card =
        Fintype.card ↥(N : Set V) := by
      have heq : Fintype.card ↥((Y : Set ↥(N : Set V))ᶜ) =
          (Yᶜ : Finset ↥(N : Set V)).card := by
        apply Fintype.card_of_finset' (Yᶜ)
        intro x
        simp
      rw [heq]
      exact Finset.card_compl_add_card Y
    omega
  exact universalAt_of_low_branch_variable_cut H c hc hforces hh
    J Y hY (t : ℝ) htR hsmallR hYoutside hJmin

end HadwigerLean.RootedDensity
