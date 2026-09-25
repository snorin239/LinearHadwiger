import HadwigerLean.Woven.OuterInductionComplete

/-!
# Mixed base and nonbase outer induction

The Corollary 24 cutoff may lie above several final integer scales.
At each such scale the clique-minor base argument applies directly.
The higher scales use the common nonbase step.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem outerAt_top_of_base_or_contracts
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m K U B : ℕ) (cutoff : ℝ)
    (h : ℕ → ℕ) (σ : ℕ → ℕ)
    (hK : 33 ≤ K)
    (hbase : OuterAt G m m K U B)
    (hsmall : ∀ i, i < m →
      ¬ cutoff < (outerScale m i : ℝ) →
      OuterAt G m i K U B)
    (hbudget : ∀ i, i < m →
      3 * outerChildLoss (outerScale m i) K (h i) (σ i) ≤
        B * outerScale m i)
    (hGN : ∀ i, i < m →
      K * outerScale m i ≤
        U + B * outerScale m (i + 1))
    (hsepThreshold : ∀ i, i < m →
      σ i <
        U + B * outerScale m (i + 1) +
          6 * (K * outerScale m i))
    (hhub : ∀ i, (hi : i < m) →
      cutoff < (outerScale m i : ℝ) →
      ∀ F : Finset V,
        VertexConnected (G.induce (F : Set V))
          (K * outerScale m i) →
        U + B * outerScale m i ≤ chromatic (G.induce (F : Set V)) →
        OuterHubContract (G.induce (F : Set V))
          (outerScale m i) (h i))
    (hsep : ∀ i, (hi : i < m) →
      cutoff < (outerScale m i : ℝ) →
      ∀ F : Finset V,
        OuterSepContract (G.induce (F : Set V))
          (outerScale m i) (σ i)) :
    OuterAt G m 0 K U B := by
  classical
  apply outerAt_top_of_base_step G m K U B hbase
  intro i hi hIH
  by_cases hcut : cutoff < (outerScale m i : ℝ)
  · intro F hconn hχ
    let X := G.induce (F : Set V)
    have hIHX : OuterAt X m (i + 1) K U B :=
      outerAt_induce G m (i + 1) K U B hIH (F : Set V)
    exact woven_nonbase_from_contracts X hi hK
      (hbudget i hi) (hGN i hi) (hsepThreshold i hi)
      hIHX (hhub i hi hcut F hconn hχ) (hsep i hi hcut F)
      hconn hχ
  · exact hsmall i hi hcut

end Woven
end HadwigerLean