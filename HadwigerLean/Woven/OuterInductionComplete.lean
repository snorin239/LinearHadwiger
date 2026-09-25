import HadwigerLean.Woven.OuterContracts

/-!
# The complete finite shared outer scale induction

Once a base-scale woven theorem and the explicit hub/separation contracts
hold at each nonbase scale in every induced host, the checked nonbase step
iterates down to the top scale.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem outerAt_all_of_contracts
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m K U B : ℕ)
    (h : ℕ → ℕ) (σ : ℕ → ℕ)
    (hK : 33 ≤ K)
    (hbase : OuterAt G m m K U B)
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
    (hhub : ∀ i, i < m → ∀ F : Finset V,
      OuterHubContract (G.induce (F : Set V))
        (outerScale m i) (h i))
    (hsep : ∀ i, i < m → ∀ F : Finset V,
      OuterSepContract (G.induce (F : Set V))
        (outerScale m i) (σ i)) :
    ∀ i, i ≤ m → OuterAt G m i K U B := by
  classical
  apply outerAt_all_of_base_step G m K U B hbase
  intro i hi hIH
  intro F hconn hχ
  let X := G.induce (F : Set V)
  have hIHX : OuterAt X m (i + 1) K U B :=
    outerAt_induce G m (i + 1) K U B hIH (F : Set V)
  exact woven_nonbase_from_contracts X hi hK
    (hbudget i hi) (hGN i hi) (hsepThreshold i hi)
    hIHX (hhub i hi F) (hsep i hi F) hconn hχ

theorem outerAt_top_of_contracts
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m K U B : ℕ)
    (h : ℕ → ℕ) (σ : ℕ → ℕ)
    (hK : 33 ≤ K)
    (hbase : OuterAt G m m K U B)
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
    (hhub : ∀ i, i < m → ∀ F : Finset V,
      OuterHubContract (G.induce (F : Set V))
        (outerScale m i) (h i))
    (hsep : ∀ i, i < m → ∀ F : Finset V,
      OuterSepContract (G.induce (F : Set V))
        (outerScale m i) (σ i)) :
    OuterAt G m 0 K U B :=
  outerAt_all_of_contracts G m K U B h σ hK hbase
    hbudget hGN hsepThreshold hhub hsep 0 (Nat.zero_le m)

end Woven
end HadwigerLean
