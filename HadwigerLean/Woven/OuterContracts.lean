import HadwigerLean.Woven.OuterNonbaseStep

/-!
# Reusable hub and separability contracts for the shared outer induction
-/

namespace HadwigerLean
namespace Woven

/-- The normalized, proxy-deleted hub contract at a fixed scale. -/
def OuterHubContract {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a h : ℕ) : Prop :=
  ∀ (j : ℕ) (_ : j ≤ 3 * a)
    (root : Fin a → V) (P : IndexedPairs (Fin j) V)
    (role : Fin (a + 2 * j) → normalizedSet root P),
    Function.Injective role →
    ¬ HasCliqueMinor (G.induce (normalizedSet root P)) (14 * a) →
    ∃ H : Finset (normalizedSet root P),
      Disjoint (Finset.univ.image (hubRoleFin role)) H ∧
      VertexConnected
        ((G.induce (normalizedSet root P)).induce (H : Set _))
        (16 * (a + j)) ∧
      chromatic
        ((G.induce (normalizedSet root P)).induce (H : Set _)) ≤ h

/-- Every induced subgraph of a minor-free normalized graph above the
threshold admits the two chromatic pieces needed by the three-child step. -/
def OuterSepContract {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a σ : ℕ) : Prop :=
  ∀ (j : ℕ) (_ : j ≤ 3 * a)
    (root : Fin a → V) (P : IndexedPairs (Fin j) V),
    ¬ HasCliqueMinor (G.induce (normalizedSet root P)) (14 * a) →
    ∀ X : Finset (normalizedSet root P),
      2 * σ <
        chromatic ((G.induce (normalizedSet root P)).induce
          (X : Set _)) →
      Bootstrap.ChromaticSeparable
        ((G.induce (normalizedSet root P)).induce (X : Set _)) σ

/-- The nonbase step, stated with reusable named contracts. -/
theorem woven_nonbase_from_contracts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m i K U B h σ : ℕ}
    (hi : i < m)
    (hK : 33 ≤ K)
    (hbudget :
      3 * outerChildLoss (outerScale m i) K h σ ≤
        B * outerScale m i)
    (hGN : K * outerScale m i ≤
      U + B * outerScale m (i + 1))
    (hsepThreshold : σ <
      U + B * outerScale m (i + 1) +
        6 * (K * outerScale m i))
    (hIH : OuterAt G m (i + 1) K U B)
    (hhub : OuterHubContract G (outerScale m i) h)
    (hsep : OuterSepContract G (outerScale m i) σ)
    (hconn : VertexConnected G (K * outerScale m i))
    (hχ : U + B * outerScale m i ≤ chromatic G) :
    Woven G (outerScale m i) (3 * outerScale m i) :=
  woven_nonbase_of_hub_separation G hi hK hbudget hGN
    hsepThreshold hIH hhub hsep hconn hχ

end Woven
end HadwigerLean
