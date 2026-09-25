import HadwigerLean.Woven.OuterBudget
import HadwigerLean.Woven.OuterChromaticSeparation
import Mathlib.Tactic

/-!
# Downward induction on exact integer woven scales
-/

namespace HadwigerLean
namespace Woven

/-- The shared outer claim at one scale, uniformly over induced subgraphs
of a fixed finite graph. -/
def OuterAt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (m i K U B : ℕ) : Prop :=
  ∀ F : Finset V,
    VertexConnected (G.induce (F : Set V)) (K * outerScale m i) →
    U + B * outerScale m i ≤
      chromatic (G.induce (F : Set V)) →
    Woven (G.induce (F : Set V))
      (outerScale m i) (3 * outerScale m i)

/-- The finite outer recursion reduces all scales to a base case at
index m and a nonbase extension from child index i+1 to parent i. -/
theorem outerAt_all_of_base_step
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (m K U B : ℕ)
    (hbase : OuterAt G m m K U B)
    (hstep : ∀ i, i < m →
      OuterAt G m (i + 1) K U B →
      OuterAt G m i K U B) :
    ∀ i, i ≤ m → OuterAt G m i K U B := by
  have hrev : ∀ d : ℕ, d ≤ m →
      OuterAt G m (m - d) K U B := by
    intro d
    induction d with
    | zero =>
        intro _
        simpa using hbase
    | succ d ih =>
        intro hdm
        have hd : d ≤ m := by omega
        have hi : m - (d + 1) < m := by omega
        have hnext : m - (d + 1) + 1 = m - d := by omega
        have hchild := ih hd
        rw [← hnext] at hchild
        exact hstep (m - (d + 1)) hi hchild
  intro i hi
  have hd : m - i ≤ m := by omega
  have h := hrev (m - i) hd
  simpa [Nat.sub_sub_self hi] using h

/-- The top-scale claim obtained from the base and extension contracts. -/
theorem outerAt_top_of_base_step
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (m K U B : ℕ)
    (hbase : OuterAt G m m K U B)
    (hstep : ∀ i, i < m →
      OuterAt G m (i + 1) K U B →
      OuterAt G m i K U B) :
    OuterAt G m 0 K U B :=
  outerAt_all_of_base_step G m K U B hbase hstep 0 (Nat.zero_le m)

end Woven
end HadwigerLean
