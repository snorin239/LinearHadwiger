import HadwigerLean.Graph.Finite
import HadwigerLean.Graph.Minor
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Graph and scale predicates for the exponent bootstrap

These definitions follow the paper's local bound and separation statements.
The only bounds assumed later are the two named external inputs in
`Deduction/ExternalInputs.lean`.
-/

namespace HadwigerLean.Bootstrap

universe u

/-- A linear coloring bound for graphs of order at most
`t * (log t)^α`, uniformly over all finite vertex types. -/
def LocalLinearBound (α : ℝ) : Prop :=
  ∃ D t₀ : ℕ, 1 ≤ D ∧ 2 ≤ t₀ ∧
    ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (t : ℕ),
      t₀ ≤ t → ¬ HadwigerLean.HasCliqueMinor G t →
      (Fintype.card V : ℝ) ≤ (t : ℝ) * (Real.log (t : ℝ)) ^ α →
      HadwigerLean.chromatic G ≤ D * t

/-- There is no connected bipartite induced subgraph on exactly `k` vertices.
The connected-subgraph reduction in the packing lemma makes this equivalent
to the paper's `b(G) < k` when `k ≥ 2`. -/
def NoLargeConnectedBipartite {V : Type u}
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ s : Finset V, s.card = k →
    ¬ ((G.induce (s : Set V)).Connected ∧
       (G.induce (s : Set V)).IsBipartite)

/-- Two disjoint induced subgraphs each retain all but `s` colors. -/
def ChromaticSeparable {V : Type u} [Fintype V]
    (G : SimpleGraph V) (s : ℕ) : Prop :=
  ∃ A B : Set V, Disjoint A B ∧
    HadwigerLean.chromatic G ≤ HadwigerLean.chromatic (G.induce A) + s ∧
    HadwigerLean.chromatic G ≤ HadwigerLean.chromatic (G.induce B) + s

/-- Integer scales `a = (2/3)^i T` from the outer recursion. -/
def IsOuterScale (T a : ℕ) : Prop :=
  ∃ i : ℕ, 3 ^ i * a = 2 ^ i * T

/-- `T` is the least power of three at least `t`. -/
def IsLeastPowerOfThreeAtLeast (t T : ℕ) : Prop :=
  (∃ m : ℕ, T = 3 ^ m) ∧ t ≤ T ∧
    ∀ U : ℕ, (∃ m : ℕ, U = 3 ^ m) → t ≤ U → T ≤ U

/-- The exact separation premise used by paper Corollary 24. -/
def OuterSeparation {V : Type u} [Fintype V]
    (G : SimpleGraph V) (T d : ℕ) : Prop :=
  ∀ a : ℕ, IsOuterScale T a →
    (T : ℝ) / Real.sqrt (Real.log (T : ℝ)) < (a : ℝ) →
    ∀ Y : Set V,
      letI : Fintype Y := Fintype.ofFinite Y
      ¬ HadwigerLean.HasCliqueMinor (G.induce Y) (14 * a) →
      28 * d * a < HadwigerLean.chromatic (G.induce Y) →
      ChromaticSeparable (G.induce Y) (14 * d * a)

end HadwigerLean.Bootstrap
