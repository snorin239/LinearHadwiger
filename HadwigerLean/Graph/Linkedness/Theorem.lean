import HadwigerLean.Graph.Linkedness.Core

/-!
# Quantitative linkedness: checked reductions

Appendix D reduces `16k`-connectivity to massed-pair rooted linkedness.
The complete result is in `Linkedness/Final.lean`.
-/

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The strengthened numerical criterion holds for the `5k`-minimum-degree,
`7k`-vertex component extracted in Appendix D. -/
theorem kLinked_of_five_k_degree_seven_k_order (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ)
    (hdegree : ∀ v, 5 * k ≤ G.degree v)
    (horder : Fintype.card V ≤ 7 * k) :
    KLinked G k := by
  apply kLinked_of_high_minDegree G k (5 * k) hdegree
  omega

/-- A `16k`-connected graph of order at most `29k` is linked directly by
the common-neighbor criterion. -/
theorem kLinked_of_connected_small_order (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ)
    (hconn : VertexConnected G (16 * k))
    (horder : Fintype.card V ≤ 29 * k) :
    KLinked G k := by
  apply kLinked_of_high_minDegree G k (16 * k)
  · intro v
    exact degree_ge_of_vertexConnected hconn v
  · omega

/-- The remaining reduction: a massed-pair rooted-linkage theorem for every
`2k`-set implies that `16k`-connectivity forces `k`-linkedness. -/
theorem kLinked_of_connected_massed_reduction (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (hk : 0 < k)
    (hconn : VertexConnected G (16 * k))
    (hmassed : ∀ X : Finset V, X.card = 2 * k →
      MassedPair G (X : Set V) ((8 * k : ℕ) : ℝ) →
        RootedLinked G X) :
    KLinked G k := by
  intro P hP hne
  let X := terminalFinset P
  have hX : X.card = 2 * k := terminalFinset_card_eq_two_mul k P hP hne
  obtain ⟨L, _⟩ := hmassed X hX
    (massed_of_vertexConnected G k hk hconn X hX)
    k P hP hne (terminals_subset_terminalFinset P)
  exact ⟨L⟩
end Linkedness
end HadwigerLean
