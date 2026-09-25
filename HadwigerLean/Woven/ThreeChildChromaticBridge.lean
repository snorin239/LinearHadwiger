import HadwigerLean.Woven.ThreeChildChildRoots

/-!
# The three-child bridge with chromatic child size

The outer induction produces chromatic lower bounds for the three children.
Such a bound also supplies enough distinct vertices for their target roots.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A chromatic lower bound supplies the target-root cardinality condition
of the geometric three-child bridge. -/
theorem rooted_minor_of_three_woven_children_connected_of_chromatic
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a c b κ : ℕ}
    (hapos : 0 < a) (hscale : 2 * a = 3 * c)
    (H : Fin 3 → Finset V)
    (hH : Pairwise fun k l : Fin 3 =>
      Disjoint (H k : Set V) (H l : Set V))
    (hW : ∀ k, Woven (G.induce (H k : Set V)) c b)
    (hchrom : ∀ k, c ≤ chromatic (G.induce (H k : Set V)))
    (root : Fin a → V) (hroot : Function.Injective root)
    (start : Fin (2 * a) → V)
    (hstartinj : Function.Injective start)
    (hstartOutsideRoots : ∀ q i, start q ≠ root i)
    (hstartOutsideH : ∀ q k, start q ∉ H k)
    (hrootOutsideH : ∀ i k, root i ∉ H k)
    (hconn : VertexConnected G κ)
    (hκ : a + 16 * (2 * a) ≤ κ)
    (hbudget : 2 * a ≤ b)
    (hfirst : ∀ i, G.Adj (root i) (start (firstConnector i)))
    (hsecond : ∀ i, G.Adj (root i) (start (secondConnector i))) :
    HasRootedCliqueMinor G root := by
  have hcard (k : Fin 3) : c ≤ (H k).card := by
    calc
      c ≤ chromatic (G.induce (H k : Set V)) := hchrom k
      _ ≤ Fintype.card (↥(H k : Set V)) := chromatic_le_card _
      _ = (H k).card := by simp
  exact rooted_minor_of_three_woven_children_connected_of_card G
    hapos hscale H hH hW hcard root hroot start hstartinj
    hstartOutsideRoots hstartOutsideH hrootOutsideH hconn hκ
    hbudget hfirst hsecond

end Woven
end HadwigerLean
