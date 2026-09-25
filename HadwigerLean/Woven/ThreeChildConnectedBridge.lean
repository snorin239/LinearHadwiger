import HadwigerLean.Woven.ThreeChildRootedBridge
import HadwigerLean.Woven.ThreeChildScaleAssignment
import HadwigerLean.Graph.Linkedness.Final

/-!
# Three-child rooted model from ambient connectivity

Deleting the parent roots lowers vertex connectivity by at most their
number. The quantitative linkedness theorem then supplies the connector
linkage used by the three-child assembly.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The full geometric three-child step under the paper's connectivity
inequality. The two starts per parent root and the three child sets have
already been chosen in the residual graph. -/
theorem rooted_minor_of_three_woven_children_connected
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a c b κ : ℕ}
    (hapos : 0 < a) (hscale : 2 * a = 3 * c)
    (H : Fin 3 → Finset V)
    (hH : Pairwise fun k l : Fin 3 =>
      Disjoint (H k : Set V) (H l : Set V))
    (hW : ∀ k, Woven (G.induce (H k : Set V)) c b)
    (root : Fin a → V) (hroot : Function.Injective root)
    (childRoot : Fin 3 → Fin c → V)
    (hchildRoot : ∀ k, Function.Injective (childRoot k))
    (hchildRootH : ∀ k u, childRoot k u ∈ H k)
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
  classical
  let R : Finset V := Finset.univ.image root
  have hR : R.card ≤ a := by
    calc
      R.card ≤ (Finset.univ : Finset (Fin a)).card := Finset.card_image_le
      _ = a := by simp
  have hdel : VertexConnected (G.induce (R : Set V)ᶜ)
      (16 * (2 * a)) := by
    apply hconn.induce_compl R (16 * (2 * a))
    omega
  have hlink : Linkedness.KLinked (G.induce (R : Set V)ᶜ)
      (2 * a) := by
    exact Linkedness.kLinked_of_sixteen_mul_vertexConnected
      (G.induce (R : Set V)ᶜ) (2 * a) hdel
  have hc : 0 < c := by omega
  exact rooted_minor_of_three_woven_children_linked_complement G
    H hH hW root hroot childRoot hchildRoot hchildRootH
    (scaleAssignment hscale) start hstartinj hstartOutsideRoots
    hstartOutsideH hrootOutsideH hlink hbudget hfirst hsecond
    (scaleAssignment_different_children hscale hc)

end Woven
end HadwigerLean
