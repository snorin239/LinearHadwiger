import HadwigerLean.Woven.ThreeChildDeletionCost

/-!
# Rooted residual model from a high-chromatic connected graph

This statement begins before deletion of the parent roots and connector
starts. Their chromatic cost is exactly bounded by `3a`; the remaining
separation, GN, and child-induction steps are delegated to the checked
three-child geometric bridge.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The high-chromatic residual rooted-clique-model theorem, with its
separability and child-wovenness contracts stated on the residual graph. -/
theorem rooted_minor_of_high_chromatic_residual
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a c b κparent κchild s childThreshold : ℕ}
    (hapos : 0 < a) (hscale : 2 * a = 3 * c)
    (root : Fin a → V) (hroot : Function.Injective root)
    (start : Fin (2 * a) → V)
    (hstartinj : Function.Injective start)
    (hstartOutsideRoots : ∀ q i, start q ≠ root i)
    (hfirst : ∀ i, G.Adj (root i) (start (firstConnector i)))
    (hsecond : ∀ i, G.Adj (root i) (start (secondConnector i)))
    (hsep : ∀ X : Finset V,
      X ⊆ parentResidual root start →
      2 * s < chromatic (G.induce (X : Set V)) →
      Bootstrap.ChromaticSeparable (G.induce (X : Set V)) s)
    (hχsep : 3 * a + 3 * s < chromatic G)
    (hχGN : 3 * a + 2 * s + 7 * κchild ≤ chromatic G)
    (hκchild : 0 < κchild)
    (hχchild : 3 * a + childThreshold + 2 * s + 6 * κchild ≤
      chromatic G)
    (hchildScale : c ≤ childThreshold)
    (hchild : ∀ H : Finset V, H ⊆ parentResidual root start →
      VertexConnected (G.induce (H : Set V)) κchild →
      childThreshold ≤ chromatic (G.induce (H : Set V)) →
      Woven (G.induce (H : Set V)) c b)
    (hconn : VertexConnected G κparent)
    (hκparent : a + 16 * (2 * a) ≤ κparent)
    (hbudget : 2 * a ≤ b) :
    HasRootedCliqueMinor G root := by
  have hχY := chromatic_le_parentResidual_add_three_mul G root start
  have hχsepY : 3 * s <
      chromatic (G.induce (parentResidual root start : Set V)) := by
    omega
  have hχGNY : 2 * s + 7 * κchild ≤
      chromatic (G.induce (parentResidual root start : Set V)) := by
    omega
  have hχchildY : childThreshold + 2 * s + 6 * κchild ≤
      chromatic (G.induce (parentResidual root start : Set V)) := by
    omega
  exact rooted_minor_of_residual_separation_GN G hapos hscale
    root hroot start hstartinj hstartOutsideRoots hfirst hsecond
    (parentResidual root start)
    (root_not_mem_parentResidual root start)
    (start_not_mem_parentResidual root start)
    hsep hχsepY hχGNY hκchild hχchildY hchildScale hchild
    hconn hκparent hbudget

end Woven
end HadwigerLean
