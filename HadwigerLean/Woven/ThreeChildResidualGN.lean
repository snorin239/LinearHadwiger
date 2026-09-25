import HadwigerLean.Woven.ThreeChildGNSeparation
import HadwigerLean.Woven.ThreeChildChromaticBridge

/-!
# Residual rooted clique model from separation, GN, and child wovenness

This is the full three-child geometric step after the parent roots and
their connector starts have been chosen. Chromatic separability supplies
three disjoint pieces, GN improves each piece's connectivity, the child
induction gives wovenness, and the geometric assembly yields the rooted
parent model.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The exact residual rooted-model bridge used by the outer induction,
with all numerical thresholds expressed as hypotheses. -/
theorem rooted_minor_of_residual_separation_GN
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a c b κparent κchild s childThreshold : ℕ}
    (hapos : 0 < a) (hscale : 2 * a = 3 * c)
    (root : Fin a → V) (hroot : Function.Injective root)
    (start : Fin (2 * a) → V)
    (hstartinj : Function.Injective start)
    (hstartOutsideRoots : ∀ q i, start q ≠ root i)
    (hfirst : ∀ i, G.Adj (root i) (start (firstConnector i)))
    (hsecond : ∀ i, G.Adj (root i) (start (secondConnector i)))
    (Y : Finset V)
    (hrootOutsideY : ∀ i, root i ∉ Y)
    (hstartOutsideY : ∀ q, start q ∉ Y)
    (hsep : ∀ X : Finset V, X ⊆ Y →
      2 * s < chromatic (G.induce (X : Set V)) →
      Bootstrap.ChromaticSeparable (G.induce (X : Set V)) s)
    (hχsep : 3 * s < chromatic (G.induce (Y : Set V)))
    (hχGN : 2 * s + 7 * κchild ≤
      chromatic (G.induce (Y : Set V)))
    (hκchild : 0 < κchild)
    (hchildBudget : childThreshold + 2 * s + 6 * κchild ≤
      chromatic (G.induce (Y : Set V)))
    (hchildScale : c ≤ childThreshold)
    (hchild : ∀ H : Finset V, H ⊆ Y →
      VertexConnected (G.induce (H : Set V)) κchild →
      childThreshold ≤ chromatic (G.induce (H : Set V)) →
      Woven (G.induce (H : Set V)) c b)
    (hconn : VertexConnected G κparent)
    (hκparent : a + 16 * (2 * a) ≤ κparent)
    (hbudget : 2 * a ≤ b) :
    HasRootedCliqueMinor G root := by
  obtain ⟨H,hHY,hHdis,hHconn,hHchrom⟩ :=
    three_connected_chromatic_pieces_of_separation G Y s κchild
      hκchild hsep hχsep hχGN
  have hW (k : Fin 3) : Woven (G.induce (H k : Set V)) c b := by
    apply hchild (H k) (hHY k) (hHconn k)
    have hb := hHchrom k
    omega
  have hchrom (k : Fin 3) :
      c ≤ chromatic (G.induce (H k : Set V)) := by
    have hb := hHchrom k
    omega
  have hstartOutsideH : ∀ q k, start q ∉ H k := by
    intro q k hq
    exact hstartOutsideY q (hHY k hq)
  have hrootOutsideH : ∀ i k, root i ∉ H k := by
    intro i k hi
    exact hrootOutsideY i (hHY k hi)
  have hHdisSet : Pairwise fun k l : Fin 3 =>
      Disjoint (H k : Set V) (H l : Set V) := by
    intro k l hkl
    simpa only [Finset.disjoint_coe] using hHdis hkl
  exact rooted_minor_of_three_woven_children_connected_of_chromatic G
    hapos hscale H hHdisSet hW hchrom root hroot start hstartinj
    hstartOutsideRoots hstartOutsideH hrootOutsideH hconn hκparent
    hbudget hfirst hsecond

end Woven
end HadwigerLean
