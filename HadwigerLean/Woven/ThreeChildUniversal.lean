import HadwigerLean.Woven.ThreeChildChromaticBridge
import HadwigerLean.Woven.ThreeChildStartConnected

/-!
# Uniform rooted models from three child graphs

This theorem is the geometric side of the outer induction. For each choice
of parent roots, the neighbor starts are chosen first. A child-selection
contract then provides three woven induced graphs in their complement.
The conclusion holds for every injective root map.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If three suitable woven children can be found after choosing the
parent roots and their connector starts, every parent root set supports a
rooted clique minor. -/
theorem rooted_minor_for_every_root_of_three_child_selection
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a c b κ : ℕ}
    (hapos : 0 < a) (hscale : 2 * a = 3 * c)
    (hconn : VertexConnected G κ)
    (hκ : a + 16 * (2 * a) ≤ κ)
    (hbudget : 2 * a ≤ b)
    (hchildren : ∀ (root : Fin a → V), Function.Injective root →
      ∀ (start : Fin (2 * a) → V), Function.Injective start →
        (∀ q i, start q ≠ root i) →
        (∀ i, G.Adj (root i) (start (firstConnector i))) →
        (∀ i, G.Adj (root i) (start (secondConnector i))) →
      ∃ H : Fin 3 → Finset V,
        (Pairwise fun k l : Fin 3 =>
          Disjoint (H k : Set V) (H l : Set V)) ∧
        (∀ k, Woven (G.induce (H k : Set V)) c b) ∧
        (∀ k, c ≤ chromatic (G.induce (H k : Set V))) ∧
        (∀ q k, start q ∉ H k) ∧
        (∀ i k, root i ∉ H k)) :
    ∀ (root : Fin a → V), Function.Injective root →
      HasRootedCliqueMinor G root := by
  intro root hroot
  have hdegree : 4 * a ≤ κ := by omega
  obtain ⟨start, hstartinj, hstartOutsideRoots, hfirst, hsecond⟩ :=
    exists_parent_connector_starts_of_connected G root hconn hdegree
  obtain ⟨H,hH,hW,hchrom,hstartOutsideH,hrootOutsideH⟩ :=
    hchildren root hroot start hstartinj hstartOutsideRoots
      hfirst hsecond
  exact rooted_minor_of_three_woven_children_connected_of_chromatic G
    hapos hscale H hH hW hchrom root hroot start hstartinj
    hstartOutsideRoots hstartOutsideH hrootOutsideH hconn hκ
    hbudget hfirst hsecond

end Woven
end HadwigerLean
