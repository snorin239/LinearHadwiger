import HadwigerLean.Woven.ThreeChildResidualTheorem
import HadwigerLean.Woven.ThreeChildStartConnected

/-!
# Uniform residual rooted clique minors

The parent roots are arbitrary. Connectivity first supplies two distinct
neighbor starts per root, and the high-chromatic three-child theorem then
builds the corresponding rooted model.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The uniform rooted-minor conclusion needed for the normalized nonbase
hub construction. The separability and child-wovenness rules apply to all
induced subgraphs of the residual graph. -/
theorem rooted_minor_for_every_root_of_high_chromatic_residual
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a c b κparent κchild s childThreshold : ℕ}
    (hapos : 0 < a) (hscale : 2 * a = 3 * c)
    (hsep : ∀ X : Finset V,
      2 * s < chromatic (G.induce (X : Set V)) →
      Bootstrap.ChromaticSeparable (G.induce (X : Set V)) s)
    (hχsep : 3 * a + 3 * s < chromatic G)
    (hχGN : 3 * a + 2 * s + 7 * κchild ≤ chromatic G)
    (hκchild : 0 < κchild)
    (hχchild : 3 * a + childThreshold + 2 * s + 6 * κchild ≤
      chromatic G)
    (hchildScale : c ≤ childThreshold)
    (hchild : ∀ H : Finset V,
      VertexConnected (G.induce (H : Set V)) κchild →
      childThreshold ≤ chromatic (G.induce (H : Set V)) →
      Woven (G.induce (H : Set V)) c b)
    (hconn : VertexConnected G κparent)
    (hκparent : a + 16 * (2 * a) ≤ κparent)
    (hbudget : 2 * a ≤ b) :
    ∀ (root : Fin a → V), Function.Injective root →
      HasRootedCliqueMinor G root := by
  intro root hroot
  have hdegree : 4 * a ≤ κparent := by omega
  obtain ⟨start,hstartinj,hstartOutsideRoots,hfirst,hsecond⟩ :=
    exists_parent_connector_starts_of_connected G root hconn hdegree
  exact rooted_minor_of_high_chromatic_residual G hapos hscale
    root hroot start hstartinj hstartOutsideRoots hfirst hsecond
    (fun X _ hχ => hsep X hχ)
    hχsep hχGN hκchild hχchild hchildScale
    (fun H _ hconnH hχH => hchild H hconnH hχH)
    hconn hκparent hbudget

end Woven
end HadwigerLean
