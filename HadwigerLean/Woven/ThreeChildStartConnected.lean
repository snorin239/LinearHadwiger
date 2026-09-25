import HadwigerLean.Woven.ThreeChildNeighbors
import HadwigerLean.Graph.Linkedness.Massed

/-!
# Parent connector starts from connectivity
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertex connectivity supplies the degree hypothesis for choosing two
distinct neighboring starts per parent root. -/
theorem exists_parent_connector_starts_of_connected
    (G : SimpleGraph V) [DecidableRel G.Adj] {a κ : ℕ}
    (root : Fin a → V) (hconn : VertexConnected G κ)
    (hκ : 4 * a ≤ κ) :
    ∃ start : Fin (2 * a) → V,
      Function.Injective start ∧
      (∀ q i, start q ≠ root i) ∧
      (∀ i, G.Adj (root i) (start (firstConnector i))) ∧
      (∀ i, G.Adj (root i) (start (secondConnector i))) := by
  apply exists_parent_connector_starts G root
  intro i
  exact hκ.trans (Linkedness.degree_ge_of_vertexConnected hconn (root i))

end Woven
end HadwigerLean
