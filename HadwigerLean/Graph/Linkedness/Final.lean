import HadwigerLean.Graph.Linkedness.Theorem
import HadwigerLean.Graph.Linkedness.RigidNoRigid
import Mathlib.Tactic

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Appendix D (L): every `16k`-vertex-connected graph is `k`-linked. -/
theorem kLinked_of_sixteen_mul_vertexConnected
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hconn : VertexConnected G (16 * k)) :
    KLinked G k := by
  by_cases hk : 0 < k
  · apply kLinked_of_connected_massed_reduction G k hk hconn
    intro X hX hm
    exact rootedLinked_of_massed G X k hk (by omega) hm
  · have hk0 : k = 0 := by omega
    subst k
    apply kLinked_of_rootedLinked G 0
    intro X hX
    exact rootedLinked_of_card_le_one G X (by omega)

end Linkedness
end HadwigerLean
