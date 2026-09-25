import HadwigerLean.Woven.ThreeChildRootedBridge
import HadwigerLean.Graph.NeighborProxies

/-!
# Distinct starts for the parent connectors

Each parent root needs two separate neighbors. The ordinary proxy selection
lemma supplies them simultaneously, even though each root occurs twice.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Forget whether a connector is the first or second copy of its root. -/
def connectorParent {a : ℕ} (q : Fin (2 * a)) : Fin a :=
  if h : q.val < a then ⟨q.val, h⟩ else
    ⟨q.val - a, by have hq := q.isLt; omega⟩

@[simp] theorem connectorParent_first {a : ℕ} (i : Fin a) :
    connectorParent (firstConnector i) = i := by
  apply Fin.ext
  simp [connectorParent, firstConnector, i.isLt]

@[simp] theorem connectorParent_second {a : ℕ} (i : Fin a) :
    connectorParent (secondConnector i) = i := by
  apply Fin.ext
  simp [connectorParent, secondConnector]

/-- Minimum degree `4a` supplies two distinct starts per root, all avoiding
the parent roots. The child sets may then be selected away from these starts. -/
theorem exists_parent_connector_starts
    (G : SimpleGraph V) [DecidableRel G.Adj] {a : ℕ}
    (root : Fin a → V)
    (hdegree : ∀ i, 4 * a ≤ G.degree (root i)) :
    ∃ start : Fin (2 * a) → V,
      Function.Injective start ∧
      (∀ q i, start q ≠ root i) ∧
      (∀ i, G.Adj (root i) (start (firstConnector i))) ∧
      (∀ i, G.Adj (root i) (start (secondConnector i))) := by
  let role : Fin (2 * a) → V := root ∘ connectorParent
  have hdegree' : ∀ q, 2 * (2 * a) ≤ G.degree (role q) := by
    intro q
    change 2 * (2 * a) ≤ G.degree (root (connectorParent q))
    have heq : 2 * (2 * a) = 4 * a := by omega
    rw [heq]
    exact hdegree (connectorParent q)
  obtain ⟨start, hinj, hadj, hav⟩ :=
    exists_distinct_neighbor_proxies_for_roles G (2 * a) role hdegree'
  refine ⟨start, hinj, ?_, ?_, ?_⟩
  · intro q i heq
    have hrange : ∃ r, connectorParent r = i :=
      ⟨firstConnector i, connectorParent_first i⟩
    obtain ⟨r, hr⟩ := hrange
    exact hav q r (by simpa [role, hr] using heq)
  · intro i
    simpa [role] using hadj (firstConnector i)
  · intro i
    simpa [role] using hadj (secondConnector i)

end Woven
end HadwigerLean
