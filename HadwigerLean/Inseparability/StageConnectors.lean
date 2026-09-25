import HadwigerLean.Inseparability.StageDeletion
import HadwigerLean.Woven.ConnectorClean

/-!
# Clean connectors after deleting a reserved set

This is the second linkage in the chromatic inseparability stage: remove
the reserved sources, spend the corresponding connectivity budget, and
link the middle connected region to the final small piece.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_clean_connectors_after_delete
    (G : SimpleGraph V) (R W A B : Finset V) (k m : ℕ)
    (hconn : VertexConnected (G.induce (R : Set V)) k)
    (hWR : W ⊆ R) (hbudget : W.card + m ≤ k)
    (hA : A ⊆ R \ W) (hB : B ⊆ R \ W)
    (hAcard : m ≤ A.card) (hBcard : m ≤ B.card) :
    ∃ (P : IndexedPairs (Fin m) V) (L : IndexedLinkage G P),
      SetMenger.IsABLinkage L A B ∧
      (∀ i, pathVertexSet (L.path i) ⊆ ((R \ W : Finset V) : Set V)) ∧
      (∀ i v, v ∈ pathVertexSet (L.path i) → v ∈ A → v = P.start i) ∧
      (∀ i v, v ∈ pathVertexSet (L.path i) → v ∈ B → v = P.finish i) := by
  have hresidual :
      VertexConnected (G.induce ((R \ W : Finset V) : Set V)) m :=
    vertexConnected_induce_sdiff R W k m hconn hWR hbudget
  exact Woven.exists_clean_connectors_inside G (R \ W) A B m m
    hresidual (Nat.le_refl m) hA hB hAcard hBcard

end Inseparability
end HadwigerLean
