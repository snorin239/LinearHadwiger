import HadwigerLean.Inseparability.StageConnectors
import Mathlib.Tactic

/-!
# Paired clean connectors for the CI middle region

The second family has two disjoint paths per eventual new source. Pairing
the Menger indices preserves its clean endpoints and deletion avoidance.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_clean_paired_connectors_after_delete
    (G : SimpleGraph V) (R W A B : Finset V) (k s : ℕ)
    (hconn : VertexConnected (G.induce (R : Set V)) k)
    (hWR : W ⊆ R) (hbudget : W.card + 2 * s ≤ k)
    (hA : A ⊆ R \ W) (hB : B ⊆ R \ W)
    (hAcard : 2 * s ≤ A.card) (hBcard : 2 * s ≤ B.card) :
    ∃ (P : IndexedPairs (Fin s × Fin 2) V)
      (L : IndexedLinkage G P),
      SetMenger.IsABLinkage L A B ∧
      (∀ slot, pathVertexSet (L.path slot) ⊆
        ((R \ W : Finset V) : Set V)) ∧
      (∀ slot v, v ∈ pathVertexSet (L.path slot) →
        v ∈ A → v = P.start slot) ∧
      (∀ slot v, v ∈ pathVertexSet (L.path slot) →
        v ∈ B → v = P.finish slot) := by
  obtain ⟨P₀,L₀,hAB,hR,honlyA,honlyB⟩ :=
    exists_clean_connectors_after_delete G R W A B k (2 * s)
      hconn hWR hbudget hA hB hAcard hBcard
  let e : Fin s × Fin 2 ≃ Fin (2 * s) :=
    finProdFinEquiv.trans (finCongr (by omega : s * 2 = 2 * s))
  let P := P₀.reindex e.toEmbedding
  let L := L₀.reindex e.toEmbedding
  refine ⟨P,L,?_,?_,?_,?_⟩
  · exact ⟨fun slot => hAB.1 (e slot), fun slot => hAB.2 (e slot)⟩
  · exact fun slot => hR (e slot)
  · exact fun slot v hv hvA => honlyA (e slot) v hv hvA
  · exact fun slot v hv hvB => honlyB (e slot) v hv hvB

end Inseparability
end HadwigerLean
