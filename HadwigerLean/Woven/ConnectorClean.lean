import HadwigerLean.Woven.ConnectorInside
import HadwigerLean.Woven.MixedFanTrim

/-!
# Clean disjoint connectors inside an induced region

Menger gives disjoint paths between the two endpoint sets. Trimming each
path at its last source-set visit and first target-set visit makes both
intersections exact while preserving disjointness and region support.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_clean_connectors_inside
    (G : SimpleGraph V) (R A B : Finset V) (k m : ℕ)
    (hconn : VertexConnected (G.induce (R : Set V)) k)
    (hm : m ≤ k) (hAR : A ⊆ R) (hBR : B ⊆ R)
    (hA : m ≤ A.card) (hB : m ≤ B.card) :
    ∃ (P : IndexedPairs (Fin m) V) (L : IndexedLinkage G P),
      SetMenger.IsABLinkage L A B ∧
      (∀ i, pathVertexSet (L.path i) ⊆ (R : Set V)) ∧
      (∀ i v, v ∈ pathVertexSet (L.path i) → v ∈ A → v = P.start i) ∧
      (∀ i v, v ∈ pathVertexSet (L.path i) → v ∈ B → v = P.finish i) := by
  obtain ⟨P₀,L₀,hAB₀,hR₀⟩ :=
    exists_disjoint_connectors_inside G R A B k m hconn hm hAR hBR hA hB
  obtain ⟨P₁,L₁,hA₁,hfinish₁,hsub₁,honlyA₁⟩ :=
    IndexedLinkage.exists_trimStartFromSet L₀ A hAB₀.1
  have hB₁ (i) : P₁.finish i ∈ B := by
    rw [hfinish₁]
    exact hAB₀.2 i
  obtain ⟨P₂,L₂,hstart₂,hB₂,hsub₂,honlyB₂⟩ :=
    IndexedLinkage.exists_trimFinishToSet L₁ hB₁
  refine ⟨P₂,L₂,?_,?_,?_,honlyB₂⟩
  · constructor
    · intro i
      rw [hstart₂]
      exact hA₁ i
    · exact hB₂
  · intro i v hv
    exact hR₀ i (hsub₁ i (hsub₂ i hv))
  · intro i v hv hvA
    rw [hstart₂]
    exact honlyA₁ i v (hsub₂ i hv) hvA

end Woven
end HadwigerLean
