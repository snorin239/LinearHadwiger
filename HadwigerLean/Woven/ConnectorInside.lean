import HadwigerLean.Woven.ConnectorMenger
import HadwigerLean.Woven.ThreeChildGNIso
import Mathlib.Tactic

/-!
# Disjoint connectors inside an induced connected region

This maps a set-to-set Menger linkage from an induced graph to ambient
vertices while retaining support inside the selected region.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_disjoint_connectors_inside
    (G : SimpleGraph V) (R A B : Finset V) (k m : ℕ)
    (hconn : VertexConnected (G.induce (R : Set V)) k)
    (hm : m ≤ k) (hAR : A ⊆ R) (hBR : B ⊆ R)
    (hA : m ≤ A.card) (hB : m ≤ B.card) :
    ∃ (P : IndexedPairs (Fin m) V) (L : IndexedLinkage G P),
      SetMenger.IsABLinkage L A B ∧
      ∀ i, pathVertexSet (L.path i) ⊆ (R : Set V) := by
  classical
  let A' : Finset (R : Set V) :=
    Finset.univ.filter (fun z : (R : Set V) => (z : V) ∈ A)
  let B' : Finset (R : Set V) :=
    Finset.univ.filter (fun z : (R : Set V) => (z : V) ∈ B)
  have hAimage : A'.image Subtype.val = A := by
    ext v
    constructor
    · intro hv
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hz).2
    · intro hv
      exact Finset.mem_image.mpr
        ⟨⟨v,hAR hv⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,rfl⟩
  have hBimage : B'.image Subtype.val = B := by
    ext v
    constructor
    · intro hv
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hz).2
    · intro hv
      exact Finset.mem_image.mpr
        ⟨⟨v,hBR hv⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,rfl⟩
  have hAcard : A'.card = A.card := by
    rw [← hAimage]
    exact (Finset.card_image_of_injective _ Subtype.val_injective).symm
  have hBcard : B'.card = B.card := by
    rw [← hBimage]
    exact (Finset.card_image_of_injective _ Subtype.val_injective).symm
  obtain ⟨P₀,L₀,hAB⟩ := exists_disjoint_connectors_of_vertexConnected
    (G.induce (R : Set V)) A' B' k m hconn hm
    (by rw [hAcard]; exact hA)
    (by rw [hBcard]; exact hB)
  let e : (G.induce (R : Set V)) ↪g G :=
    SimpleGraph.Embedding.induce (R : Set V)
  let P : IndexedPairs (Fin m) V := P₀.map Subtype.val
  let L : IndexedLinkage G P := L₀.map e.toHom e.injective
  refine ⟨P,L,?_,?_⟩
  · constructor
    · intro i
      exact hAimage ▸ Finset.mem_image.mpr
        ⟨P₀.start i,hAB.1 i,rfl⟩
    · intro i
      exact hBimage ▸ Finset.mem_image.mpr
        ⟨P₀.finish i,hAB.2 i,rfl⟩
  · intro i v hv
    change v ∈ pathVertexSet ((L₀.path i).map e.toHom e.injective) at hv
    rw [pathVertexSet.map] at hv
    obtain ⟨z, _, rfl⟩ := hv
    exact z.property

end Woven
end HadwigerLean

