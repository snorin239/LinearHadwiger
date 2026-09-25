import HadwigerLean.Inseparability.SmallPiecesSC
import HadwigerLean.Woven.ThreeChildGN
import Mathlib.Tactic

/-!
# Disjoint small connected pieces inside a specified residual set

The SC packing theorem is applied to an induced residual graph, and each
piece is transported back to ambient vertices. This is the form needed after
deleting the previous stage's tangency vertices.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_disjoint_small_connected_pieces_inside_of_SC
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (t k r N q : ℕ)
    (ht : 3 ≤ t) (htk : t ≤ k)
    (hminor : ¬ HasCliqueMinor G t)
    (hsize : (480 * 6400 : ℝ)^2 * (t : ℝ) *
      (Real.log (t : ℝ))^3 ≤ (N : ℝ))
    (hlocal : ∀ U : Finset V, U ⊆ R → U.card ≤ r * N →
      chromatic (G.induce (U : Set V)) ≤ q)
    (hχ : q + 2 * (480 * 6400 * k) <
      chromatic (G.induce (R : Set V))) :
    ∃ J : Fin r → Finset V,
      (∀ i, J i ⊆ R ∧ (J i).card ≤ N ∧
        VertexConnected (G.induce (J i : Set V)) k) ∧
      (Pairwise fun i j => Disjoint (J i) (J j)) := by
  classical
  let H := G.induce (R : Set V)
  have hminorH : ¬ HasCliqueMinor H t := by
    intro hm
    exact hminor (hasCliqueMinor_of_minor (induce_isMinor G (R : Set V)) hm)
  have hlocalH : ∀ U : Finset (R : Set V), U.card ≤ r * N →
      chromatic (H.induce (U : Set (R : Set V))) ≤ q := by
    intro U hU
    let W := Woven.nestedImageFinset R U
    have hWR : W ⊆ R := Woven.nestedImageFinset_subset R U
    have hWcard : W.card = U.card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    have hχW := hlocal W hWR (by omega)
    have hχeq : chromatic (H.induce (U : Set (R : Set V))) =
        chromatic (G.induce (W : Set V)) := by
      change chromatic ((G.induce (R : Set V)).induce
        (U : Set (R : Set V))) =
        chromatic (G.induce (Woven.nestedImageFinset R U : Set V))
      rw [Woven.nestedImageFinset_coe]
      exact Woven.chromatic_nested_image G (R : Set V)
        (U : Set (R : Set V))
    rw [hχeq]
    exact hχW
  obtain ⟨K,hK,hKdisj⟩ :=
    exists_disjoint_small_connected_pieces_of_SC
      H t k r N q ht htk hminorH hsize hlocalH hχ
  let J : Fin r → Finset V := fun i => Woven.nestedImageFinset R (K i)
  refine ⟨J, ?_, ?_⟩
  · intro i
    have hcard : (J i).card = (K i).card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    refine ⟨Woven.nestedImageFinset_subset R (K i), ?_, ?_⟩
    · rw [hcard]
      exact (hK i).1
    · exact VertexConnected.of_iso
        (Woven.nestedInducedIso G R (K i)) k (hK i).2
  · intro i j hij
    exact (Finset.disjoint_image Subtype.val_injective).mpr (hKdisj hij)

end Inseparability
end HadwigerLean

