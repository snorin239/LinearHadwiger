import HadwigerLean.Inseparability.CheapTree
import HadwigerLean.Woven.ThreeChildGN
import Mathlib.Tactic

/-!
# Cheap trees inside an ambient induced set

The cheap-tree theorem is applied to each branch on its subtype vertex type.
This lemma transports its two finite sets, connectivity, and chromatic bound
back to the ambient graph.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_cheap_tree_inside
    (G : SimpleGraph V) (B S : Finset V)
    (hBconn : (G.induce (B : Set V)).Connected)
    (hSB : S ⊆ B) (hS : S.Nonempty) :
    ∃ Q T : Finset V,
      S ⊆ T ∧ T ⊆ Q ∧ Q ⊆ B ∧ T.card ≤ 3 * S.card ∧
      (G.induce (Q : Set V)).Connected ∧
      chromatic (G.induce ((Q \ T : Finset V) : Set V)) ≤ 2 := by
  classical
  let S' : Finset (B : Set V) :=
    Finset.univ.filter (fun v : (B : Set V) => (v : V) ∈ S)
  have hSimage : S'.image Subtype.val = S := by
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hw).2
    · intro hv
      apply Finset.mem_image.mpr
      exact ⟨⟨v, hSB hv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
  have hS' : S'.Nonempty := by
    obtain ⟨v, hv⟩ := hS
    exact ⟨⟨v, hSB hv⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
  have hScard : S'.card = S.card := by
    rw [← hSimage]
    exact (Finset.card_image_of_injective _ Subtype.val_injective).symm
  obtain ⟨Q',T',hS'T,hT'Q,hTcard,hQconn,hrem⟩ :=
    exists_cheap_tree hBconn S' hS'
  let Q : Finset V := Woven.nestedImageFinset B Q'
  let T : Finset V := Woven.nestedImageFinset B T'
  have hST : S ⊆ T := by
    rw [← hSimage]
    exact Finset.image_subset_image hS'T
  have hTQ : T ⊆ Q := Finset.image_subset_image hT'Q
  have hQB : Q ⊆ B := Woven.nestedImageFinset_subset B Q'
  have hTcard' : T.card ≤ 3 * S.card := by
    have hcard : T.card = T'.card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    rw [hcard, ← hScard]
    exact hTcard
  have hQconn' : (G.induce (Q : Set V)).Connected := by
    let e := Woven.nestedInducedIso G B Q'
    exact hQconn.map e.toHom e.surjective
  have hdiff : Woven.nestedImageFinset B (Q' \ T') = Q \ T := by
    exact Finset.image_sdiff Q' T' Subtype.val_injective
  have hrem' :
      chromatic (G.induce ((Q \ T : Finset V) : Set V)) ≤ 2 := by
    have heq := Woven.chromatic_nested_image G (B : Set V)
      ((Q' \ T' : Finset (B : Set V)) : Set (B : Set V))
    have hset : Subtype.val ''
        ((Q' \ T' : Finset (B : Set V)) : Set (B : Set V)) =
        (Woven.nestedImageFinset B (Q' \ T') : Set V) := by
      exact (Woven.nestedImageFinset_coe B (Q' \ T')).symm
    rw [hset, hdiff] at heq
    exact heq ▸ hrem
  exact ⟨Q,T,hST,hTQ,hQB,hTcard',hQconn',hrem'⟩

end Inseparability
end HadwigerLean
