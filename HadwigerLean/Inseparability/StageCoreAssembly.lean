import HadwigerLean.Inseparability.RawModelFromLinkage
import Mathlib.Tactic

/-!
# The next CI core

The new core contains the old core, all small connected pieces (including
the knitting piece), and the selected middle-region tangencies. Its size
is bounded by the sum of those explicit contributions.
-/

namespace HadwigerLean.Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]

def ciNextCore (p x : ℕ) (oldCore : Finset V)
    (J : Fin p → Finset V) (D : Finset V)
    (root : CIRawIndex p x → V) : Finset V :=
  oldCore ∪ ((Finset.univ : Finset (Fin p)).biUnion J) ∪
    D ∪ Finset.univ.image root

theorem ciNextCore_old_subset (p x : ℕ) (oldCore : Finset V)
    (J : Fin p → Finset V) (D : Finset V)
    (root : CIRawIndex p x → V) :
    oldCore ⊆ ciNextCore p x oldCore J D root := by
  intro v hv
  exact Finset.mem_union_left _
    (Finset.mem_union_left _ (Finset.mem_union_left _ hv))

theorem ciNextCore_piece_subset (p x : ℕ) (oldCore : Finset V)
    (J : Fin p → Finset V) (D : Finset V)
    (root : CIRawIndex p x → V) (i : Fin p) :
    J i ⊆ ciNextCore p x oldCore J D root := by
  intro v hv
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hv⟩

theorem ciNextCore_D_subset (p x : ℕ) (oldCore : Finset V)
    (J : Fin p → Finset V) (D : Finset V)
    (root : CIRawIndex p x → V) :
    D ⊆ ciNextCore p x oldCore J D root := by
  intro v hv
  exact Finset.mem_union_left _ (Finset.mem_union_right _ hv)

theorem ciNextCore_root_mem (p x : ℕ) (oldCore : Finset V)
    (J : Fin p → Finset V) (D : Finset V)
    (root : CIRawIndex p x → V) (z : CIRawIndex p x) :
    root z ∈ ciNextCore p x oldCore J D root := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩

theorem ciNextCore_card_le (p x N oldBound : ℕ)
    (oldCore : Finset V) (J : Fin p → Finset V)
    (D : Finset V) (root : CIRawIndex p x → V)
    (hOld : oldCore.card ≤ oldBound)
    (hJ : ∀ i, (J i).card ≤ N)
    (hD : D.card ≤ N) :
    (ciNextCore p x oldCore J D root).card ≤
      oldBound + p * N + N + (p + 1) * x := by
  classical
  have hJunion :
      ((Finset.univ : Finset (Fin p)).biUnion J).card ≤ p * N := by
    simpa using Finset.card_biUnion_le_card_mul
      (Finset.univ : Finset (Fin p)) J N (fun i _ => hJ i)
  have hRoot : (Finset.univ.image root).card ≤ (p + 1) * x := by
    have h := Finset.card_image_le (s := Finset.univ) (f := root)
    simpa [CIRawIndex, Fintype.card_sum, Fintype.card_prod,
      add_mul] using h
  have h₁ := Finset.card_union_le oldCore
    ((Finset.univ : Finset (Fin p)).biUnion J)
  have h₂ := Finset.card_union_le
    (oldCore ∪ ((Finset.univ : Finset (Fin p)).biUnion J)) D
  have h₃ := Finset.card_union_le
    ((oldCore ∪ ((Finset.univ : Finset (Fin p)).biUnion J)) ∪ D)
    (Finset.univ.image root)
  unfold ciNextCore
  omega

end HadwigerLean.Inseparability
