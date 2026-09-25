import HadwigerLean.Inseparability.StageChildRerouting
import Mathlib.Data.Fintype.EquivFin

/-!
# Choosing two rows of distinct roots in each child piece

Each k-connected small piece has more than k vertices, so the numerical
budget `2x ≤ k` supplies the prescribed `Fin 2 × Fin x` root array.
-/

namespace HadwigerLean.Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_child_roots_in_pieces
    (p x : ℕ) (J : Fin p → Finset V)
    (hcard : ∀ i, 2 * x ≤ (J i).card) :
    ∃ root : Fin p → Fin 2 × Fin x → V,
      (∀ i, Function.Injective (root i)) ∧
      (∀ i z, root i z ∈ J i) := by
  classical
  have hchoose (i : Fin p) :
      ∃ f : (Fin 2 × Fin x) ↪ V, Set.range f ⊆ (J i : Set V) := by
    apply Function.Embedding.exists_of_card_le_finset
    simpa [Fintype.card_prod] using hcard i
  choose f hf using hchoose
  exact ⟨(fun i z => f i z),fun i => (f i).injective,
    fun i z => hf i ⟨z,rfl⟩⟩

theorem exists_child_roots_of_connected_pieces
    (G : SimpleGraph V) (p x k : ℕ)
    (J : Fin p → Finset V)
    (hconn : ∀ i, VertexConnected (G.induce (J i : Set V)) k)
    (hbudget : 2 * x ≤ k) :
    ∃ root : Fin p → Fin 2 × Fin x → V,
      (∀ i, Function.Injective (root i)) ∧
      (∀ i z, root i z ∈ J i) := by
  apply exists_child_roots_in_pieces p x J
  intro i
  have horder := (hconn i).order_gt
  have hcard : Fintype.card (J i : Set V) = (J i).card := by
    apply Fintype.card_of_finset' (J i)
    intro v
    rfl
  rw [hcard] at horder
  omega

end HadwigerLean.Inseparability

