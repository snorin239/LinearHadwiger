import HadwigerLean.Graph.SetMengerTheorem
import Mathlib.Tactic

/-!
# Redundant Menger lemma

Each source has two paths to a target set. The two paths may meet at their
source but are otherwise disjoint across the family. A second such family
from a disjoint source set guarantees one disjoint target path per source.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A two-path fan from every source in `A` to `B`, with path interiors
outside `A ∪ C`. Different fan paths are disjoint outside `A`. -/
structure RedundantFan (G : SimpleGraph V) (A B C : Finset V) where
  finish : A × Fin 2 → V
  path : ∀ slot : A × Fin 2, G.Path slot.1.1 (finish slot)
  finish_mem : ∀ slot, finish slot ∈ B
  source_only : ∀ slot v, v ∈ pathVertexSet (path slot) →
    v ∈ A → v = slot.1.1
  avoids_other : ∀ slot v, v ∈ pathVertexSet (path slot) → v ∉ C
  disjoint_outside : Pairwise fun slot₁ slot₂ : A × Fin 2 =>
    Disjoint (pathVertexSet (path slot₁) \ (A : Set V))
      (pathVertexSet (path slot₂) \ (A : Set V))

namespace RedundantFan

/-- Any separator of `A ∪ C` from `B` has at least two exterior vertices
for each source of `A` that it does not itself delete. -/
theorem cut_card (G : SimpleGraph V) (A B C Q : Finset V)
    (F : RedundantFan G A B C)
    (hsep : SetMenger.IsABSeparator G (A ∪ C) B Q) :
    2 * (A \ Q).card ≤ (Q \ (A ∪ C)).card := by
  classical
  let slot : ↥(A \ Q) × Fin 2 → A × Fin 2 := fun d =>
    (⟨d.1.1, (Finset.mem_sdiff.mp d.1.2).1⟩, d.2)
  have slot_inj : Function.Injective slot := by
    intro x y h
    cases x with
    | mk x i =>
      cases y with
      | mk y j =>
        have hval : x.1 = y.1 := congrArg (fun z : A × Fin 2 => z.1.1) h
        have hij : i = j := congrArg Prod.snd h
        have hxy : x = y := Subtype.ext hval
        simp only [hxy, hij]
  let hit (d : ↥(A \ Q) × Fin 2) : V :=
    Classical.choose (hsep (slot d).1.1
      (Finset.mem_union_left C (slot d).1.2)
      (F.finish (slot d)) (F.finish_mem (slot d)) (F.path (slot d)))
  have hit_spec (d : ↥(A \ Q) × Fin 2) :
      hit d ∈ Q ∧ hit d ∈ pathVertexSet (F.path (slot d)) :=
    Classical.choose_spec (hsep (slot d).1.1
      (Finset.mem_union_left C (slot d).1.2)
      (F.finish (slot d)) (F.finish_mem (slot d)) (F.path (slot d)))
  have hit_out (d : ↥(A \ Q) × Fin 2) : hit d ∉ A ∪ C := by
    intro h
    rcases Finset.mem_union.mp h with hA | hC
    · have heq := F.source_only (slot d) (hit d) (hit_spec d).2 hA
      exact (Finset.mem_sdiff.mp d.1.2).2 (heq ▸ (hit_spec d).1)
    · exact F.avoids_other (slot d) (hit d) (hit_spec d).2 hC
  let f : ↥(A \ Q) × Fin 2 → ↥(Q \ (A ∪ C)) := fun d =>
    ⟨hit d, Finset.mem_sdiff.mpr ⟨(hit_spec d).1, hit_out d⟩⟩
  have finj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hslot : slot x ≠ slot y := fun h => hne (slot_inj h)
    have hdis := Set.disjoint_left.mp (F.disjoint_outside hslot)
    have hx : hit x ∈ pathVertexSet (F.path (slot x)) \ (A : Set V) :=
      ⟨(hit_spec x).2, fun hA => hit_out x (Finset.mem_union_left C hA)⟩
    have hy : hit x ∈ pathVertexSet (F.path (slot y)) \ (A : Set V) := by
      have heq : hit x = hit y := congrArg Subtype.val hxy
      exact ⟨heq ▸ (hit_spec y).2,
        fun hA => hit_out x (Finset.mem_union_left C hA)⟩
    exact hdis hx hy
  have hcard := Fintype.card_le_of_injective f finj
  change Fintype.card (↥(A \ Q) × Fin 2) ≤
    Fintype.card (↥(Q \ (A ∪ C))) at hcard
  rw [Fintype.card_prod, Fintype.card_fin,
    Fintype.card_coe (A \ Q), Fintype.card_coe (Q \ (A ∪ C))] at hcard
  omega

end RedundantFan

/-- Two redundant fans from disjoint source sets yield a vertex-disjoint
path from every source to the common target. -/
theorem exists_linkage_of_two_redundant_fans
    (G : SimpleGraph V) (A₁ A₂ B : Finset V)
    (hdis : Disjoint A₁ A₂)
    (F₁ : RedundantFan G A₁ B A₂)
    (F₂ : RedundantFan G A₂ B A₁) :
    ∃ (P : IndexedPairs (Fin (A₁.card + A₂.card)) V)
      (L : IndexedLinkage G P),
      SetMenger.IsABLinkage L (A₁ ∪ A₂) B := by
  classical
  have hcard_union : (A₁ ∪ A₂).card = A₁.card + A₂.card :=
    Finset.card_union_of_disjoint hdis
  apply SetMenger.exists_linkage_of_separator_lower_bound G (A₁ ∪ A₂) B
    (A₁.card + A₂.card)
  intro Q hsep
  by_contra hsmall
  have hq : Q.card < (A₁ ∪ A₂).card := by omega
  have houtside : (Q \ (A₁ ∪ A₂)).card < ((A₁ ∪ A₂) \ Q).card := by
    exact Finset.card_sdiff_lt_card_sdiff_iff.mpr hq
  have hsplit : ((A₁ ∪ A₂) \ Q).card =
      (A₁ \ Q).card + (A₂ \ Q).card := by
    have heq : (A₁ ∪ A₂) \ Q = (A₁ \ Q) ∪ (A₂ \ Q) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    rw [heq]
    apply Finset.card_union_of_disjoint
    exact Finset.disjoint_left.mpr (by intro x hx hy; exact (Finset.disjoint_left.mp hdis) (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hy).1)
  have h₁ := F₁.cut_card G A₁ B A₂ Q hsep
  have h₂ := F₂.cut_card G A₂ B A₁ Q (by simpa [Finset.union_comm] using hsep)
  rw [Finset.union_comm A₂ A₁] at h₂
  omega

end Woven
end HadwigerLean