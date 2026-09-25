import HadwigerLean.Graph.RootedDensity.TorsoProjection
import HadwigerLean.Graph.Linkedness.Massed
import Mathlib.Tactic

/-!
# Lifting universality through a connected touching quotient

A rooted model in a quotient lifts through connected blocks whenever the
quotient does not identify distinct prescribed roots.
-/

namespace HadwigerLean.RootedDensity

universe u v w

/-- Universality at the image of a root set lifts through a connected
partition whose index map separates the roots. -/
theorem universalAt_of_connectedPartition
    {V : Type u} {I : Type v} {W : Type w}
    [Fintype V] [Fintype I] [Fintype W] [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) (P : ConnectedPartition G I)
    (H : SimpleGraph W) (X : Finset V)
    (f : V → I) (hfmem : ∀ x, x ∈ P.block (f x))
    (hfinj : Set.InjOn f (X : Set V))
    (huni : UniversalAt P.touchingQuotient H (X.image f)) :
    UniversalAt G H X := by
  classical
  intro Y root hrootinj hrange
  let qroot : ↥(Y : Set W) → I := f ∘ root
  have hqinj : Function.Injective qroot := by
    intro i j heq
    apply hrootinj
    apply hfinj
    · rw [← hrange]
      exact ⟨i, rfl⟩
    · rw [← hrange]
      exact ⟨j, rfl⟩
    · exact heq
  have hqrange : Set.range qroot = (X.image f : Set I) := by
    ext i
    simp only [Set.mem_range, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨y, rfl⟩
      have hyX : root y ∈ X := by
        change root y ∈ (X : Set V)
        rw [← hrange]
        exact ⟨y, rfl⟩
      exact ⟨root y, hyX, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have hx' : x ∈ (X : Set V) := hx
      rw [← hrange] at hx'
      obtain ⟨y, rfl⟩ := hx'
      exact ⟨y, rfl⟩
  obtain ⟨M⟩ := huni Y qroot hqinj hqrange
  exact ⟨M.liftThroughPartition P root (fun i => hfmem (root i))⟩

/-- The canonical quotient index sends each vertex into its connected
partition block. -/
theorem universalAt_of_partitionIndex
    {V : Type u} {I : Type v} {W : Type w}
    [Fintype V] [Fintype I] [Fintype W] [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) (P : ConnectedPartition G I)
    (H : SimpleGraph W) (X : Finset V)
    (hinj : Set.InjOn (Linkedness.partitionIndex P) (X : Set V))
    (huni : UniversalAt P.touchingQuotient H
      (X.image (Linkedness.partitionIndex P))) :
    UniversalAt G H X :=
  universalAt_of_connectedPartition G P H X (Linkedness.partitionIndex P)
    (Linkedness.partitionIndex_mem P) hinj huni


/-- A universal rooted model in a contraction lifts when at least one
endpoint of the contracted edge lies outside the prescribed root set. -/
theorem universalAt_of_edgeContraction
    {V : Type u} {W : Type w}
    [Fintype V] [Fintype W] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (X : Finset V)
    {a b : V} (hab : G.Adj a b) (hb : b ∉ X)
    (huni : UniversalAt (edgeContraction G hab) H
      (X.image (Linkedness.partitionIndex
        (edgeContractionPartition G hab)))) :
    UniversalAt G H X := by
  classical
  exact universalAt_of_partitionIndex G (edgeContractionPartition G hab)
    H X (Linkedness.edgeContraction_index_injOn_roots hab X hb) huni

/-- Contracting an edge that does not identify two roots preserves failure
of universality at the image root set. -/
theorem not_universalAt_edgeContraction
    {V : Type u} {W : Type w}
    [Fintype V] [Fintype W] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (X : Finset V)
    {a b : V} (hab : G.Adj a b) (hb : b ∉ X)
    (hbad : ¬ UniversalAt G H X) :
    ¬ UniversalAt (edgeContraction G hab) H
      (X.image (Linkedness.partitionIndex
        (edgeContractionPartition G hab))) := by
  intro huni
  exact hbad (universalAt_of_edgeContraction G H X hab hb huni)
end HadwigerLean.RootedDensity