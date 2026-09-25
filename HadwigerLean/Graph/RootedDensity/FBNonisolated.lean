import HadwigerLean.Graph.RootedDensity.FBExtremalCore
import HadwigerLean.Graph.RootedDensity.OutsideNonisolated
import Mathlib.Tactic

/-! Nonisolated exterior vertices in an extremal massed counterexample. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- Graph-order extremality rules out every isolated outside vertex. -/
theorem BadMassedWitness.outside_has_neighbor
    {W : Type v} [Fintype W] {H : SimpleGraph W} {α : ℝ}
    (B : BadMassedWitness.{u,v} H α)
    (hmin : ∀ B' : BadMassedWitness.{u,v} H α,
      B.order ≤ B'.order ∧
        (B.order = B'.order →
          B.outsideIncidence ≤ B'.outsideIncidence))
    (hα : 0 ≤ α) :
    ∀ z : B.Vertex, z ∉ B.roots →
      ∃ w : B.Vertex, B.graph.Adj z w := by
  classical
  letI : Fintype B.Vertex := B.fintype
  letI : DecidableEq B.Vertex := Classical.decEq _
  letI : DecidableRel B.graph.Adj := Classical.decRel _
  apply outside_has_neighbor_of_universal_vertex_deletions
    H B.graph B.roots α hα B.massed B.not_universal
  intro z hz
  dsimp
  let S : Set B.Vertex := {v | v ≠ z}
  letI : Fintype S := Fintype.ofFinite S
  let Y : Finset S := Finset.univ.filter
    (fun q : S => (q : B.Vertex) ∈ B.roots)
  intro hmY
  have horder : Fintype.card S < B.order := by
    have hlt : Nat.card {v : B.Vertex // v ≠ z} <
        Nat.card B.Vertex := by
      simpa only [Nat.card_eq_fintype_card] using
        (Linkedness.vertexDeletion_order_lt z)
    have hcS : Fintype.card S = Nat.card S :=
      Nat.card_eq_fintype_card.symm
    have hcB : B.order = Nat.card B.Vertex := by
      simp [BadMassedWitness.order, Nat.card_eq_fintype_card]
    rw [hcS, hcB]
    exact hlt
  have hYsub : Y.image Subtype.val ⊆ B.roots := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    simpa [Y] using hq
  have hYcard : Y.card ≤ Fintype.card W := by
    have hcard : Y.card ≤ B.roots.card := by
      rw [← Finset.card_image_of_injective Y Subtype.val_injective]
      exact Finset.card_le_card hYsub
    exact hcard.trans B.root_card
  exact B.universal_of_smaller_order hmin
    (B.graph.induce S) Y horder hYcard (by simpa [S,Y] using hmY)

end HadwigerLean.RootedDensity
