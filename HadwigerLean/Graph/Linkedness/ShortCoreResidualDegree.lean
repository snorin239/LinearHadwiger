import HadwigerLean.Graph.Linkedness.ShortCoreOccupancy
import Mathlib.Tactic

/-!
# Order and degree of the residual graph after short partial paths
-/

namespace HadwigerLean
namespace Linkedness
namespace ShortPartial

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {k : ℕ} {P : IndexedPairs (Fin k) V}

/-- Deleting the occupied set removes at least the `2k` distinct terminals. -/
theorem residual_order_le_fourteen_mul
    (C : ShortPartial G P (terminalFinset P))
    (hP : P.DisjointTerminals)
    (hne : ∀ i, P.start i ≠ P.finish i)
    (horder : Fintype.card V ≤ 16 * k) :
    Fintype.card (↥((C.occupied : Set V)ᶜ)) ≤ 14 * k := by
  classical
  have hX : (terminalFinset P).card = 2 * k :=
    terminalFinset_card_eq_two_mul k P hP hne
  have hsub := Finset.card_le_card C.terminal_subset_occupied
  have hsplit := Finset.card_compl_add_card C.occupied
  have hcard : Fintype.card (↥((C.occupied : Set V)ᶜ)) =
      C.occupiedᶜ.card := by
    apply Fintype.card_of_finset' (C.occupiedᶜ)
    intro v
    simp
  rw [hcard]
  omega

/-- The induced residual degree is the number of original neighbors
outside the occupied set. -/
theorem residual_degree_eq_outside_neighbors
    (C : ShortPartial G P (terminalFinset P))
    (v : ↥((C.occupied : Set V)ᶜ)) :
    (G.induce ((C.occupied : Set V)ᶜ)).degree v =
      (G.neighborFinset v.1 \ C.occupied).card := by
  classical
  let S : Set V := (C.occupied : Set V)ᶜ
  let e : S ↪ V := Function.Embedding.subtype (· ∈ S)
  have hmap : ((G.induce S).neighborFinset v).map e =
      G.neighborFinset v.1 \ C.occupied := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
      have hadj : G.Adj v.1 u.1 :=
        ((G.induce S).mem_neighborFinset v u).mp hu
      exact Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset v.1 u.1).mpr hadj,
        u.property⟩
    · intro hx
      have hadj : G.Adj v.1 x :=
        (G.mem_neighborFinset v.1 x).mp (Finset.mem_sdiff.mp hx).1
      let u : S := ⟨x, (Finset.mem_sdiff.mp hx).2⟩
      have hu : u ∈ (G.induce S).neighborFinset v :=
        ((G.induce S).mem_neighborFinset v u).mpr hadj
      exact Finset.mem_map.mpr ⟨u, hu, rfl⟩
  calc
    (G.induce S).degree v = ((G.induce S).neighborFinset v).card :=
      ((G.induce S).card_neighborFinset_eq_degree v).symm
    _ = (((G.induce S).neighborFinset v).map e).card := by
      rw [Finset.card_map]
    _ = (G.neighborFinset v.1 \ C.occupied).card :=
      congrArg Finset.card hmap

/-- Minimum degree `8k` in the original graph leaves minimum degree `5k`
after deleting the occupied set of an optimal partial linkage. -/
theorem residual_min_degree_ge_five_mul
    (C : ShortPartial G P (terminalFinset P))
    (hP : P.DisjointTerminals)
    (hne : ∀ i, P.start i ≠ P.finish i)
    (hminimal : ∀ D : ShortPartial G P (terminalFinset P),
      D.used.card = C.used.card → C.totalLength ≤ D.totalLength)
    (hdeg : ∀ v, 8 * k ≤ G.degree v)
    (v : ↥((C.occupied : Set V)ᶜ)) :
    5 * k ≤ (G.induce ((C.occupied : Set V)ᶜ)).degree v := by
  classical
  have hocc : (G.neighborFinset v.1 ∩ C.occupied).card ≤ 3 * k :=
    C.outside_occupied_neighbor_card_le_three_mul hP hne hminimal v.1 v.property
  have hsplit := Finset.card_inter_add_card_sdiff (G.neighborFinset v.1) C.occupied
  have hdegree := hdeg v.1
  rw [C.residual_degree_eq_outside_neighbors v]
  change (G.neighborFinset v.1).card ≥ 8 * k at hdegree
  omega

end ShortPartial
end Linkedness
end HadwigerLean
