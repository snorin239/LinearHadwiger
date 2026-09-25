import HadwigerLean.Graph.RootedDensity.LowCut
import HadwigerLean.Graph.RootedDensity.LowBranchVariable
import Mathlib.Tactic

/-! A small strict side of a low-order cut retains all but adhesion degree. -/

namespace HadwigerLean.RootedDensity

universe u

/-- Every neighbor of a strict-side vertex lies on its own side or in the
cut adhesion. The induced side loses at most the adhesion size in degree. -/
theorem degree_le_induce_strict_side_add_separator
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hcover : A ∪ B = Finset.univ)
    (hnocross : ∀ ⦃x y : V⦄, x ∈ A → x ∉ B → y ∈ B → y ∉ A → ¬ G.Adj x y)
    (v : ↥((A \ B : Finset V) : Set V)) :
    G.degree (v : V) ≤
      (G.induce ((A \ B : Finset V) : Set V)).degree v + (A ∩ B).card := by
  classical
  let N : Finset V := A \ B
  let Z : Finset V := A ∩ B
  have hvA : (v : V) ∈ A := (Finset.mem_sdiff.mp v.property).1
  have hvB : (v : V) ∉ B := (Finset.mem_sdiff.mp v.property).2
  have hnear : G.neighborFinset (v : V) \ N ⊆ Z := by
    intro y hy
    have hxy : G.Adj (v : V) y := (G.mem_neighborFinset _ _).mp
      (Finset.mem_sdiff.mp hy).1
    have hyN : y ∉ N := (Finset.mem_sdiff.mp hy).2
    have hyA : y ∈ A := by
      by_contra hya
      have hyB : y ∈ B := by
        have hc : y ∈ A ∪ B := by rw [hcover]; simp
        exact (Finset.mem_union.mp hc).resolve_left hya
      exact hnocross hvA hvB hyB hya hxy
    have hyB : y ∈ B := by
      by_contra hyb
      exact hyN (Finset.mem_sdiff.mpr ⟨hyA, hyb⟩)
    exact Finset.mem_inter.mpr ⟨hyA, hyB⟩
  have hfar : (G.neighborFinset (v : V) \ N).card ≤ Z.card :=
    Finset.card_le_card hnear
  let emb : ↥(N : Set V) ↪ V := Function.Embedding.subtype (· ∈ (N : Set V))
  have hmap : ((G.induce (N : Set V)).neighborFinset v).map emb =
      G.neighborFinset (v : V) ∩ N := by
    ext x
    simp [emb]
  have hdegN : (G.induce (N : Set V)).degree v =
      (G.neighborFinset (v : V) ∩ N).card := by
    have hcard := congrArg Finset.card hmap
    simpa only [Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree] using hcard
  have hsplit := Finset.card_inter_add_card_sdiff
    (G.neighborFinset (v : V)) N
  change G.degree (v : V) ≤ (G.induce (N : Set V)).degree v + Z.card
  rw [← G.card_neighborFinset_eq_degree, hdegN]
  omega

/-- A low-order cut has a nonempty strict side of at most half the vertices
outside the adhesion, with the inherited degree estimate. -/
theorem exists_small_strict_side_of_low_cut
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hcut : LowCut G k) :
    ∃ (N : Finset V) (t : ℕ),
      N.Nonempty ∧ t < k ∧
      2 * N.card + t ≤ Fintype.card V ∧
      (∀ v : ↥(N : Set V),
        G.degree (v : V) ≤ (G.induce (N : Set V)).degree v + t) := by
  classical
  obtain ⟨A, B, hcover, horder, hA, hB, hno⟩ := hcut
  let Z := A ∩ B
  let L := A \ B
  let R := B \ A
  have hsum : L.card + R.card + Z.card = Fintype.card V := by
    have hAB := Finset.card_union_add_card_inter A B
    rw [hcover, Finset.card_univ] at hAB
    have hAcard := Finset.card_sdiff_add_card_inter A B
    have hBcard := Finset.card_sdiff_add_card_inter B A
    have hZ : (B ∩ A).card = Z.card := by simp [Z, Finset.inter_comm]
    change Fintype.card V + Z.card = A.card + B.card at hAB
    change L.card + Z.card = A.card at hAcard
    rw [hZ] at hBcard
    change R.card + Z.card = B.card at hBcard
    omega
  have hRno : ∀ ⦃x y : V⦄, x ∈ B → x ∉ A → y ∈ A → y ∉ B → ¬ G.Adj x y := by
    intro x y hxB hxA hyA hyB hxy
    exact hno hyA hyB hxB hxA hxy.symm
  by_cases hsmall : L.card ≤ R.card
  · refine ⟨L, Z.card, hA, ?_, ?_, ?_⟩
    · exact horder
    · omega
    · intro v
      exact degree_le_induce_strict_side_add_separator G A B hcover hno v
  · refine ⟨R, Z.card, hB, ?_, ?_, ?_⟩
    · exact horder
    · omega
    · intro v
      simpa only [Finset.inter_comm] using
        degree_le_induce_strict_side_add_separator G B A
          (by simpa only [Finset.union_comm] using hcover) hRno v

end HadwigerLean.RootedDensity





