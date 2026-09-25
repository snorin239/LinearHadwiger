import HadwigerLean.Woven.DoubleFanCost
import HadwigerLean.Graph.ChromaticSlice
import Mathlib.Tactic

/-!
# Coloring the trimmed clique-model branches

Each branch remainder uses two colors, with a private palette for each
branch. A shared marked set accounts for every other model vertex.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

/-- An induced union costs at most the sum of the two chromatic numbers. -/
theorem chromatic_induce_union_le_add
    (G : SimpleGraph V) (A B : Finset V) :
    chromatic (G.induce ((A ∪ B : Finset V) : Set V)) ≤
      chromatic (G.induce (A : Set V)) +
        chromatic (G.induce (B : Set V)) := by
  have h := Woven.chromatic_induce_le_add_remainder G
    ((A ∪ B : Finset V) : Set V) (A : Set V)
  have hdiff : (((A ∪ B : Finset V) : Set V) \ (A : Set V)) =
      ((B \ A : Finset V) : Set V) := by
    ext v
    simp only [Set.mem_sdiff, Finset.mem_coe, Finset.mem_union,
      Finset.mem_sdiff]
    tauto
  rw [hdiff] at h
  have hmono := chromatic_induce_mono_finset G
    (S := B \ A) (T := B) Finset.sdiff_subset
  omega

/-- A finite union of induced pieces that each need at most two colors
needs at most two colors per piece. -/
theorem chromatic_biUnion_le_two_mul
    {ι : Type*} [Fintype ι]
    (G : SimpleGraph V) (R : ι → Finset V)
    (hR : ∀ i, chromatic (G.induce (R i : Set V)) ≤ 2)
    (F : Finset ι) :
    chromatic (G.induce ((F.biUnion R : Finset V) : Set V)) ≤
      2 * F.card := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    have hχ : chromatic (G.induce ((∅ : Finset V) : Set V)) = 0 := by
      haveI : IsEmpty (↥((∅ : Finset V) : Set V)) := by
        refine ⟨fun z => ?_⟩
        simpa using z.property
      exact (chromatic_eq_zero_iff _).mpr inferInstance
    simpa [hχ]
  | @insert i F hi ih =>
    have h := chromatic_induce_union_le_add G (R i) (F.biUnion R)
    have hbound := hR i
    have hcard : (insert i F).card = F.card + 1 := by simp [hi]
    have hbi : (insert i F).biUnion R = R i ∪ F.biUnion R := by simp
    rw [hbi,hcard]
    omega

/-- The model union has chromatic number at most the marked-set cost plus
two colors for each trimmed branch. -/
theorem chromatic_model_union_le_marked_add_two_mul
    (G : SimpleGraph V) {s L : ℕ}
    (Q T : Fin s → Finset V)
    (hrem : ∀ i,
      chromatic (G.induce ((Q i \ T i : Finset V) : Set V)) ≤ 2)
    (hmark : chromatic (G.induce
      (((Finset.univ : Finset (Fin s)).biUnion T : Finset V) : Set V)) ≤ L) :
    chromatic (G.induce
      (((Finset.univ : Finset (Fin s)).biUnion Q : Finset V) : Set V)) ≤
      L + 2 * s := by
  classical
  let A : Finset V := (Finset.univ : Finset (Fin s)).biUnion Q
  let X : Finset V := (Finset.univ : Finset (Fin s)).biUnion T
  let R : Fin s → Finset V := fun i => Q i \ T i
  let U : Finset V := (Finset.univ : Finset (Fin s)).biUnion R
  have hsub : A \ X ⊆ U := by
    intro v hv
    obtain ⟨i,hi,hvQ⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hv).1
    apply Finset.mem_biUnion.mpr
    refine ⟨i,hi,Finset.mem_sdiff.mpr ⟨hvQ,?_⟩⟩
    intro hvT
    exact (Finset.mem_sdiff.mp hv).2
      (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hvT⟩)
  have hUχ : chromatic (G.induce (U : Set V)) ≤ 2 * s := by
    have h := chromatic_biUnion_le_two_mul G R hrem Finset.univ
    simpa [U] using h
  have hAXχ : chromatic (G.induce ((A \ X : Finset V) : Set V)) ≤
      2 * s :=
    (chromatic_induce_mono_finset G hsub).trans hUχ
  have hsplit := Woven.chromatic_induce_le_add_remainder G
    (A : Set V) (X : Set V)
  have hdiff : (A : Set V) \ (X : Set V) =
      ((A \ X : Finset V) : Set V) := by
    ext v
    simp
  rw [hdiff] at hsplit
  have hmark' : chromatic (G.induce (X : Set V)) ≤ L := hmark
  change chromatic (G.induce (A : Set V)) ≤ L + 2 * s
  omega

end Inseparability
end HadwigerLean


