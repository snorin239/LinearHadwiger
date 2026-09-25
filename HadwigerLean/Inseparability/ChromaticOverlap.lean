import HadwigerLean.Bootstrap.Definitions
import HadwigerLean.Woven.DoubleFanCost

/-!
# Chromatic inseparability forces overlap

If two induced regions both retain nearly all colors, and one can pay for
deleting fewer than `k` shared vertices from the second, their intersection
must contain at least `k` vertices. This is the chromatic half of the final
`H₃ ∪ H₅` step.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

/-- Failure of chromatic separability forces two high-chromatic regions to
have a large overlap. -/
theorem overlap_card_ge_of_chromatic_inseparable
    (A B : Finset V) (k m : ℕ)
    (hinsep : ¬ Bootstrap.ChromaticSeparable G m)
    (hχA : chromatic G ≤ chromatic (G.induce (A : Set V)) + m)
    (hχB : chromatic G ≤ chromatic (G.induce (B : Set V)) + m / 2)
    (hbudget : m / 2 + k ≤ m) :
    k ≤ (A ∩ B).card := by
  classical
  by_contra hsmall
  have hIk : (A ∩ B).card < k := by omega
  have hIχ : chromatic (G.induce ((A ∩ B : Finset V) : Set V)) ≤
      (A ∩ B).card := by
    have hcard : Fintype.card (↥(((A ∩ B : Finset V) : Set V))) =
        (A ∩ B).card := by
      apply Fintype.card_of_finset' (A ∩ B)
      intro v
      rfl
    simpa only [hcard] using chromatic_le_card
      (G.induce ((A ∩ B : Finset V) : Set V))
  have hcost := Woven.chromatic_induce_le_add_remainder G
    (B : Set V) ((A ∩ B : Finset V) : Set V)
  have hset : (B : Set V) \ ((A ∩ B : Finset V) : Set V) =
      ((B \ A : Finset V) : Set V) := by
    ext v
    simp only [Set.mem_sdiff, Finset.mem_coe, Finset.mem_inter,
      Finset.mem_sdiff]
    tauto
  rw [hset] at hcost
  have hχR : chromatic G ≤
      chromatic (G.induce ((B \ A : Finset V) : Set V)) + m := by
    omega
  have hdis : Disjoint (A : Set V) ((B \ A : Finset V) : Set V) := by
    apply Set.disjoint_left.mpr
    intro v hvA hvR
    exact (Finset.mem_sdiff.mp hvR).2 hvA
  exact hinsep ⟨(A : Set V),((B \ A : Finset V) : Set V),
    hdis,hχA,hχR⟩

end Inseparability
end HadwigerLean


