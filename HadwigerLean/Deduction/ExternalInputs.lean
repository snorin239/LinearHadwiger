import HadwigerLean.Bootstrap.Definitions
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# The two external inputs for the conditional Theorem 1 deduction

`Theorem4Statement` is the exact maximum-ratio form of the Delcourt--Postle
small-graph reduction. Its `H` ranges over arbitrary Mathlib subgraphs of
`G`, with the induced vertex type of `H.coe`. `Corollary24Statement` is the
outer-recursion bound at the least power-of-three scale. Neither proposition
is asserted as an axiom.
-/

namespace HadwigerLean.Deduction

open HadwigerLean.Bootstrap

universe u

/-- The ratios occurring in the maximum in paper Theorem 4. The zero member
implements the paper's explicit union with `{0}`. -/
noncomputable def theorem4RatioSet {V : Type u} [Fintype V]
    (G : SimpleGraph V) (C t : ℕ) : Set ℝ := by
  classical
  exact {0} ∪ {r : ℝ | ∃ (a : ℕ) (H : G.Subgraph),
    (t : ℝ) / Real.sqrt (Real.log (t : ℝ)) ≤ (a : ℝ) ∧
    a ≤ t ∧
    ¬ HadwigerLean.HasCliqueMinor H.coe a ∧
    (Fintype.card H.verts : ℝ) ≤
      (C : ℝ) * (a : ℝ) * (Real.log (a : ℝ)) ^ (4 : ℝ) ∧
    r = (HadwigerLean.chromatic H.coe : ℝ) / (a : ℝ)}

/-- The finite-graph maximum `f(G,t)` from paper Theorem 4, expressed as a
real supremum of the displayed ratios and zero. -/
noncomputable def theorem4MaxRatio {V : Type u} [Fintype V]
    (G : SimpleGraph V) (C t : ℕ) : ℝ :=
  sSup (theorem4RatioSet G C t)

/-- Paper Theorem 4, kept as a proposition rather than a global axiom. The
same `C` occurs in the coefficient and in the order cutoff. -/
def Theorem4Statement : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧
    ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (t : ℕ),
      3 ≤ t → ¬ HadwigerLean.HasCliqueMinor G t →
      (HadwigerLean.chromatic G : ℝ) ≤
        (C : ℝ) * (t : ℝ) * (1 + theorem4MaxRatio G C t)

/-- Paper Corollary 24, conditional on its exact outer-separation premise.
The quantification over `T` requires it to be the least power of three above
`t`; `OuterSeparation` retains every eligible integer recursion scale. -/
def Corollary24Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (t T d : ℕ),
    100 ≤ t → IsLeastPowerOfThreeAtLeast t T → 1 ≤ d →
    ¬ HadwigerLean.HasCliqueMinor G t → OuterSeparation G T d →
    HadwigerLean.chromatic G <
      3 * (10 ^ 6 * (d + 1) + 62000) * t

/-- The displayed ratio set contains zero. -/
theorem theorem4RatioSet_nonempty {V : Type u} [Fintype V]
    (G : SimpleGraph V) (C t : ℕ) :
    (theorem4RatioSet G C t).Nonempty := by
  refine ⟨0, ?_⟩
  simp [theorem4RatioSet]


/-- The ratio set is bounded above by the host order, so its supremum is the
ordinary finite maximum intended by the paper. -/
theorem theorem4RatioSet_bddAbove {V : Type u} [Fintype V]
    (G : SimpleGraph V) (C t : ℕ) :
    BddAbove (theorem4RatioSet G C t) := by
  classical
  refine ⟨(Fintype.card V : ℝ), ?_⟩
  intro r hr
  simp only [theorem4RatioSet, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hr
  rcases hr with hr | ⟨a, H, _, _, _, _, rfl⟩
  · subst r
    positivity
  · by_cases ha : a = 0
    · simp [ha]
    · have hapos : (0 : ℝ) < (a : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero ha
      have ha1 : (1 : ℝ) ≤ (a : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr ha)
      have hcard : HadwigerLean.chromatic H.coe ≤ Fintype.card V :=
        (HadwigerLean.chromatic_le_card H.coe).trans
          (Fintype.card_subtype_le H.verts)
      have hcardR : (HadwigerLean.chromatic H.coe : ℝ) ≤ (Fintype.card V : ℝ) := by
        exact_mod_cast hcard
      apply (div_le_iff₀ hapos).2
      calc
        (HadwigerLean.chromatic H.coe : ℝ) ≤ (Fintype.card V : ℝ) := hcardR
        _ = (Fintype.card V : ℝ) * 1 := by ring
        _ ≤ (Fintype.card V : ℝ) * (a : ℝ) :=
          mul_le_mul_of_nonneg_left ha1 (by positivity)

/-- There are only finitely many admissible ratios in a finite graph. -/
theorem theorem4RatioSet_finite {V : Type u} [Fintype V]
    (G : SimpleGraph V) (C t : ℕ) :
    (theorem4RatioSet G C t).Finite := by
  classical
  let f : Fin (t + 1) × G.Subgraph → ℝ :=
    fun p => (HadwigerLean.chromatic p.2.coe : ℝ) / (p.1.1 : ℝ)
  apply (Set.finite_singleton (0 : ℝ) |>.union (Set.finite_range f)).subset
  intro r hr
  simp only [theorem4RatioSet, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hr
  rcases hr with hr | ⟨a, H, _, hat, _, _, rfl⟩
  · exact Or.inl hr
  · right
    refine ⟨(⟨a, Nat.lt_succ_of_le hat⟩, H), ?_⟩
    rfl

/-- The supremum used in paper Theorem 4 is attained by zero or one of the
eligible arbitrary-subgraph ratios. -/
theorem theorem4MaxRatio_mem {V : Type u} [Fintype V]
    (G : SimpleGraph V) (C t : ℕ) :
    theorem4MaxRatio G C t ∈ theorem4RatioSet G C t := by
  unfold theorem4MaxRatio
  exact (theorem4RatioSet_nonempty G C t).csSup_mem
    (theorem4RatioSet_finite G C t)
/-- The paper maximum admits the pointwise elimination form used in the
bootstrap deduction. This is a direct consequence of Theorem 4: every
eligible subgraph ratio is bounded by `D`. -/
theorem theorem4_elimination (h4 : Theorem4Statement.{u}) :
    ∃ C : ℕ, 1 ≤ C ∧
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (t : ℕ) (D : ℝ),
        3 ≤ t → ¬ HadwigerLean.HasCliqueMinor G t → 0 ≤ D →
        (∀ (a : ℕ) (H : G.Subgraph) [Fintype H.verts],
          (t : ℝ) / Real.sqrt (Real.log (t : ℝ)) ≤ (a : ℝ) →
          a ≤ t →
          ¬ HadwigerLean.HasCliqueMinor H.coe a →
          (Fintype.card H.verts : ℝ) ≤
            (C : ℝ) * (a : ℝ) * (Real.log (a : ℝ)) ^ (4 : ℝ) →
          (HadwigerLean.chromatic H.coe : ℝ) ≤ D * (a : ℝ)) →
        (HadwigerLean.chromatic G : ℝ) ≤
          (C : ℝ) * (t : ℝ) * (1 + D) := by
  classical
  obtain ⟨C, hC, hCbound⟩ := h4
  refine ⟨C, hC, ?_⟩
  intro V _ G t D ht hminor hD hlocal
  have hmax : theorem4MaxRatio G C t ≤ D := by
    unfold theorem4MaxRatio
    apply csSup_le (theorem4RatioSet_nonempty G C t)
    intro r hr
    change r ∈ ({0} ∪ {r : ℝ | ∃ (a : ℕ) (H : G.Subgraph),
      (t : ℝ) / Real.sqrt (Real.log (t : ℝ)) ≤ (a : ℝ) ∧
      a ≤ t ∧
      ¬ HadwigerLean.HasCliqueMinor H.coe a ∧
      (Fintype.card H.verts : ℝ) ≤
        (C : ℝ) * (a : ℝ) * (Real.log (a : ℝ)) ^ (4 : ℝ) ∧
      r = (HadwigerLean.chromatic H.coe : ℝ) / (a : ℝ)}) at hr
    rcases hr with hr | hr
    · simp only [Set.mem_singleton_iff] at hr
      simpa [hr] using hD
    · rcases hr with ⟨a, H, hwindow, hat, hHminor, horder, rfl⟩
      by_cases ha : a = 0
      · simp [ha, hD]
      · have ha_pos : (0 : ℝ) < (a : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero ha
        apply (div_le_iff₀ ha_pos).2
        exact hlocal a H hwindow hat hHminor horder
  have h := hCbound V G t ht hminor
  have hCt : 0 ≤ (C : ℝ) * (t : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add_left hmax 1) hCt]

end HadwigerLean.Deduction
