import HadwigerLean.Deduction.ExternalInputs
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! The finite ratio maximum at the enlarged top power-of-three scale. -/

namespace HadwigerLean.Deduction

universe u

/-- The candidate ratios used by the corrected outer woven theorem.
`Nat.card` makes the vertex count independent of a chosen finite subtype
instance. -/
noncomputable def theorem4ScaleRatioSet
    {V : Type u} [Fintype V] (F : SimpleGraph V) (D T : ℕ) : Set ℝ :=
  {0} ∪ {r : ℝ | ∃ (q : ℕ) (H : F.Subgraph),
    (T : ℝ) / Real.sqrt (Real.log (T : ℝ)) ≤ (q : ℝ) ∧
    q ≤ 14 * T ∧
    ¬ HadwigerLean.HasCliqueMinor H.coe q ∧
    (Nat.card H.verts : ℝ) ≤
      (D : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ (4 : ℝ) ∧
    r = (HadwigerLean.chromatic H.coe : ℝ) / (q : ℝ)}

noncomputable def theorem4ScaleMaxRatio
    {V : Type u} [Fintype V] (F : SimpleGraph V) (D T : ℕ) : ℝ :=
  sSup (theorem4ScaleRatioSet F D T)

theorem theorem4ScaleRatioSet_nonempty
    {V : Type u} [Fintype V] (F : SimpleGraph V) (D T : ℕ) :
    (theorem4ScaleRatioSet F D T).Nonempty := by
  refine ⟨0, ?_⟩
  simp [theorem4ScaleRatioSet]

theorem theorem4ScaleRatioSet_finite
    {V : Type u} [Fintype V] (F : SimpleGraph V) (D T : ℕ) :
    (theorem4ScaleRatioSet F D T).Finite := by
  classical
  let f : Fin (14 * T + 1) × F.Subgraph → ℝ :=
    fun p => (HadwigerLean.chromatic p.2.coe : ℝ) / (p.1.1 : ℝ)
  apply (Set.finite_singleton (0 : ℝ) |>.union (Set.finite_range f)).subset
  intro r hr
  simp only [theorem4ScaleRatioSet, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_setOf_eq] at hr
  rcases hr with hr | ⟨q, H, _, hq, _, _, rfl⟩
  · exact Or.inl hr
  · right
    refine ⟨(⟨q, Nat.lt_succ_of_le hq⟩, H), ?_⟩
    rfl

theorem theorem4ScaleMaxRatio_nonneg
    {V : Type u} [Fintype V] (F : SimpleGraph V) (D T : ℕ) :
    0 ≤ theorem4ScaleMaxRatio F D T := by
  unfold theorem4ScaleMaxRatio
  apply le_csSup (theorem4ScaleRatioSet_finite F D T).bddAbove
  simp [theorem4ScaleRatioSet]

end HadwigerLean.Deduction
