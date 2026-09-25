import HadwigerLean.Inseparability.RawModelAdjacency
import Mathlib.Tactic

/-!
# Disjointness of old and child model pieces in a nonzero CI stage

Every selected supplementary piece has a primitive label: an old
branch, or a branch of one child model. The primitive label determines
the assembled branch to which it belongs. Disjointness of different
assembled branches then follows from the old model, child models, and
the fact that the old and child regions are disjoint.
-/

namespace HadwigerLean.Inseparability

universe u

def ciPrimitiveLabel (p x : ℕ) :=
  Sum (Fin p × Fin x) (Fin p × (Fin 2 × Fin x))

def ciPrimitiveOwner (p x : ℕ) :
    ciPrimitiveLabel p x → Sum (Fin p × Fin x) (Fin x)
  | .inl z => .inl z
  | .inr (i,(k,r)) =>
      if k = 0 then .inl (i,r) else .inr r

def ciExtraLabel (p x : ℕ)
    (z : Sum (Fin p × Fin x) (Fin x))
    (slot : Option (Fin p)) :
    Option (ciPrimitiveLabel p x) :=
  match z, slot with
  | .inl z, none => some (.inl z)
  | .inl (i,r), some j =>
      if j = i then some (.inr (i,(0,r))) else none
  | .inr _, none => none
  | .inr r, some i => some (.inr (i,(1,r)))

def ciPrimitiveSet {V : Type u} (p x : ℕ)
    {G : SimpleGraph V}
    (A : MinorModel (SimpleGraph.completeGraph (Fin p × Fin x)) G)
    (M : Fin p → MinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G) :
    ciPrimitiveLabel p x → Set V
  | .inl z => A.branch z
  | .inr (i,z) => (M i).branch z

theorem ciExtraPiece_eq_primitive {V : Type u} (p x : ℕ)
    {G : SimpleGraph V}
    (A : MinorModel (SimpleGraph.completeGraph (Fin p × Fin x)) G)
    (M : Fin p → MinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G)
    (z : Sum (Fin p × Fin x) (Fin x))
    (slot : Option (Fin p)) :
    ciExtraPiece p x A M z slot =
      match ciExtraLabel p x z slot with
      | some l => ciPrimitiveSet p x A M l
      | none => ∅ := by
  cases z with
  | inl z =>
      obtain ⟨i,r⟩ := z
      cases slot with
      | none => rfl
      | some j =>
          by_cases hji : j = i <;>
            simp [ciExtraPiece, ciExtraLabel, ciPrimitiveSet, hji]
  | inr r =>
      cases slot <;> rfl

theorem ciExtraLabel_owner
    (p x : ℕ)
    (z : Sum (Fin p × Fin x) (Fin x))
    (slot : Option (Fin p))
    (l : ciPrimitiveLabel p x)
    (hl : ciExtraLabel p x z slot = some l) :
    ciPrimitiveOwner p x l = z := by
  cases z with
  | inl z =>
      obtain ⟨i,r⟩ := z
      cases slot with
      | none =>
          simp [ciExtraLabel] at hl
          subst l
          rfl
      | some j =>
          by_cases hji : j = i
          · subst j
            simp [ciExtraLabel] at hl
            subst l
            simp [ciPrimitiveOwner]
          · simp [ciExtraLabel, hji] at hl
  | inr r =>
      cases slot with
      | none => simp [ciExtraLabel] at hl
      | some j =>
          simp [ciExtraLabel] at hl
          subst l
          simp [ciPrimitiveOwner]

theorem ciExtraLabel_exists_of_mem
    (p x : ℕ)
    (z : Sum (Fin p × Fin x) (Fin x))
    (slot : Option (Fin p))
    (hslot : slot ∈ ciExtraIndex p x z) :
    ∃ l : ciPrimitiveLabel p x,
      ciExtraLabel p x z slot = some l := by
  cases z with
  | inl z =>
      obtain ⟨i,r⟩ := z
      have hh : slot = none ∨ slot = some i := by
        simpa [ciExtraIndex] using hslot
      rcases hh with rfl | rfl
      · exact ⟨.inl (i,r),rfl⟩
      · exact ⟨.inr (i,(0,r)),by simp [ciExtraLabel]⟩
  | inr r =>
      cases slot with
      | none => simp [ciExtraIndex] at hslot
      | some i => exact ⟨.inr (i,(1,r)),rfl⟩

private theorem old_child_disjoint {V : Type u} (p x : ℕ)
    {G : SimpleGraph V}
    (A : MinorModel (SimpleGraph.completeGraph (Fin p × Fin x)) G)
    (M : Fin p → MinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G)
    (hAChild : ∀ i, Disjoint A.vertices (M i).vertices)
    (z : Fin p × Fin x) (i : Fin p) (w : Fin 2 × Fin x) :
    Disjoint (A.branch z) ((M i).branch w) := by
  apply Set.disjoint_left.mpr
  intro v hvA hvM
  exact (Set.disjoint_left.mp (hAChild i))
    (Set.mem_iUnion.mpr ⟨z,hvA⟩)
    (Set.mem_iUnion.mpr ⟨w,hvM⟩)

private theorem child_child_disjoint {V : Type u} (p x : ℕ)
    {G : SimpleGraph V}
    (M : Fin p → MinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G)
    (hChildChild : ∀ i j, i ≠ j →
      Disjoint (M i).vertices (M j).vertices)
    (i j : Fin p) (z w : Fin 2 × Fin x) (hij : i ≠ j) :
    Disjoint ((M i).branch z) ((M j).branch w) := by
  apply Set.disjoint_left.mpr
  intro v hvI hvJ
  exact (Set.disjoint_left.mp (hChildChild i j hij))
    (Set.mem_iUnion.mpr ⟨z,hvI⟩)
    (Set.mem_iUnion.mpr ⟨w,hvJ⟩)

theorem ciPrimitiveSet_disjoint
    {V : Type u} (p x : ℕ)
    {G : SimpleGraph V}
    (A : MinorModel (SimpleGraph.completeGraph (Fin p × Fin x)) G)
    (M : Fin p → MinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G)
    (hAChild : ∀ i, Disjoint A.vertices (M i).vertices)
    (hChildChild : ∀ i j, i ≠ j →
      Disjoint (M i).vertices (M j).vertices) :
    ∀ l m : ciPrimitiveLabel p x, l ≠ m →
      Disjoint (ciPrimitiveSet p x A M l)
        (ciPrimitiveSet p x A M m) := by
  intro l m hlm
  cases l with
  | inl z =>
      cases m with
      | inl w =>
          apply A.disjoint
          intro h
          exact hlm (congrArg Sum.inl h)
      | inr iw =>
          exact old_child_disjoint p x A M hAChild z iw.1 iw.2
  | inr iz =>
      cases m with
      | inl w =>
          exact (old_child_disjoint p x A M hAChild w iz.1 iz.2).symm
      | inr jw =>
          by_cases hij : iz.1 = jw.1
          · obtain ⟨i,z⟩ := iz
            obtain ⟨j,w⟩ := jw
            dsimp at hij
            subst j
            apply (M i).disjoint
            intro h
            exact hlm (congrArg Sum.inr (Prod.ext rfl h))
          · exact child_child_disjoint p x M hChildChild
              iz.1 jw.1 iz.2 jw.2 hij

/-- Distinct assembled branches have disjoint supplementary model pieces.
The hypotheses are exactly the separation of old model from selected
child regions and the pairwise disjointness of those regions. -/
theorem ci_extra_cross_disjoint
    {V : Type u} (p x : ℕ)
    {G : SimpleGraph V}
    (A : MinorModel (SimpleGraph.completeGraph (Fin p × Fin x)) G)
    (M : Fin p → MinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G)
    (hAChild : ∀ i, Disjoint A.vertices (M i).vertices)
    (hChildChild : ∀ i j, i ≠ j →
      Disjoint (M i).vertices (M j).vertices) :
    ∀ z w : Sum (Fin p × Fin x) (Fin x), z ≠ w →
      ∀ a ∈ ciExtraIndex p x z,
      ∀ b ∈ ciExtraIndex p x w,
        Disjoint (ciExtraPiece p x A M z a)
          (ciExtraPiece p x A M w b) := by
  intro z w hzw a ha b hb
  obtain ⟨l,hl⟩ := ciExtraLabel_exists_of_mem p x z a ha
  obtain ⟨m,hm⟩ := ciExtraLabel_exists_of_mem p x w b hb
  have hlm : l ≠ m := by
    intro h
    have hz := ciExtraLabel_owner p x z a l hl
    have hw := ciExtraLabel_owner p x w b m hm
    exact hzw (hz.symm.trans (h ▸ hw))
  rw [ciExtraPiece_eq_primitive,ciExtraPiece_eq_primitive,hl,hm]
  exact ciPrimitiveSet_disjoint p x A M hAChild hChildChild l m hlm

end HadwigerLean.Inseparability
