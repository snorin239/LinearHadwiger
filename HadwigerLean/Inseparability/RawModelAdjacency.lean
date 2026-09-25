import HadwigerLean.Inseparability.RawModelAssembly
import Mathlib.Tactic

/-!
# Adjacency witnesses for the nonzero CI model stage

Old branches preserve old-old edges. Each small child model supplies the
old-new edges, and any child supplies new-new edges when at least one old
block exists. This module identifies the source of each witness in the
nonpath part of the assembled branches.
-/

namespace HadwigerLean.Inseparability

universe u

def ciExtraPiece {V : Type u} (p x : ℕ)
    {G : SimpleGraph V}
    (A : MinorModel (SimpleGraph.completeGraph (Fin p × Fin x)) G)
    (M : Fin p → MinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G)
    (z : Sum (Fin p × Fin x) (Fin x)) (slot : Option (Fin p)) :
    Set V :=
  match z, slot with
  | .inl z, none => A.branch z
  | .inl (i,r), some j =>
      if j = i then (M i).branch (0,r) else ∅
  | .inr _, none => ∅
  | .inr r, some i => (M i).branch (1,r)

def ciExtraIndex (p x : ℕ)
    (z : Sum (Fin p × Fin x) (Fin x)) :
    Finset (Option (Fin p)) :=
  match z with
  | .inl (i,_) => {none, some i}
  | .inr _ => Finset.univ.image some

private theorem ci_old_in_base {V : Type u} (p x : ℕ)
    {G : SimpleGraph V}
    (A : MinorModel (SimpleGraph.completeGraph (Fin p × Fin x)) G)
    (M : Fin p → MinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G)
    (C : Sum (Fin p × Fin x) (Fin x) → Set V)
    (z : Fin p × Fin x) {v : V}
    (hv : v ∈ A.branch z) :
    v ∈ branchBase C (ciExtraPiece p x A M)
      (ciExtraIndex p x) (.inl z) := by
  right
  change v ∈ ⋃ j ∈ ciExtraIndex p x (.inl z), ciExtraPiece p x A M (.inl z) j
  exact Set.mem_iUnion.mpr ⟨none,
    Set.mem_iUnion.mpr ⟨by simp [ciExtraIndex], by simpa [ciExtraPiece] using hv⟩⟩

private theorem ci_child_old_in_base {V : Type u} (p x : ℕ)
    {G : SimpleGraph V}
    (A : MinorModel (SimpleGraph.completeGraph (Fin p × Fin x)) G)
    (M : Fin p → MinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G)
    (C : Sum (Fin p × Fin x) (Fin x) → Set V)
    (i : Fin p) (r : Fin x) {v : V}
    (hv : v ∈ (M i).branch (0,r)) :
    v ∈ branchBase C (ciExtraPiece p x A M)
      (ciExtraIndex p x) (.inl (i,r)) := by
  right
  change v ∈ ⋃ j ∈ ciExtraIndex p x (.inl (i,r)),
    ciExtraPiece p x A M (.inl (i,r)) j
  exact Set.mem_iUnion.mpr ⟨some i,
    Set.mem_iUnion.mpr ⟨by simp [ciExtraIndex], by simpa [ciExtraPiece] using hv⟩⟩

private theorem ci_child_new_in_base {V : Type u} (p x : ℕ)
    {G : SimpleGraph V}
    (A : MinorModel (SimpleGraph.completeGraph (Fin p × Fin x)) G)
    (M : Fin p → MinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G)
    (C : Sum (Fin p × Fin x) (Fin x) → Set V)
    (i : Fin p) (r : Fin x) {v : V}
    (hv : v ∈ (M i).branch (1,r)) :
    v ∈ branchBase C (ciExtraPiece p x A M)
      (ciExtraIndex p x) (.inr r) := by
  right
  change v ∈ ⋃ j ∈ ciExtraIndex p x (.inr r),
    ciExtraPiece p x A M (.inr r) j
  exact Set.mem_iUnion.mpr ⟨some i,
    Set.mem_iUnion.mpr
      ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,
        by simpa [ciExtraPiece] using hv⟩⟩

/-- Every edge of the enlarged clique has a witness in the nonpath
pieces, with both endpoints in the proposed new core. The first
stage is handled separately; this theorem uses a child for
new-new adjacency. -/
theorem ci_nonzero_stage_base_witness
    {V : Type u} (p x : ℕ) (hp : 0 < p)
    {G : SimpleGraph V}
    (A : MinorModel (SimpleGraph.completeGraph (Fin p × Fin x)) G)
    (M : Fin p → MinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G)
    (C : Sum (Fin p × Fin x) (Fin x) → Set V)
    (core : Set V)
    (hOldCore : ∀ z w, z ≠ w →
      ∃ a ∈ A.branch z, ∃ b ∈ A.branch w,
        a ∈ core ∧ b ∈ core ∧ G.Adj a b)
    (hChildCore : ∀ i z, (M i).branch z ⊆ core) :
    ∀ z w : Sum (Fin p × Fin x) (Fin x), z ≠ w →
      ∃ a ∈ branchBase C (ciExtraPiece p x A M) (ciExtraIndex p x) z,
        ∃ b ∈ branchBase C (ciExtraPiece p x A M)
          (ciExtraIndex p x) w,
          a ∈ core ∧ b ∈ core ∧ G.Adj a b := by
  intro z w hzw
  cases z with
  | inl z =>
    cases w with
    | inl w =>
      have hne : z ≠ w := by
        intro h
        exact hzw (congrArg Sum.inl h)
      obtain ⟨a,ha,b,hb,hac,hbc,hab⟩ := hOldCore z w hne
      exact ⟨a,ci_old_in_base p x A M C z ha,b,
        ci_old_in_base p x A M C w hb,hac,hbc,hab⟩
    | inr r =>
      obtain ⟨a,ha,b,hb,hab⟩ :=
        (M z.1).adjacent (show ((0 : Fin 2),z.2) ≠ ((1 : Fin 2),r) by simp)
      exact ⟨a,ci_child_old_in_base p x A M C z.1 z.2 ha,
        b,ci_child_new_in_base p x A M C z.1 r hb,
        hChildCore z.1 (0,z.2) ha,
        hChildCore z.1 (1,r) hb,hab⟩
  | inr r =>
    cases w with
    | inl z =>
      obtain ⟨a,ha,b,hb,hab⟩ :=
        (M z.1).adjacent (show ((1 : Fin 2),r) ≠ ((0 : Fin 2),z.2) by simp)
      exact ⟨a,ci_child_new_in_base p x A M C z.1 r ha,
        b,ci_child_old_in_base p x A M C z.1 z.2 hb,
        hChildCore z.1 (1,r) ha,
        hChildCore z.1 (0,z.2) hb,hab⟩
    | inr s =>
      have hrs : r ≠ s := by
        intro h
        exact hzw (congrArg Sum.inr h)
      let i : Fin p := ⟨0,hp⟩
      obtain ⟨a,ha,b,hb,hab⟩ :=
        (M i).adjacent (show ((1 : Fin 2),r) ≠ ((1 : Fin 2),s) by
          simpa using hrs)
      exact ⟨a,ci_child_new_in_base p x A M C i r ha,
        b,ci_child_new_in_base p x A M C i s hb,
        hChildCore i (1,r) ha,hChildCore i (1,s) hb,hab⟩


/-- Every selected old or child model piece is connected. -/
theorem ci_extra_connected
    {V : Type u} (p x : ℕ)
    {G : SimpleGraph V}
    (A : MinorModel (SimpleGraph.completeGraph (Fin p × Fin x)) G)
    (M : Fin p → MinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G) :
    ∀ z j, j ∈ ciExtraIndex p x z →
      (G.induce (ciExtraPiece p x A M z j)).Connected := by
  intro z j hj
  cases z with
  | inl z =>
    obtain ⟨i,r⟩ := z
    have hh : j = none ∨ j = some i := by
      simpa [ciExtraIndex] using hj
    rcases hh with rfl | rfl
    · exact A.connected (i,r)
    · change (G.induce (if i = i then (M i).branch (0,r) else ∅)).Connected
      rw [if_pos rfl]
      exact (M i).connected (0,r)
  | inr r =>
    cases j with
    | none =>
      simp [ciExtraIndex] at hj
    | some i =>
      exact (M i).connected (1,r)

end HadwigerLean.Inseparability
