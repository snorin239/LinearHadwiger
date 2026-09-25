import Mathlib.Tactic

/-! Pairwise disjoint pieces remain disjoint after reassignment by recipient. -/

namespace HadwigerLean.RootedDensity

universe u v w

/-- The union of all pieces assigned to a given recipient. -/
def reassignedPieces {A : Type u} {I : Type v} {V : Type w}
    (piece : A → Set V) (recipient : A → I) (i : I) : Set V :=
  ⋃ a : A, ⋃ (_ : recipient a = i), piece a

theorem mem_reassignedPieces_iff
    {A : Type u} {I : Type v} {V : Type w}
    (piece : A → Set V) (recipient : A → I) (i : I) (v : V) :
    v ∈ reassignedPieces piece recipient i ↔
      ∃ a : A, recipient a = i ∧ v ∈ piece a := by
  simp [reassignedPieces]

/-- If the original pieces are pairwise disjoint, different recipients
receive disjoint unions even when several pieces share one recipient. -/
theorem reassignedPieces_pairwise_disjoint
    {A : Type u} {I : Type v} {V : Type w}
    (piece : A → Set V) (recipient : A → I)
    (hdis : Pairwise (fun a b => Disjoint (piece a) (piece b))) :
    Pairwise (fun i j =>
      Disjoint (reassignedPieces piece recipient i)
        (reassignedPieces piece recipient j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro v hvi hvj
  obtain ⟨a, ha, hva⟩ :=
    (mem_reassignedPieces_iff piece recipient i v).mp hvi
  obtain ⟨b, hb, hvb⟩ :=
    (mem_reassignedPieces_iff piece recipient j v).mp hvj
  by_cases hab : a = b
  · subst b
    exact hij (ha.symm.trans hb)
  · exact (Set.disjoint_left.mp (hdis hab)) hva hvb

/-- Disjointness between pieces assigned to different recipients suffices;
pieces assigned to the same branch may overlap at their common roots. -/
theorem reassignedPieces_pairwise_disjoint_of_cross
    {A : Type u} {I : Type v} {V : Type w}
    (piece : A → Set V) (recipient : A → I)
    (hcross : ∀ a b, recipient a ≠ recipient b →
      Disjoint (piece a) (piece b)) :
    Pairwise (fun i j =>
      Disjoint (reassignedPieces piece recipient i)
        (reassignedPieces piece recipient j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro v hvi hvj
  obtain ⟨a, ha, hva⟩ :=
    (mem_reassignedPieces_iff piece recipient i v).mp hvi
  obtain ⟨b, hb, hvb⟩ :=
    (mem_reassignedPieces_iff piece recipient j v).mp hvj
  have hab : recipient a ≠ recipient b := by
    intro heq
    exact hij (ha.symm.trans (heq.trans hb))
  exact (Set.disjoint_left.mp (hcross a b hab)) hva hvb
end HadwigerLean.RootedDensity

