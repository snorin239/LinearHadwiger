import HadwigerLean.Inseparability.RawModelAssembly
import Mathlib.Tactic

/-!
# Elementary disjointness criteria for raw clique branches

The raw assembly theorem asks for disjoint base pieces and for paths
not assigned to a branch to avoid its base. These lemmas reduce those
conditions to checks on one patch, one extra model piece, or one path.
-/

namespace HadwigerLean.Inseparability

universe u v

theorem branchBase_disjoint_of_pieces
    {V : Type u} {I : Type v} {J : Type*}
    (C : I → Set V) (E : I → J → Set V)
    (extra : I → Finset J)
    (hCC : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hCE : ∀ i j, i ≠ j → ∀ a ∈ extra j,
      Disjoint (C i) (E j a))
    (hEE : ∀ i j, i ≠ j → ∀ a ∈ extra i, ∀ b ∈ extra j,
      Disjoint (E i a) (E j b)) :
    ∀ i j, i ≠ j →
      Disjoint (branchBase C E extra i) (branchBase C E extra j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro v hvi hvj
  rcases hvi with hvi | hvi <;> rcases hvj with hvj | hvj
  · exact (Set.disjoint_left.mp (hCC i j hij)) hvi hvj
  · obtain ⟨b,hbj,hvb⟩ := by
      simpa [extraPieces] using hvj
    exact (Set.disjoint_left.mp (hCE i j hij b hbj)) hvi hvb
  · obtain ⟨a,hai,hva⟩ := by
      simpa [extraPieces] using hvi
    exact (Set.disjoint_left.mp (hCE j i hij.symm a hai)) hvj hva
  · obtain ⟨a,hai,hva⟩ := by
      simpa [extraPieces] using hvi
    obtain ⟨b,hbj,hvb⟩ := by
      simpa [extraPieces] using hvj
    exact (Set.disjoint_left.mp (hEE i j hij a hai b hbj)) hva hvb

theorem path_base_disjoint_of_pieces
    {V : Type u} {I : Type v} {J K : Type*}
    (C : I → Set V) (P : K → Set V)
    (E : I → J → Set V) (extra : I → Finset J)
    (owner : K → I)
    (hPC : ∀ k i, owner k ≠ i → Disjoint (P k) (C i))
    (hPE : ∀ k i, owner k ≠ i → ∀ a ∈ extra i,
      Disjoint (P k) (E i a)) :
    ∀ k i, owner k ≠ i →
      Disjoint (P k) (branchBase C E extra i) := by
  intro k i hki
  apply Set.disjoint_left.mpr
  intro v hvP hvB
  rcases hvB with hvC | hvE
  · exact (Set.disjoint_left.mp (hPC k i hki)) hvP hvC
  · obtain ⟨a,hai,hva⟩ := by
      simpa [extraPieces] using hvE
    exact (Set.disjoint_left.mp (hPE k i hki a hai)) hvP hva

/-- To attach an old or child model piece, it suffices to identify one
assigned path meeting that piece. -/
theorem extra_meet_of_path_attachment
    {V : Type u} {I : Type v} {J K : Type*}
    [Fintype K] [DecidableEq I]
    (C : I → Set V) (P : K → Set V)
    (owner : K → I)
    (E : I → J → Set V) (extra : I → Finset J)
    (hattach : ∀ i j, j ∈ extra i →
      ∃ k, owner k = i ∧ ∃ v, v ∈ P k ∧ v ∈ E i j) :
    ∀ i j, j ∈ extra i →
      ∃ v, v ∈ C i ∪ assignedPaths owner P i ∧ v ∈ E i j := by
  intro i j hj
  obtain ⟨k,hk,v,hvP,hvE⟩ := hattach i j hj
  have hvAssigned : v ∈ assignedPaths owner P i := by
    change v ∈ ⋃ l ∈ Finset.univ.filter (fun l => owner l = i), P l
    exact Set.mem_iUnion.mpr ⟨k,
      Set.mem_iUnion.mpr ⟨by simp [hk],hvP⟩⟩
  exact ⟨v,Or.inr hvAssigned,hvE⟩

end HadwigerLean.Inseparability
