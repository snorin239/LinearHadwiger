import HadwigerLean.Inseparability.IndexPartition
import HadwigerLean.Woven.Basic
import HadwigerLean.Graph.RootedMinor
import HadwigerLean.Graph.Linkedness.RegionLinkage
import Mathlib.Tactic

/-! Joining branch pieces into the raw clique model of a CI stage. -/

namespace HadwigerLean.Inseparability

universe u v

private theorem connected_induce_of_set_eq
    {V : Type u} (G : SimpleGraph V) {A B : Set V}
    (hAB : A = B) (hA : (G.induce A).Connected) :
    (G.induce B).Connected := by
  cases hAB
  exact hA
/-- A connected central patch stays connected after attaching finitely
many connected pieces which each meet that patch. -/
theorem connected_patch_union_finset
    {V : Type u} {J : Type v} [DecidableEq J]
    (G : SimpleGraph V) (C : Set V) (P : J → Set V)
    (hC : (G.induce C).Connected)
    (S : Finset J) (hP : ∀ j ∈ S, (G.induce (P j)).Connected)
    (hmeet : ∀ j ∈ S, ∃ v, v ∈ C ∧ v ∈ P j)
    :
    (G.induce (C ∪ ⋃ j ∈ S, P j)).Connected := by
  induction S using Finset.induction with
  | empty =>
      apply connected_induce_of_set_eq G ?_ hC
      ext v
      simp
  | @insert j S hj ih =>
      obtain ⟨v,hvC,hvP⟩ := hmeet j (Finset.mem_insert_self j S)
      have hvfront : v ∈ C ∪ ⋃ t ∈ S, P t := Or.inl hvC
      have hconn := Linkedness.connected_induce_union_of_common
        (ih (fun t ht => hP t (Finset.mem_insert_of_mem ht))
          (fun t ht => hmeet t (Finset.mem_insert_of_mem ht)))
        (hP j (Finset.mem_insert_self j S)) hvfront hvP
      apply connected_induce_of_set_eq G ?_ hconn
      ext v
      simp [Finset.mem_insert, or_and_left, Set.union_assoc,
        Set.union_left_comm, Set.union_comm]

/-- Reindex a rooted clique model by any equivalence of its branch names. -/
def rootedCliqueModel_reindex
    {I : Type u} {J : Type v} {V : Type*}
    {G : SimpleGraph V} {root : I → V}
    (M : RootedMinorModel (SimpleGraph.completeGraph I) G root)
    (e : J ≃ I) :
    RootedMinorModel (SimpleGraph.completeGraph J) G (root ∘ e) where
  branch := fun j => M.branch (e j)
  connected := fun j => M.connected (e j)
  disjoint := by
    intro j k hjk
    exact M.disjoint (fun h => hjk (e.injective h))
  adjacent := by
    intro j k hjk
    exact M.adjacent (fun h => hjk (e.injective h))
  root_mem := fun j => M.root_mem (e j)



/-- The path pieces assigned to one branch. -/
def assignedPaths {V : Type u} {I : Type v} {K : Type*}
    [Fintype K] [DecidableEq I]
    (owner : K → I) (P : K → Set V) (i : I) : Set V :=
  ⋃ k ∈ Finset.univ.filter (fun k => owner k = i), P k

/-- The supplementary old and child model pieces assigned to a branch. -/
def extraPieces {V : Type u} {I : Type v} {J : Type*}
    (E : I → J → Set V) (extra : I → Finset J) (i : I) : Set V :=
  ⋃ j ∈ extra i, E i j

/-- All nonpath pieces of a branch, including its connected D patch. -/
def branchBase {V : Type u} {I : Type v} {J : Type*}
    (C : I → Set V) (E : I → J → Set V)
    (extra : I → Finset J) (i : I) : Set V :=
  C i ∪ extraPieces E extra i

/-- The assembled branch. -/
def assembledBranch {V : Type u} {I : Type v} {J K : Type*}
    [Fintype K] [DecidableEq I]
    (C : I → Set V) (P : K → Set V) (owner : K → I)
    (E : I → J → Set V) (extra : I → Finset J)
    (i : I) : Set V :=
  branchBase C E extra i ∪ assignedPaths owner P i

private theorem mem_assignedPaths_iff
    {V : Type u} {I : Type v} {K : Type*}
    [Fintype K] [DecidableEq I]
    (owner : K → I) (P : K → Set V) (i : I) (v : V) :
    v ∈ assignedPaths owner P i ↔
      ∃ k, owner k = i ∧ v ∈ P k := by
  classical
  simp [assignedPaths]

private theorem mem_extraPieces_iff
    {V : Type u} {I : Type v} {J : Type*}
    (E : I → J → Set V) (extra : I → Finset J) (i : I) (v : V) :
    v ∈ extraPieces E extra i ↔
      ∃ j ∈ extra i, v ∈ E i j := by
  simp [extraPieces]

/-- Assemble a raw rooted clique model from the old branches, the child
branches, the disjoint indexed paths, and the central D patches. The
hypotheses state disjointness only for elementary pieces; connectivity
of each whole branch and the exact tangency to the future region are
proved here. -/
theorem assemble_raw_rooted_clique_model
    {V : Type u} {I : Type v} {J K : Type*}
    [Fintype K] [DecidableEq I] [DecidableEq J]
    (G : SimpleGraph V)
    (C : I → Set V) (P : K → Set V) (owner : K → I)
    (E : I → J → Set V) (extra : I → Finset J)
    (root : I → V) (H core : Set V)
    (hC : ∀ i, (G.induce (C i)).Connected)
    (hP : ∀ k, (G.induce (P k)).Connected)
    (hPmeet : ∀ k, ∃ v, v ∈ C (owner k) ∧ v ∈ P k)
    (hE : ∀ i j, j ∈ extra i → (G.induce (E i j)).Connected)
    (hEmeet : ∀ i j, j ∈ extra i →
      ∃ v, v ∈ C i ∪ assignedPaths owner P i ∧ v ∈ E i j)
    (hBaseDisjoint : ∀ i j, i ≠ j →
      Disjoint (branchBase C E extra i) (branchBase C E extra j))
    (hPathBaseDisjoint : ∀ k i, owner k ≠ i →
      Disjoint (P k) (branchBase C E extra i))
    (hPathDisjoint : ∀ k l, k ≠ l → Disjoint (P k) (P l))
    (hRootPath : ∀ i, root i ∈ assignedPaths owner P i)
    (hBaseH : ∀ i, Disjoint (branchBase C E extra i) H)
    (hPathH : ∀ i, assignedPaths owner P i ∩ H = {root i})
    (hRootCore : ∀ i, root i ∈ core)
    (hBaseWitness : ∀ i j, i ≠ j →
      ∃ a ∈ branchBase C E extra i,
        ∃ b ∈ branchBase C E extra j,
          a ∈ core ∧ b ∈ core ∧ G.Adj a b) :
    ∃ M : RootedMinorModel (SimpleGraph.completeGraph I) G root,
      (∀ i, M.branch i = assembledBranch C P owner E extra i) ∧
      (∀ i, M.branch i ∩ H = {root i}) ∧
      (∀ i j, i ≠ j →
        ∃ a ∈ M.branch i, ∃ b ∈ M.branch j,
          a ∈ core ∧ b ∈ core ∧ G.Adj a b) ∧
      M.toMinorModel.vertices ∩ H ⊆ core := by
  classical
  let B := assembledBranch C P owner E extra
  have hBconnected : ∀ i, (G.induce (B i)).Connected := by
    intro i
    have hfirst : (G.induce (C i ∪ assignedPaths owner P i)).Connected := by
      unfold assignedPaths
      apply connected_patch_union_finset G (C i) P (hC i)
      · intro k hk
        exact hP k
      · intro k hk
        have hown : owner k = i := (Finset.mem_filter.mp hk).2
        simpa [hown] using hPmeet k
    have hsecond : (G.induce
        ((C i ∪ assignedPaths owner P i) ∪ extraPieces E extra i)).Connected := by
      unfold extraPieces
      apply connected_patch_union_finset G
        (C i ∪ assignedPaths owner P i) (E i) hfirst
      · intro j hj
        exact hE i j hj
      · intro j hj
        exact hEmeet i j hj
    apply connected_induce_of_set_eq G ?_ hsecond
    ext v
    simp [B, assembledBranch, branchBase, Set.union_assoc,
      Set.union_left_comm, Set.union_comm]
  have hBdisjoint : ∀ i j, i ≠ j → Disjoint (B i) (B j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro v hvi hvj
    change v ∈ branchBase C E extra i ∪ assignedPaths owner P i at hvi
    change v ∈ branchBase C E extra j ∪ assignedPaths owner P j at hvj
    rcases hvi with hvi | hvi <;> rcases hvj with hvj | hvj
    · exact (Set.disjoint_left.mp (hBaseDisjoint i j hij)) hvi hvj
    · obtain ⟨k,hki,hvk⟩ := (mem_assignedPaths_iff owner P j v).mp hvj
      have hne : owner k ≠ i := by simpa [hki] using hij.symm
      exact (Set.disjoint_left.mp (hPathBaseDisjoint k i hne)) hvk hvi
    · obtain ⟨k,hki,hvk⟩ := (mem_assignedPaths_iff owner P i v).mp hvi
      have hne : owner k ≠ j := by simpa [hki] using hij
      exact (Set.disjoint_left.mp (hPathBaseDisjoint k j hne)) hvk hvj
    · obtain ⟨k,hki,hvk⟩ := (mem_assignedPaths_iff owner P i v).mp hvi
      obtain ⟨l,hlj,hvl⟩ := (mem_assignedPaths_iff owner P j v).mp hvj
      have hkl : k ≠ l := by
        intro h
        subst l
        exact hij (hki.symm.trans hlj)
      exact (Set.disjoint_left.mp (hPathDisjoint k l hkl)) hvk hvl
  let M : RootedMinorModel (SimpleGraph.completeGraph I) G root := {
    branch := B
    connected := hBconnected
    disjoint := hBdisjoint
    adjacent := by
      intro i j hij
      obtain ⟨a,ha,b,hb,_,_,hab⟩ := hBaseWitness i j hij
      exact ⟨a,Or.inl ha,b,Or.inl hb,hab⟩
    root_mem := by
      intro i
      exact Or.inr (hRootPath i)
  }
  have hTangency : ∀ i, M.branch i ∩ H = {root i} := by
    intro i
    apply Set.Subset.antisymm
    · intro v hv
      rcases hv.1 with hvB | hvP
      · exact False.elim ((Set.disjoint_left.mp (hBaseH i)) hvB hv.2)
      · have hh : v ∈ assignedPaths owner P i ∩ H := ⟨hvP,hv.2⟩
        rw [hPathH i] at hh
        exact hh
    · intro v hv
      have heq : v = root i := by simpa using hv
      subst v
      have hmem : root i ∈ ({root i} : Set V) := by simp
      have hh : root i ∈ assignedPaths owner P i ∩ H := by
        rw [hPathH i]
        exact hmem
      exact ⟨Or.inr (hRootPath i),hh.2⟩
  refine ⟨M, fun _ => rfl, hTangency, ?_, ?_⟩
  · intro i j hij
    obtain ⟨a,ha,b,hb,hac,hbc,hab⟩ := hBaseWitness i j hij
    exact ⟨a,Or.inl ha,b,Or.inl hb,hac,hbc,hab⟩
  · intro v hv
    obtain ⟨i,hvi⟩ := Set.mem_iUnion.mp hv.1
    have hviH : v ∈ M.branch i ∩ H := ⟨hvi,hv.2⟩
    rw [hTangency i] at hviH
    have heq : v = root i := by simpa using hviH
    simpa [heq] using hRootCore i

end HadwigerLean.Inseparability
