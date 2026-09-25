import HadwigerLean.Woven.BranchPairPath

/-!
# Woven solutions from a rooted clique model with distinct roles

When all root and terminal roles have distinct vertices, a rooted clique
model at those vertices directly supplies a woven solution: retain the root
branches and connect each terminal pair through its two branches.
-/

namespace HadwigerLean

universe v

namespace RootedMinorModel

variable {V : Type v} {G : SimpleGraph V} {n a j : ℕ}
  {role : Fin n → V}

/-- Restrict a rooted clique model to injectively selected branches. -/
def selectClique (M : RootedMinorModel (SimpleGraph.completeGraph (Fin n)) G role)
    (f : Fin a ↪ Fin n) :
    RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G (role ∘ f) where
  branch := fun i => M.branch (f i)
  connected := fun i => M.connected (f i)
  disjoint := by
    intro i k hik
    exact M.disjoint (f.injective.ne hik)
  adjacent := by
    intro i k hik
    exact M.adjacent (f.injective.ne hik)
  root_mem := fun i => M.root_mem (f i)

end RootedMinorModel

namespace Woven

variable {V : Type v} {G : SimpleGraph V} {n a j : ℕ}
  {role : Fin n → V}

/-- Role slots for roots and the two ends of each terminal pair. -/
abbrev DistinctRoleIndex (a j : ℕ) := Fin a ⊕ (Fin j ⊕ Fin j)

/-- Enumerate exactly one slot per root and two slots per terminal pair. -/
noncomputable def distinctRoleEquiv (a j : ℕ) :
    DistinctRoleIndex a j ≃ Fin (a + 2 * j) :=
  Fintype.equivOfCardEq (by simp [DistinctRoleIndex]; omega)

/-- Assign the original vertex to each root or terminal role slot. -/
def originalRole (root : Fin a → V) (P : IndexedPairs (Fin j) V) :
    DistinctRoleIndex a j → V
  | Sum.inl i => root i
  | Sum.inr (Sum.inl i) => P.start i
  | Sum.inr (Sum.inr i) => P.finish i
/-- The root role selected by a global injection of role slots. -/
def selectedRoots (f : DistinctRoleIndex a j ↪ Fin n) (role : Fin n → V) :
    Fin a → V := fun i => role (f (Sum.inl i))

/-- The pair roles selected by a global injection of role slots. -/
def selectedPairs (f : DistinctRoleIndex a j ↪ Fin n) (role : Fin n → V) :
    IndexedPairs (Fin j) V where
  start := fun i => role (f (Sum.inr (Sum.inl i)))
  finish := fun i => role (f (Sum.inr (Sum.inr i)))

/-- Distinct proxy role slots keep proxy roots disjoint from proxy
terminal vertices. -/
theorem selectedRoles_disjoint
    (f : DistinctRoleIndex a j ↪ Fin n) (role : Fin n → V)
    (hrole : Function.Injective role) :
    Disjoint (Set.range (selectedRoots f role))
      (selectedPairs f role).allTerminals := by
  apply Set.disjoint_left.mpr
  intro x hxroot hxterm
  rcases hxroot with ⟨i, rfl⟩
  rcases Set.mem_iUnion.mp hxterm with ⟨k, hk⟩
  rcases hk with hs | ht
  · have heq : f (Sum.inl i) = f (Sum.inr (Sum.inl k)) :=
      hrole (by simpa [selectedRoots, selectedPairs] using hs)
    simpa using (f.injective heq)
  · have heq : f (Sum.inl i) = f (Sum.inr (Sum.inr k)) :=
      hrole (by simpa [selectedRoots, selectedPairs] using ht)
    simpa using (f.injective heq)
/-- A rooted clique model on every distinct role gives a compatible woven
solution on the selected root and terminal roles. -/
theorem exists_solution_of_distinct_roles
    (M : RootedMinorModel (SimpleGraph.completeGraph (Fin n)) G role)
    (f : DistinctRoleIndex a j ↪ Fin n) :
    Nonempty (WovenSolution G (selectedRoots f role) (selectedPairs f role)) := by
  classical
  let ri : Fin a ↪ Fin n :=
    ⟨fun i => f (Sum.inl i), fun _ _ h => Sum.inl_injective (f.injective h)⟩
  let si : Fin j → Fin n := fun i => f (Sum.inr (Sum.inl i))
  let ti : Fin j → Fin n := fun i => f (Sum.inr (Sum.inr i))
  let P : IndexedPairs (Fin j) V := selectedPairs f role
  have hij (i : Fin j) : si i ≠ ti i := by
    intro h
    have heq := f.injective h
    cases heq
  let L : IndexedLinkage G P := {
    path := fun i => M.pairPath (by simpa using hij i)
    disjoint := by
      intro i k hik
      apply Set.disjoint_left.mpr
      intro x hx hk
      have hxi : x ∈ M.branch (si i) ∪ M.branch (ti i) :=
        M.pairPath_vertices_subset (by simpa using hij i) hx
      have hxk : x ∈ M.branch (si k) ∪ M.branch (ti k) :=
        M.pairPath_vertices_subset (by simpa using hij k) hk
      have noOverlap (p q : DistinctRoleIndex a j) (hpq : p ≠ q)
          (hp : x ∈ M.branch (f p)) (hq : x ∈ M.branch (f q)) : False :=
        (Set.disjoint_left.mp (M.disjoint (f.injective.ne hpq))) hp hq
      rcases hxi with hxi | hxi <;> rcases hxk with hxk | hxk
      · exact noOverlap (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl k))
          (by simpa using hik) hxi hxk
      · exact noOverlap (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr k))
          (by simp) hxi hxk
      · exact noOverlap (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl k))
          (by simp) hxi hxk
      · exact noOverlap (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr k))
          (by simpa using hik) hxi hxk
  }
  let N := M.selectClique ri
  refine ⟨{ model := N, linkage := L, exact_intersection := ?_ }⟩
  have hdis : N.toMinorModel.vertices ∩ L.vertices = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    intro hx
    rcases Set.mem_iUnion.mp hx.1 with ⟨i, hxi⟩
    rcases Set.mem_iUnion.mp hx.2 with ⟨k, hxk⟩
    have hxpair : x ∈ M.branch (si k) ∪ M.branch (ti k) :=
      M.pairPath_vertices_subset (by simpa using hij k) hxk
    rcases hxpair with hxs | hxt
    · exact (Set.disjoint_left.mp (M.disjoint (f.injective.ne (by simp :
          (Sum.inl i : DistinctRoleIndex a j) ≠ Sum.inr (Sum.inl k))))) hxi hxs
    · exact (Set.disjoint_left.mp (M.disjoint (f.injective.ne (by simp :
          (Sum.inl i : DistinctRoleIndex a j) ≠ Sum.inr (Sum.inr k))))) hxi hxt
  have hroles : Set.range (selectedRoots f role) ∩ P.allTerminals = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    intro hx
    rcases hx.1 with ⟨i, rfl⟩
    rcases Set.mem_iUnion.mp hx.2 with ⟨k, hk⟩
    rcases hk with hs | ht
    · have heq : ri i = si k := M.root_injective (by
        simpa [ri, si, P, selectedRoots, selectedPairs] using hs)
      simpa using (f.injective heq)
    · have heq : ri i = ti k := M.root_injective (by
        simpa [ri, ti, P, selectedRoots, selectedPairs] using ht)
      simpa using (f.injective heq)
  exact hdis.trans hroles.symm

end Woven

end HadwigerLean
