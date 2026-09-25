import HadwigerLean.Woven.BranchPairPath
import HadwigerLean.Woven.DistinctRoles

/-! Extracting a woven solution from a rooted sparse target model. -/

namespace HadwigerLean.Woven

universe u v

variable {W : Type u} {V : Type v} {a j : ℕ}

/-- The root roles selected from the labels of an arbitrary target graph. -/
def sparseSelectedRoots
    (label : DistinctRoleIndex a j → W) (role : W → V) : Fin a → V :=
  fun i => role (label (Sum.inl i))

/-- The terminal roles selected from the labels of an arbitrary target graph. -/
def sparseSelectedPairs
    (label : DistinctRoleIndex a j → W) (role : W → V) :
    IndexedPairs (Fin j) V where
  start := fun i => role (label (Sum.inr (Sum.inl i)))
  finish := fun i => role (label (Sum.inr (Sum.inr i)))

/-- A rooted model of a target containing a clique on the root labels and
one independent adjacent label pair per terminal demand supplies a woven
solution on the selected roles. Extra target edges are harmless. -/
theorem exists_solution_of_sparse_target_model
    {H : SimpleGraph W} {G : SimpleGraph V} {role : W → V}
    (M : RootedMinorModel H G role)
    (label : DistinctRoleIndex a j → W)
    (hlabel : Function.Injective label)
    (hclique : ∀ i k : Fin a, i ≠ k →
      H.Adj (label (Sum.inl i)) (label (Sum.inl k)))
    (hpair : ∀ i : Fin j,
      H.Adj (label (Sum.inr (Sum.inl i)))
        (label (Sum.inr (Sum.inr i)))) :
    Nonempty (WovenSolution G
      (sparseSelectedRoots label role) (sparseSelectedPairs label role)) := by
  classical
  let ri : Fin a → W := fun i => label (Sum.inl i)
  let si : Fin j → W := fun i => label (Sum.inr (Sum.inl i))
  let ti : Fin j → W := fun i => label (Sum.inr (Sum.inr i))
  let P : IndexedPairs (Fin j) V := sparseSelectedPairs label role
  let N : RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G
      (sparseSelectedRoots label role) := {
    branch := fun i => M.branch (ri i)
    connected := fun i => M.connected (ri i)
    disjoint := by
      intro i k hik
      exact M.disjoint (hlabel.ne (by simpa using hik))
    adjacent := by
      intro i k hik
      exact M.adjacent (hclique i k (by simpa using hik))
    root_mem := fun i => M.root_mem (ri i)
  }
  let L : IndexedLinkage G P := {
    path := fun i => M.pairPath (hpair i)
    disjoint := by
      intro i k hik
      apply Set.disjoint_left.mpr
      intro x hx hk
      have hxi : x ∈ M.branch (si i) ∪ M.branch (ti i) :=
        M.pairPath_vertices_subset (hpair i) hx
      have hxk : x ∈ M.branch (si k) ∪ M.branch (ti k) :=
        M.pairPath_vertices_subset (hpair k) hk
      have noOverlap (p q : DistinctRoleIndex a j) (hpq : p ≠ q)
          (hp : x ∈ M.branch (label p)) (hq : x ∈ M.branch (label q)) : False :=
        (Set.disjoint_left.mp (M.disjoint (hlabel.ne hpq))) hp hq
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
  refine ⟨{ model := N, linkage := L, exact_intersection := ?_ }⟩
  have hdis : N.toMinorModel.vertices ∩ L.vertices = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    intro hx
    rcases Set.mem_iUnion.mp hx.1 with ⟨i, hxi⟩
    rcases Set.mem_iUnion.mp hx.2 with ⟨k, hxk⟩
    have hxpair : x ∈ M.branch (si k) ∪ M.branch (ti k) :=
      M.pairPath_vertices_subset (hpair k) hxk
    rcases hxpair with hxs | hxt
    · exact (Set.disjoint_left.mp (M.disjoint (hlabel.ne (by simp :
          (Sum.inl i : DistinctRoleIndex a j) ≠ Sum.inr (Sum.inl k))))) hxi hxs
    · exact (Set.disjoint_left.mp (M.disjoint (hlabel.ne (by simp :
          (Sum.inl i : DistinctRoleIndex a j) ≠ Sum.inr (Sum.inr k))))) hxi hxt
  have hroles : Set.range (sparseSelectedRoots label role) ∩ P.allTerminals = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    intro hx
    rcases hx.1 with ⟨i, rfl⟩
    rcases Set.mem_iUnion.mp hx.2 with ⟨k, hk⟩
    rcases hk with hs | ht
    · have heq : ri i = si k := M.root_injective (by
        simpa [ri, si, P, sparseSelectedRoots, sparseSelectedPairs] using hs)
      simpa using (hlabel heq)
    · have heq : ri i = ti k := M.root_injective (by
        simpa [ri, ti, P, sparseSelectedRoots, sparseSelectedPairs] using ht)
      simpa using (hlabel heq)
  exact hdis.trans hroles.symm

end HadwigerLean.Woven
