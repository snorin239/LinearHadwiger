import HadwigerLean.Woven.Basic
import Mathlib.Tactic

/-!
# Pathwise control from exact model-linkage intersection

A global exact intersection between a rooted minor model and an
indexed linkage implies that each branch can meet a path only at its
own root. If that root is prescribed on a particular path, the branch
avoids every other path.
-/

namespace HadwigerLean.Woven

universe u v

theorem rooted_model_path_intersection_subset_root
    {I : Type u} {K : Type v} {V : Type*}
    {G : SimpleGraph V} {root : I → V}
    (M : RootedMinorModel (SimpleGraph.completeGraph I) G root)
    {P : IndexedPairs K V} (L : IndexedLinkage G P)
    (hExact : M.toMinorModel.vertices ∩ L.vertices =
      Set.range root)
    (i : I) (k : K) :
    M.branch i ∩ pathVertexSet (L.path k) ⊆ {root i} := by
  intro v hv
  have hvModel : v ∈ M.toMinorModel.vertices :=
    Set.mem_iUnion.mpr ⟨i,hv.1⟩
  have hvLink : v ∈ L.vertices :=
    L.path_subset_vertices k hv.2
  have hvRoot : v ∈ Set.range root := by
    rw [← hExact]
    exact ⟨hvModel,hvLink⟩
  obtain ⟨j,hj⟩ := hvRoot
  have hij : i = j := by
    by_contra hne
    exact (Set.disjoint_left.mp (M.disjoint hne))
      hv.1 (hj ▸ M.root_mem j)
  have hvEq : v = root i := by
    rw [hij]
    exact hj.symm
  simpa [hvEq]

theorem rooted_model_path_disjoint_of_other_index
    {I : Type u} {K : Type v} {V : Type*}
    {G : SimpleGraph V} {root : I → V}
    (M : RootedMinorModel (SimpleGraph.completeGraph I) G root)
    {P : IndexedPairs K V} (L : IndexedLinkage G P)
    (hExact : M.toMinorModel.vertices ∩ L.vertices =
      Set.range root)
    (assigned : I → K)
    (hterm : ∀ i, root i ∈ P.terminals (assigned i))
    (i : I) (k : K) (hki : k ≠ assigned i) :
    Disjoint (M.branch i) (pathVertexSet (L.path k)) := by
  apply Set.disjoint_left.mpr
  intro v hvM hvP
  have hvRoot : v = root i := by
    have h := rooted_model_path_intersection_subset_root M L hExact i k
      ⟨hvM,hvP⟩
    simpa using h
  have hrootPath : root i ∈ pathVertexSet (L.path (assigned i)) :=
    L.terminal_subset_path (assigned i) (hterm i)
  exact (Set.disjoint_left.mp (L.disjoint hki))
    (hvRoot ▸ hvP) hrootPath


/-- The single-branch version avoids defining an assignment for all
roots when only one branch is being attached. -/
theorem rooted_model_path_disjoint_of_other_index_single
    {I : Type u} {K : Type v} {V : Type*}
    {G : SimpleGraph V} {root : I → V}
    (M : RootedMinorModel (SimpleGraph.completeGraph I) G root)
    {P : IndexedPairs K V} (L : IndexedLinkage G P)
    (hExact : M.toMinorModel.vertices ∩ L.vertices =
      Set.range root)
    (i : I) (assigned k : K)
    (hterm : root i ∈ P.terminals assigned)
    (hki : k ≠ assigned) :
    Disjoint (M.branch i) (pathVertexSet (L.path k)) := by
  apply Set.disjoint_left.mpr
  intro v hvM hvP
  have hvRoot : v = root i := by
    have h := rooted_model_path_intersection_subset_root M L hExact i k
      ⟨hvM,hvP⟩
    simpa using h
  have hrootPath : root i ∈ pathVertexSet (L.path assigned) :=
    L.terminal_subset_path assigned hterm
  exact (Set.disjoint_left.mp (L.disjoint hki))
    (hvRoot ▸ hvP) hrootPath

end HadwigerLean.Woven
