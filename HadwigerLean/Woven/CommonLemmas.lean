import HadwigerLean.Woven.Basic

/-!
# Shared elementary woven lemmas

The up-to-budget formulation is stable under discarding some prescribed
paths. In particular, after padding a family of pairs, the dummy paths can
be dropped without changing the rooted model or its exact intersection
with the remaining linkage.
-/

namespace HadwigerLean

universe u v

namespace IndexedPairs

variable {ι : Type u} {κ : Type*} {V : Type v}

/-- The terminal set of a reindexed family is contained in the terminal set
of the original family. -/
theorem allTerminals_reindex_subset (P : IndexedPairs ι V) (f : κ → ι) :
    (P.reindex f).allTerminals ⊆ P.allTerminals := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
  exact Set.mem_iUnion.mpr ⟨f i, hi⟩

end IndexedPairs

namespace IndexedLinkage

variable {ι : Type u} {κ : Type*} {V : Type v} {G : SimpleGraph V}
  {P : IndexedPairs ι V}

/-- Deleting indexed paths only decreases the set of linkage vertices. -/
theorem reindex_vertices_subset (L : IndexedLinkage G P) (f : κ ↪ ι) :
    (L.reindex f).vertices ⊆ L.vertices := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
  exact Set.mem_iUnion.mpr ⟨f i, hi⟩

end IndexedLinkage

namespace WovenSolution

variable {V : Type v} {G : SimpleGraph V} {a j k : ℕ}
  {root : Fin a → V} {P : IndexedPairs (Fin j) V}

/-- Restrict a woven solution to an injectively indexed subfamily of pairs.
The branch sets stay unchanged; exact intersection follows from the old
exact intersection and the retained terminal paths. -/
def reindex (S : WovenSolution G root P) (f : Fin k ↪ Fin j) :
    WovenSolution G root (P.reindex f) where
  model := S.model
  linkage := S.linkage.reindex f
  exact_intersection := by
    apply Set.Subset.antisymm
    · intro x hx
      have hm : x ∈ S.model.toMinorModel.vertices := hx.1
      have hl : x ∈ S.linkage.vertices :=
        S.linkage.reindex_vertices_subset f hx.2
      have hr : x ∈ Set.range root := (S.overlap_iff x).mp ⟨hm, hl⟩ |>.1
      have ht : x ∈ (P.reindex f).allTerminals := by
        rcases Set.mem_iUnion.mp hx.2 with ⟨i, hi⟩
        have hrootterm : x ∈ P.allTerminals :=
          (S.overlap_iff x).mp ⟨hm, hl⟩ |>.2
        -- Exact intersection says that a model vertex on a retained path
        -- is one of that path's prescribed endpoints.
        have hxi : x ∈ (P.reindex f).terminals i := by
          by_contra hnot
          have hother : x ∈ S.linkage.vertices := hl
          have hpath : x ∈ pathVertexSet (S.linkage.path (f i)) := hi
          -- Disjointness of paths identifies its unique terminal index.
          rcases Set.mem_iUnion.mp hrootterm with ⟨j, hj⟩
          by_cases hji : j = f i
          · subst j
            exact hnot hj
          · exact (Set.disjoint_left.mp (S.linkage.disjoint hji))
              (S.linkage.terminal_subset_path j hj) hpath
        exact Set.mem_iUnion.mpr ⟨i, hxi⟩
      exact ⟨hr, ht⟩
    · intro x hx
      have hm : x ∈ S.model.toMinorModel.vertices := by
        rcases hx.1 with ⟨i, rfl⟩
        exact S.root_mem_model i
      have hl : x ∈ (S.linkage.reindex f).vertices := by
        rcases Set.mem_iUnion.mp hx.2 with ⟨i, hi⟩
        rcases hi with rfl | rfl
        · exact Set.mem_iUnion.mpr ⟨i, by
            change P.start (f i) ∈ pathVertexSet (S.linkage.path (f i))
            exact pathVertexSet.start_mem _⟩
        · exact Set.mem_iUnion.mpr ⟨i, by
            change P.finish (f i) ∈ pathVertexSet (S.linkage.path (f i))
            exact pathVertexSet.finish_mem _⟩
      exact ⟨hm, hl⟩

end WovenSolution

end HadwigerLean
