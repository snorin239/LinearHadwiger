import HadwigerLean.Inseparability.RawModelAssembly
import HadwigerLean.Woven.Basic
import Mathlib.Tactic

/-!
# Reindexing a woven child's rooted model

The woven rerouting API uses `Fin (2x)` roots; the CI raw model names them
by a side in `Fin 2` and an offset in `Fin x`. Reindexing preserves every
branch vertex and the exact model-linkage root intersection.
-/

namespace HadwigerLean.Inseparability

universe u

def ciChildRootFin {V : Type u} (x : ℕ)
    (childRoot : Fin 2 × Fin x → V) : Fin (2 * x) → V :=
  fun n => childRoot (finProdFinEquiv.symm n)

def ciChildModelReindex {V : Type u} {G : SimpleGraph V}
    (x : ℕ) (childRoot : Fin 2 × Fin x → V)
    (M : RootedMinorModel
      (SimpleGraph.completeGraph (Fin (2 * x))) G
      (ciChildRootFin x childRoot)) :
    RootedMinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G childRoot where
  branch := fun z => M.branch (finProdFinEquiv z)
  connected := fun z => M.connected (finProdFinEquiv z)
  disjoint := by
    intro z w hzw
    exact M.disjoint (fun h => hzw (finProdFinEquiv.injective h))
  adjacent := by
    intro z w hzw
    exact M.adjacent (fun h => hzw (finProdFinEquiv.injective h))
  root_mem := by
    intro z
    simpa [ciChildRootFin] using M.root_mem (finProdFinEquiv z)

theorem ciChildModelReindex_vertices {V : Type u} {G : SimpleGraph V}
    (x : ℕ) (childRoot : Fin 2 × Fin x → V)
    (M : RootedMinorModel
      (SimpleGraph.completeGraph (Fin (2 * x))) G
      (ciChildRootFin x childRoot)) :
    (ciChildModelReindex x childRoot M).toMinorModel.vertices =
      M.toMinorModel.vertices := by
  ext v
  constructor
  · intro hv
    obtain ⟨z,hz⟩ := Set.mem_iUnion.mp hv
    exact Set.mem_iUnion.mpr ⟨finProdFinEquiv z,
      by simpa [ciChildModelReindex, rootedCliqueModel_reindex] using hz⟩
  · intro hv
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hv
    exact Set.mem_iUnion.mpr ⟨finProdFinEquiv.symm n,
      by
        change v ∈ M.branch (finProdFinEquiv (finProdFinEquiv.symm n))
        rw [Equiv.apply_symm_apply]
        exact hn⟩

theorem ciChildModelReindex_exact {V : Type u} {G : SimpleGraph V}
    {K : Type*} {P : IndexedPairs K V} (L : IndexedLinkage G P)
    (x : ℕ) (childRoot : Fin 2 × Fin x → V)
    (M : RootedMinorModel
      (SimpleGraph.completeGraph (Fin (2 * x))) G
      (ciChildRootFin x childRoot))
    (hExact : M.toMinorModel.vertices ∩ L.vertices =
      Set.range (ciChildRootFin x childRoot)) :
    (ciChildModelReindex x childRoot M).toMinorModel.vertices ∩
      L.vertices = Set.range childRoot := by
  rw [ciChildModelReindex_vertices, hExact]
  ext v
  constructor
  · rintro ⟨n,rfl⟩
    exact ⟨finProdFinEquiv.symm n,rfl⟩
  · rintro ⟨z,rfl⟩
    exact ⟨finProdFinEquiv z,by simp [ciChildRootFin]⟩

end HadwigerLean.Inseparability





