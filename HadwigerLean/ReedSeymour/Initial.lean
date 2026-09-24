import HadwigerLean.ReedSeymour.Partial
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# An initial partial egg decomposition

The connected components form a connected partition with an edgeless touching
quotient. Every non-egg block is therefore simplicial with no neighbors. This
provides the starting point for finite maximal-support selection, including
disconnected and empty graphs.
-/

namespace HadwigerLean

variable {V : Type*} [Fintype V]

noncomputable local instance componentFintype (G : SimpleGraph V) :
    Fintype G.ConnectedComponent := Fintype.ofFinite _

/-- Partition a graph by its connected components. -/
noncomputable def componentPartition (G : SimpleGraph V) :
    ConnectedPartition G G.ConnectedComponent where
  block C := C.supp
  connected C := C.connected_toSimpleGraph
  disjoint := by
    intro C D hCD
    apply Set.disjoint_left.mpr
    intro v hC hD
    exact hCD (hC.symm.trans hD)
  cover v := ⟨G.connectedComponentMk v, rfl⟩

omit [Fintype V] in
/-- Distinct connected components never touch. -/
theorem componentPartition_no_edges (G : SimpleGraph V)
    (C D : G.ConnectedComponent) :
    ¬ (componentPartition G).touchingQuotient.Adj C D := by
  rintro ⟨hCD, x, hx, y, hy, hxy⟩
  have hxyc := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy
  exact hCD (hx.symm.trans (hxyc.trans hy))

/-- The component partition is a partial egg decomposition for any weight. -/
theorem componentPartition_partial (G : SimpleGraph V) (w : V → ℝ) :
    IsPartialEggDecomposition (componentPartition G) w := by
  classical
  constructor
  · intro s hs
    obtain ⟨C, hC⟩ := hs
    refine ⟨C, hC, ?_⟩
    intro x y hx hy hCx hCy hxy
    exact False.elim (componentPartition_no_edges G C x hCx)
  · intro C
    right
    constructor
    · intro x y hx hy hCx hCy hxy
      exact False.elim (componentPartition_no_edges G C x hCx)
    · intro D hCD
      exact False.elim (componentPartition_no_edges G C D hCD)

/-- Every finite graph, including the empty graph, has an initial partial egg
decomposition indexed by a finite ordinal. -/
theorem exists_initial_partial_egg_decomposition_any
    (G : SimpleGraph V) (w : V → ℝ) :
    ∃ n : ℕ, ∃ P : ConnectedPartition G (Fin n),
      IsPartialEggDecomposition P w := by
  classical
  let C := componentPartition G
  let e : Fin (Fintype.card G.ConnectedComponent) ≃ G.ConnectedComponent :=
    (Fintype.equivFin G.ConnectedComponent).symm
  let P : ConnectedPartition G (Fin (Fintype.card G.ConnectedComponent)) := C.relabel e
  have hno : ∀ i j, ¬ P.touchingQuotient.Adj i j := by
    intro i j hij
    have hOld : C.touchingQuotient.Adj (e i) (e j) :=
      (C.touchingQuotientIso e).map_rel_iff.mpr hij
    exact componentPartition_no_edges G (e i) (e j) hOld
  refine ⟨Fintype.card G.ConnectedComponent, P, ?_⟩
  constructor
  · intro s hs
    obtain ⟨i, hi⟩ := hs
    refine ⟨i, hi, ?_⟩
    intro x y hx hy hix hiy hxy
    exact False.elim (hno i x hix)
  · intro i
    right
    constructor
    · intro x y hx hy hix hiy hxy
      exact False.elim (hno i x hix)
    · intro j hij
      exact False.elim (hno i j hij)
/-- A partial egg decomposition of maximal egg-support cardinality always
exists. The contradiction steps will show that every block of this choice is
an egg. -/
theorem exists_maximal_partial_egg_support_any
    (G : SimpleGraph V) (w : V → ℝ) :
    ∃ n : ℕ, ∃ P : ConnectedPartition G (Fin n),
      IsPartialEggDecomposition P w ∧
        ∀ m : ℕ, ∀ Q : ConnectedPartition G (Fin m),
          IsPartialEggDecomposition Q w →
            (eggSupport Q w).card ≤ (eggSupport P w).card :=
  exists_maximal_partial_egg_support G w
    (exists_initial_partial_egg_decomposition_any G w)
end HadwigerLean
