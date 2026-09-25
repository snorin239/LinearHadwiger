import HadwigerLean.Graph.VertexConnectivity
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Indexed terminal pairs and linkages

Indices distinguish prescribed pairs, even when a pair has equal endpoints.
Mathlib's `SimpleGraph.Path` includes the length-zero path `Path.nil`; this is
the one-vertex path required for a singleton pair.
-/

namespace HadwigerLean

universe u v

/-- A family of ordered terminal pairs. The two terminals in one pair may
coincide. -/
structure IndexedPairs (ι : Type u) (V : Type v) where
  start : ι → V
  finish : ι → V

namespace IndexedPairs

variable {ι : Type u} {V : Type v}

/-- Both endpoints of one indexed pair, as a set. -/
def terminals (P : IndexedPairs ι V) (i : ι) : Set V :=
  {P.start i, P.finish i}

/-- Distinct indexed pairs have disjoint terminal sets. -/
def DisjointTerminals (P : IndexedPairs ι V) : Prop :=
  Pairwise fun i j => Disjoint (P.terminals i) (P.terminals j)

theorem start_injective {P : IndexedPairs ι V} (h : P.DisjointTerminals) :
    Function.Injective P.start := by
  intro i j hij
  by_contra hne
  have hd := Set.disjoint_left.mp (h hne)
  exact hd (show P.start i ∈ P.terminals i by simp [terminals])
    (show P.start i ∈ P.terminals j by simp [terminals, hij])

theorem finish_injective {P : IndexedPairs ι V} (h : P.DisjointTerminals) :
    Function.Injective P.finish := by
  intro i j hij
  by_contra hne
  have hd := Set.disjoint_left.mp (h hne)
  exact hd (show P.finish i ∈ P.terminals i by simp [terminals])
    (show P.finish i ∈ P.terminals j by simp [terminals, hij])

/-- Relabel a family of pairs by a function on its index set. -/
def reindex (P : IndexedPairs ι V) {κ : Type*} (f : κ → ι) :
    IndexedPairs κ V where
  start := P.start ∘ f
  finish := P.finish ∘ f

end IndexedPairs

/-- The vertices visited by a path, including both endpoints. -/
def pathVertexSet {V : Type v} {G : SimpleGraph V} {s t : V}
    (p : G.Path s t) : Set V :=
  {x | x ∈ (p : G.Walk s t).support}

namespace pathVertexSet

variable {V : Type v} {G : SimpleGraph V} {s t : V}

theorem start_mem (p : G.Path s t) : s ∈ pathVertexSet p :=
  (p : G.Walk s t).start_mem_support

theorem finish_mem (p : G.Path s t) : t ∈ pathVertexSet p :=
  (p : G.Walk s t).end_mem_support

@[simp] theorem nil (s : V) :
    pathVertexSet (SimpleGraph.Path.nil : G.Path s s) = {s} := by
  ext x
  simp [pathVertexSet]

theorem loop (p : G.Path s s) : pathVertexSet p = {s} := by
  rw [p.loop_eq]
  exact nil s

theorem eq_singleton_of_eq (p : G.Path s t) (hst : s = t) :
    pathVertexSet p = {s} := by
  subst t
  exact loop p

end pathVertexSet

/-- A vertex-disjoint path for each indexed terminal pair. Singleton paths
are allowed and represented by `SimpleGraph.Path.nil`. -/
structure IndexedLinkage {ι : Type u} {V : Type v}
    (G : SimpleGraph V) (P : IndexedPairs ι V) where
  path : ∀ i, G.Path (P.start i) (P.finish i)
  disjoint : Pairwise fun i j =>
    Disjoint (pathVertexSet (path i)) (pathVertexSet (path j))

namespace IndexedLinkage

variable {ι : Type u} {V : Type v} {G : SimpleGraph V}
    {P : IndexedPairs ι V}

/-- The union of all path vertex sets. -/
def vertices (L : IndexedLinkage G P) : Set V :=
  ⋃ i, pathVertexSet (L.path i)

theorem path_subset_vertices (L : IndexedLinkage G P) (i : ι) :
    pathVertexSet (L.path i) ⊆ L.vertices := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨i, hx⟩

theorem start_mem_vertices (L : IndexedLinkage G P) (i : ι) :
    P.start i ∈ L.vertices :=
  L.path_subset_vertices i (pathVertexSet.start_mem (L.path i))

theorem finish_mem_vertices (L : IndexedLinkage G P) (i : ι) :
    P.finish i ∈ L.vertices :=
  L.path_subset_vertices i (pathVertexSet.finish_mem (L.path i))

theorem terminal_subset_path (L : IndexedLinkage G P) (i : ι) :
    P.terminals i ⊆ pathVertexSet (L.path i) := by
  intro x hx
  rcases hx with rfl | rfl
  · exact pathVertexSet.start_mem (L.path i)
  · exact pathVertexSet.finish_mem (L.path i)

/-- The existence of a linkage enforces disjoint terminals across indices. -/
theorem disjointTerminals (L : IndexedLinkage G P) : P.DisjointTerminals := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  exact (Set.disjoint_left.mp (L.disjoint hij))
    (L.terminal_subset_path i hxi) (L.terminal_subset_path j hxj)

theorem start_injective (L : IndexedLinkage G P) : Function.Injective P.start :=
  IndexedPairs.start_injective L.disjointTerminals

theorem finish_injective (L : IndexedLinkage G P) : Function.Injective P.finish :=
  IndexedPairs.finish_injective L.disjointTerminals

/-- Restrict an indexed linkage along an injective map of indices. -/
def reindex (L : IndexedLinkage G P) {κ : Type*} (f : κ ↪ ι) :
    IndexedLinkage G (P.reindex f) where
  path := fun i => L.path (f i)
  disjoint := by
    intro i j hij
    exact L.disjoint (fun h => hij (f.injective h))

private def singletonPath (h : ∀ i, P.start i = P.finish i) (i : ι) :
    G.Path (P.start i) (P.finish i) := by
  rw [← h i]
  exact SimpleGraph.Path.nil

private theorem singletonPath_vertices (h : ∀ i, P.start i = P.finish i) (i : ι) :
    pathVertexSet (singletonPath (G := G) h i) = P.terminals i := by
  have hp : pathVertexSet (singletonPath (G := G) h i) = {P.start i} :=
    pathVertexSet.eq_singleton_of_eq _ (h i)
  rw [hp]
  simp [IndexedPairs.terminals, ← h i]

/-- The family of length-zero paths links any disjoint family of singleton
terminal pairs. -/
def of_singletons (h : ∀ i, P.start i = P.finish i)
    (hdis : P.DisjointTerminals) : IndexedLinkage G P where
  path := singletonPath h
  disjoint := by
    intro i j hij
    rw [singletonPath_vertices h i, singletonPath_vertices h j]
    exact hdis hij

end IndexedLinkage

end HadwigerLean
