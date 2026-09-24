import HadwigerLean.Graph.Minor

/-!
# Touching quotients of connected partitions

The quotient has one vertex per connected block. Two distinct blocks are
adjacent precisely when an edge of the original graph joins them. In
particular, every quotient edge has a witness in the original graph; extra
edges are not discarded.
-/

namespace HadwigerLean

universe u v

/-- A partition of the vertices of `G` into nonempty connected blocks.
Finiteness is required only for the numerical minor-bound theorem below. -/
structure ConnectedPartition {V : Type v} (G : SimpleGraph V) (I : Type u) where
  block : I → Set V
  connected : ∀ i, (G.induce (block i)).Connected
  disjoint : Pairwise fun i j => Disjoint (block i) (block j)
  cover : ∀ x, ∃ i, x ∈ block i

namespace ConnectedPartition

variable {V : Type v} {I : Type u} {G : SimpleGraph V}

/-- A connected block is nonempty. -/
theorem block_nonempty (P : ConnectedPartition G I) (i : I) :
    (P.block i).Nonempty := by
  obtain ⟨x⟩ := (P.connected i).nonempty
  exact ⟨x.val, x.property⟩

/-- Every vertex lies in exactly one block. -/
theorem existsUnique_block (P : ConnectedPartition G I) (x : V) :
    ∃! i, x ∈ P.block i := by
  obtain ⟨i, hi⟩ := P.cover x
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hji
  exact (Set.disjoint_left.mp (P.disjoint hji)) hj hi

/-- Two blocks touch exactly when an original edge joins them. -/
def touchingQuotient (P : ConnectedPartition G I) : SimpleGraph I where
  Adj i j := i ≠ j ∧ ∃ x ∈ P.block i, ∃ y ∈ P.block j, G.Adj x y
  symm := ⟨by
    intro i j hij
    obtain ⟨hne, x, hx, y, hy, hxy⟩ := hij
    exact ⟨hne.symm, y, hy, x, hx, hxy.symm⟩⟩
  loopless := ⟨by
    intro i hii
    exact hii.1 rfl⟩

theorem touchingQuotient_adj_iff (P : ConnectedPartition G I) (i j : I) :
    P.touchingQuotient.Adj i j ↔
      i ≠ j ∧ ∃ x ∈ P.block i, ∃ y ∈ P.block j, G.Adj x y :=
  Iff.rfl

/-- The blocks themselves model the touching quotient as a minor. -/
def toMinorModel (P : ConnectedPartition G I) : MinorModel P.touchingQuotient G where
  branch := P.block
  connected := P.connected
  disjoint := P.disjoint
  adjacent := by
    intro i j hij
    exact (P.touchingQuotient_adj_iff i j).mp hij |>.2

theorem isMinor (P : ConnectedPartition G I) : IsMinor P.touchingQuotient G :=
  ⟨P.toMinorModel⟩

/-- A connected touching quotient has no larger complete minor. -/
theorem cliqueMinorNumber_touchingQuotient_le [Fintype V] [Fintype I]
    (P : ConnectedPartition G I) :
    cliqueMinorNumber P.touchingQuotient ≤ cliqueMinorNumber G :=
  cliqueMinorNumber_mono_minor P.isMinor

end ConnectedPartition

end HadwigerLean
