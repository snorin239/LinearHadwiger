import HadwigerLean.Graph.TouchingQuotient

/-!
# Contracting a single edge

The two ends of an edge form one connected block; every other vertex is a
singleton block. The touching quotient is therefore a minor of the original
graph, and any minor model in the quotient lifts by composition.
-/

namespace HadwigerLean

universe u

variable {V : Type u} (G : SimpleGraph V) {a b : V} (hab : G.Adj a b)

/-- The vertex type after identifying the ends of an edge. `none` is the
contracted vertex. -/
abbrev EdgeContractionVertex (a b : V) :=
  Option {x : V // x ≠ a ∧ x ≠ b}

/-- The branch of the original graph represented by a contracted vertex. -/
def edgeContractionBlock : EdgeContractionVertex a b → Set V
  | none => {a, b}
  | some x => {x.1}

theorem edgeContractionBlock_connected (hab : G.Adj a b)
    (i : EdgeContractionVertex a b) :
    (G.induce (edgeContractionBlock (a := a) (b := b) i)).Connected := by
  cases i with
  | none =>
      simpa [edgeContractionBlock] using G.induce_pair_connected_of_adj hab
  | some x =>
      simp [edgeContractionBlock]

theorem edgeContractionBlock_disjoint :
    Pairwise fun i j : EdgeContractionVertex a b =>
      Disjoint (edgeContractionBlock (a := a) (b := b) i)
        (edgeContractionBlock (a := a) (b := b) j) := by
  intro i j hij
  cases i with
  | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some y =>
          apply Set.disjoint_left.mpr
          intro x hx hy
          simp only [edgeContractionBlock, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hx hy
          rcases hx with hx | hx
          · exact y.2.1 (hy.symm.trans hx)
          · exact y.2.2 (hy.symm.trans hx)
  | some x =>
      cases j with
      | none =>
          apply Set.disjoint_left.mpr
          intro y hy hz
          simp only [edgeContractionBlock, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hy hz
          rcases hz with hz | hz
          · exact x.2.1 (hy.symm.trans hz)
          · exact x.2.2 (hy.symm.trans hz)
      | some y =>
          apply Set.disjoint_left.mpr
          intro z hz hz'
          simp only [edgeContractionBlock, Set.mem_singleton_iff] at hz hz'
          apply hij
          exact congrArg some (Subtype.ext (hz.symm.trans hz'))

theorem edgeContractionBlock_cover (x : V) :
    ∃ i : EdgeContractionVertex a b,
      x ∈ edgeContractionBlock (a := a) (b := b) i := by
  by_cases ha : x = a
  · exact ⟨none, by simp [edgeContractionBlock, ha]⟩
  by_cases hb : x = b
  · exact ⟨none, by simp [edgeContractionBlock, hb]⟩
  exact ⟨some ⟨x, ha, hb⟩, by simp [edgeContractionBlock]⟩

/-- The connected partition associated to one edge contraction. -/
def edgeContractionPartition (hab : G.Adj a b) : ConnectedPartition G (EdgeContractionVertex a b) where
  block := edgeContractionBlock (a := a) (b := b)
  connected := edgeContractionBlock_connected G hab
  disjoint := edgeContractionBlock_disjoint (a := a) (b := b)
  cover := edgeContractionBlock_cover (a := a) (b := b)

/-- The graph obtained by identifying the ends of `hab`. -/
def edgeContraction (hab : G.Adj a b) : SimpleGraph (EdgeContractionVertex a b) :=
  (edgeContractionPartition G hab).touchingQuotient

theorem edgeContraction_isMinor (hab : G.Adj a b) : IsMinor (edgeContraction G hab) G :=
  (edgeContractionPartition G hab).isMinor

/-- A model in an edge contraction lifts to the original graph. -/
theorem hasCliqueMinor_of_edgeContraction {n : ℕ}
    (h : HasCliqueMinor (edgeContraction G hab) n) : HasCliqueMinor G n :=
  hasCliqueMinor_of_minor (edgeContraction_isMinor G hab) h

end HadwigerLean
