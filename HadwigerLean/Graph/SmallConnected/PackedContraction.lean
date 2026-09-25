import HadwigerLean.Graph.TouchingQuotient
import HadwigerLean.Graph.DensityBasic
import Mathlib.Tactic

/-!
# Contracting a disjoint family of connected vertex sets
-/

namespace HadwigerLean

universe u
variable {V : Type u} [DecidableEq V]

/-- A finite family of pairwise disjoint connected vertex blocks. -/
structure ConnectedBlockFamily (G : SimpleGraph V) where
  blocks : Finset (Finset V)
  connected : ∀ B ∈ blocks, (G.induce (B : Set V)).Connected
  disjoint : ∀ B ∈ blocks, ∀ C ∈ blocks, B ≠ C →
    Disjoint (B : Set V) (C : Set V)

namespace ConnectedBlockFamily

variable {G : SimpleGraph V} (F : ConnectedBlockFamily G)

/-- Union of all contracted blocks. -/
def covered : Finset V := F.blocks.biUnion id

/-- One vertex per contracted block and one per surviving original vertex. -/
abbrev Vertex := Sum ↥(F.blocks : Set (Finset V))
  {v : V // v ∉ F.covered}

/-- The original vertices represented by a quotient vertex. -/
def block : F.Vertex → Set V
  | .inl B => (B.1 : Set V)
  | .inr x => {x.1}

theorem block_connected (i : F.Vertex) :
    (G.induce (F.block i)).Connected := by
  cases i with
  | inl B => exact F.connected B.1 B.2
  | inr x => simp [block]

theorem block_disjoint :
    Pairwise fun i j : F.Vertex => Disjoint (F.block i) (F.block j) := by
  intro i j hij
  cases i with
  | inl B =>
      cases j with
      | inl C =>
          have hBC : B.1 ≠ C.1 := by
            intro h
            apply hij
            exact congrArg Sum.inl (Subtype.ext h)
          exact F.disjoint B.1 B.2 C.1 C.2 hBC
      | inr y =>
          apply Set.disjoint_left.mpr
          intro x hx hy
          have hxy : x = y.1 := by simpa [block] using hy
          subst x
          have hycovered : y.1 ∈ F.covered := by
            simp only [covered, Finset.mem_biUnion]
            exact ⟨B.1, B.2, hx⟩
          exact y.2 hycovered
  | inr x =>
      cases j with
      | inl B =>
          apply Set.disjoint_left.mpr
          intro y hy hx
          have hyx : y = x.1 := by simpa [block] using hy
          subst y
          have hxcovered : x.1 ∈ F.covered := by
            simp only [covered, Finset.mem_biUnion]
            exact ⟨B.1, B.2, hx⟩
          exact x.2 hxcovered
      | inr y =>
          apply Set.disjoint_left.mpr
          intro z hz hz'
          have hzx : z = x.1 := by simpa [block] using hz
          have hzy : z = y.1 := by simpa [block] using hz'
          apply hij
          exact congrArg Sum.inr (Subtype.ext (hzx.symm.trans hzy))

theorem block_cover (v : V) : ∃ i : F.Vertex, v ∈ F.block i := by
  by_cases hv : v ∈ F.covered
  · obtain ⟨B, hBF, hvB⟩ := Finset.mem_biUnion.mp hv
    exact ⟨.inl ⟨B, hBF⟩, hvB⟩
  · exact ⟨.inr ⟨v, hv⟩, by simp [block]⟩

/-- The connected partition associated to the block family. -/
def partition : ConnectedPartition G F.Vertex where
  block := F.block
  connected := F.block_connected
  disjoint := F.block_disjoint
  cover := F.block_cover

/-- Simultaneously contract the family of connected blocks. -/
def quotient : SimpleGraph F.Vertex := F.partition.touchingQuotient

theorem quotient_isMinor : IsMinor F.quotient G := F.partition.isMinor

end ConnectedBlockFamily
end HadwigerLean