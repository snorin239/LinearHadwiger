import HadwigerLean.Graph.SmallConnected.PackedMax
import Mathlib.Tactic

/-!
# The block vertices in a simultaneous contraction quotient
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} (F : ConnectedBlockFamily G)

noncomputable def ConnectedBlockFamily.blockVertices : Finset F.Vertex := by
  classical
  exact Finset.univ.filter fun q =>
    match q with | .inl _ => True | .inr _ => False

theorem ConnectedBlockFamily.mem_blockVertices_inl
    (B : ↥(F.blocks : Set (Finset V))) :
    (Sum.inl B : F.Vertex) ∈ F.blockVertices := by
  simp [ConnectedBlockFamily.blockVertices]

theorem ConnectedBlockFamily.not_mem_blockVertices_inr
    (x : {v : V // v ∉ F.covered}) :
    (Sum.inr x : F.Vertex) ∉ F.blockVertices := by
  simp [ConnectedBlockFamily.blockVertices]

theorem ConnectedBlockFamily.blockVertices_card :
    F.blockVertices.card = F.blocks.card := by
  classical
  have heq : F.blockVertices =
      (Finset.univ : Finset ↥(F.blocks : Set (Finset V))).map
        Function.Embedding.inl := by
    ext q
    cases q <;> simp [ConnectedBlockFamily.blockVertices]
  rw [heq, Finset.card_map]
  simpa using Fintype.card_coe F.blocks

theorem ConnectedBlockFamily.singletonLift_disjoint_blockVertices
    (H : Finset V) : Disjoint (F.singletonLift H) F.blockVertices := by
  apply Finset.disjoint_left.mpr
  intro q hq hblock
  cases q with
  | inl B => exact F.not_mem_singletonLift_inl H B hq
  | inr x => exact F.not_mem_blockVertices_inr x hblock

end HadwigerLean
