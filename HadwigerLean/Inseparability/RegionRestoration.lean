import HadwigerLean.Inseparability.Stages
import HadwigerLean.Inseparability.ConnectedGluing
import HadwigerLean.Inseparability.ChromaticOverlap

/-!
# Restore the chromatic region after a stage

The new high-chromatic region avoids the constructed model. Inseparability
forces it to overlap the old region in at least `k` vertices; the union is
therefore `k`-connected and preserves the model's exact tangencies.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {s k m coreBound : ℕ}

/-- Final region restoration for a sequential stage. The input stage may
have lost `m` colors; the new region restores the reserve to `m/2`. -/
def StageState.restoreRegion
    (S : StageState G s k m coreBound)
    (B : Finset V)
    (hBconn : VertexConnected (G.induce (B : Set V)) k)
    (hχB : chromatic G ≤ chromatic (G.induce (B : Set V)) + m / 2)
    (hbudget : m / 2 + k ≤ m)
    (hinsep : ¬ Bootstrap.ChromaticSeparable G m)
    (hBavoid : Disjoint (B : Set V) S.model.toMinorModel.vertices) :
    StageState G s k (m / 2) coreBound := by
  classical
  have hoverlap : k ≤ (S.region ∩ B).card :=
    overlap_card_ge_of_chromatic_inseparable
      S.region B k m hinsep S.chromatic_reserve hχB hbudget
  have hconn : VertexConnected
      (G.induce ((S.region ∪ B : Finset V) : Set V)) k :=
    vertexConnected_union_of_large_overlap
      S.region B k S.region_connected hBconn hoverlap
  have hmono : chromatic (G.induce (B : Set V)) ≤
      chromatic (G.induce ((S.region ∪ B : Finset V) : Set V)) :=
    chromatic_induce_mono_finset G (S := B) (T := S.region ∪ B) Finset.subset_union_right
  refine {
    root := S.root
    root_injective := S.root_injective
    model := S.model
    core := S.core
    region := S.region ∪ B
    region_connected := hconn
    chromatic_reserve := by omega
    core_card_le := S.core_card_le
    tangent := ?_
    intersection_in_core := ?_
    core_witness := S.core_witness
  }
  · intro i
    obtain ⟨v,hv,huniq⟩ := S.tangent i
    refine ⟨v,⟨hv.1,Finset.mem_union.mpr (Or.inl hv.2)⟩,?_⟩
    intro w hw
    have hwA : w ∈ S.region := by
      rcases Finset.mem_union.mp hw.2 with hwA | hwB
      · exact hwA
      · exact False.elim ((Set.disjoint_left.mp hBavoid) hwB
          (Set.mem_iUnion.mpr ⟨i,hw.1⟩))
    exact huniq w ⟨hw.1,hwA⟩
  · intro v hv
    rcases Finset.mem_union.mp hv.2 with hvA | hvB
    · exact S.intersection_in_core ⟨hv.1,hvA⟩
    · exact False.elim ((Set.disjoint_left.mp hBavoid) hvB hv.1)

end Inseparability
end HadwigerLean

