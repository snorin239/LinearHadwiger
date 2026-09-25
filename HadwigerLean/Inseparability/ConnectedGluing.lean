import HadwigerLean.Inseparability.DeletionTransport
import HadwigerLean.Graph.Linkedness.RegionLinkage

/-!
# Glue highly connected induced regions across a large overlap

The last step of the sequential induction combines its old chromatic region
with a new one. A common set of at least `k` vertices survives every deletion
of fewer than `k` vertices, and the two surviving connected regions glue.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

/-- A globally specified deletion inside a `k`-connected induced region is
connected whenever fewer than `k` vertices are deleted. -/
theorem connected_induce_sdiff_of_vertexConnected
    (A U : Finset V) (k : ℕ)
    (hA : VertexConnected (G.induce (A : Set V)) k)
    (hU : U.card < k) :
    (G.induce ((A \ U : Finset V) : Set V)).Connected := by
  classical
  let D : Finset (↥(A : Set V)) :=
    Finset.univ.filter (fun a => (a : V) ∈ U)
  let f : D → (U : Set V) := fun a =>
    ⟨a.1.1, (Finset.mem_filter.mp a.2).2⟩
  have hf : Function.Injective f := by
    intro a b h
    have hv : a.1.1 = b.1.1 := congrArg (fun u : (U : Set V) => (u : V)) h
    exact Subtype.ext (Subtype.ext hv)
  have hDcard : D.card ≤ U.card := by
    have h := Fintype.card_le_of_injective f hf
    simpa using h
  have himage : D.image Subtype.val = A ∩ U := by
    ext v
    constructor
    · intro hv
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_inter.mpr ⟨a.property,(Finset.mem_filter.mp ha).2⟩
    · intro hv
      obtain ⟨hvA,hvU⟩ := Finset.mem_inter.mp hv
      exact Finset.mem_image.mpr
        ⟨⟨v,hvA⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvU⟩,rfl⟩
  have hdiff : A \ D.image Subtype.val = A \ U := by
    ext v
    simp [himage]
  have hconn := hA.connected_delete D (lt_of_le_of_lt hDcard hU)
  have hconn' := (deletionIso G A D).connected_iff.mp hconn
  rw [hdiff] at hconn'
  exact hconn'

/-- Two `k`-connected induced vertex sets with at least `k` common vertices
have a `k`-connected induced union. -/
theorem vertexConnected_union_of_large_overlap
    (A B : Finset V) (k : ℕ)
    (hA : VertexConnected (G.induce (A : Set V)) k)
    (hB : VertexConnected (G.induce (B : Set V)) k)
    (hoverlap : k ≤ (A ∩ B).card) :
    VertexConnected (G.induce ((A ∪ B : Finset V) : Set V)) k := by
  classical
  have horder : k < Fintype.card (↥((A ∪ B : Finset V) : Set V)) := by
    have hle : Fintype.card (↥(A : Set V)) ≤
        Fintype.card (↥((A ∪ B : Finset V) : Set V)) := by
      let e : ↥(A : Set V) → ↥((A ∪ B : Finset V) : Set V) :=
        fun a => ⟨a.1, Finset.mem_union.mpr (Or.inl a.2)⟩
      have he : Function.Injective e := by
        intro a b h
        exact Subtype.ext (congrArg (fun u : ↥((A ∪ B : Finset V) : Set V) => (u : V)) h)
      exact Fintype.card_le_of_injective e he
    exact lt_of_lt_of_le hA.order_gt hle
  refine ⟨horder,?_⟩
  intro D hD
  let U : Finset V := D.image Subtype.val
  have hU : U.card < k :=
    lt_of_le_of_lt Finset.card_image_le hD
  have hAC : (G.induce ((A \ U : Finset V) : Set V)).Connected :=
    connected_induce_sdiff_of_vertexConnected A U k hA hU
  have hBC : (G.induce ((B \ U : Finset V) : Set V)).Connected :=
    connected_induce_sdiff_of_vertexConnected B U k hB hU
  have hz : ∃ z : V, z ∈ A ∩ B ∧ z ∉ U := by
    by_contra hn
    have hsub : A ∩ B ⊆ U := by
      intro z hz
      by_contra hzU
      exact hn ⟨z,hz,hzU⟩
    have hcard := Finset.card_le_card hsub
    omega
  obtain ⟨z,hzAB,hzU⟩ := hz
  have hzA : z ∈ A \ U := Finset.mem_sdiff.mpr
    ⟨(Finset.mem_inter.mp hzAB).1,hzU⟩
  have hzB : z ∈ B \ U := Finset.mem_sdiff.mpr
    ⟨(Finset.mem_inter.mp hzAB).2,hzU⟩
  have hconnected := Linkedness.connected_induce_union_of_common
    hAC hBC hzA hzB
  have hdiff : (A ∪ B) \ U = (A \ U) ∪ (B \ U) := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hset : (((A \ U : Finset V) : Set V) ∪ ((B \ U : Finset V) : Set V)) =
      (((A ∪ B) \ U : Finset V) : Set V) := by
    ext v
    simp only [Set.mem_union, Finset.mem_coe, Finset.mem_sdiff, Finset.mem_union]
    tauto
  rw [hset] at hconnected
  exact (deletionIso G (A ∪ B) D).connected_iff.mpr hconnected

end Inseparability
end HadwigerLean




