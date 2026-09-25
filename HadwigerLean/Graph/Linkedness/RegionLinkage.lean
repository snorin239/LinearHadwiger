import HadwigerLean.Graph.IndexedLinkage
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Extracting disjoint paths from disjoint connected regions
-/

namespace HadwigerLean
namespace Linkedness

/-- A connected induced region containing both endpoints contains a path
between them whose support remains in that region. -/
theorem exists_path_in_connected_region
    {V : Type*} {G : SimpleGraph V} {s t : V} (R : Set V)
    (hR : (G.induce R).Connected) (hs : s ∈ R) (ht : t ∈ R) :
    ∃ p : G.Path s t, pathVertexSet p ⊆ R := by
  let a : R := ⟨s, hs⟩
  let b : R := ⟨t, ht⟩
  obtain ⟨w, hw⟩ := hR.exists_isPath a b
  let e : (G.induce R) ↪g G := SimpleGraph.Embedding.induce R
  let p : G.Path s t :=
    SimpleGraph.Path.mapEmbedding e (⟨w, hw⟩ : (G.induce R).Path a b)
  refine ⟨p, ?_⟩
  intro z hz
  change z ∈ (w.map e.toHom).support at hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨q, _, hq⟩ := List.mem_map.mp hz
  exact hq ▸ q.property

/-- Two connected induced regions sharing a vertex have connected union. -/
theorem connected_induce_union_of_common
    {V : Type*} {G : SimpleGraph V} {A B : Set V}
    (hA : (G.induce A).Connected) (hB : (G.induce B).Connected)
    {z : V} (hzA : z ∈ A) (hzB : z ∈ B) :
    (G.induce (A ∪ B)).Connected := by
  let eA : (G.induce A) ↪g (G.induce (A ∪ B)) :=
    G.induceHomOfLE (fun x hx => Or.inl hx)
  let eB : (G.induce B) ↪g (G.induce (A ∪ B)) :=
    G.induceHomOfLE (fun x hx => Or.inr hx)
  have reachA {x : V} (hx : x ∈ A) :
      (G.induce (A ∪ B)).Reachable ⟨x, Or.inl hx⟩
        ⟨z, Or.inl hzA⟩ :=
    (hA.preconnected ⟨x, hx⟩ ⟨z, hzA⟩).map eA.toHom
  have reachB {x : V} (hx : x ∈ B) :
      (G.induce (A ∪ B)).Reachable ⟨x, Or.inr hx⟩
        ⟨z, Or.inl hzA⟩ := by
    have h := (hB.preconnected ⟨x, hx⟩ ⟨z, hzB⟩).map eB.toHom
    exact h
  haveI : Nonempty (↑(A ∪ B : Set V)) := ⟨⟨z, Or.inl hzA⟩⟩
  refine ⟨?_⟩
  intro x y
  have hx : (G.induce (A ∪ B)).Reachable x ⟨z, Or.inl hzA⟩ := by
    rcases x.property with hxA | hxB
    · exact reachA hxA
    · exact reachB hxB
  have hy : (G.induce (A ∪ B)).Reachable y ⟨z, Or.inl hzA⟩ := by
    rcases y.property with hyA | hyB
    · exact reachA hyA
    · exact reachB hyB
  exact hx.trans hy.symm
/-- Pairwise disjoint connected regions containing their respective terminal
pairs yield an indexed linkage. -/
theorem exists_linkage_of_disjoint_connected_regions
    {ι V : Type*} {G : SimpleGraph V} (P : IndexedPairs ι V)
    (R : ι → Set V)
    (hconn : ∀ i, (G.induce (R i)).Connected)
    (hstart : ∀ i, P.start i ∈ R i)
    (hfinish : ∀ i, P.finish i ∈ R i)
    (hdis : Pairwise fun i j => Disjoint (R i) (R j)) :
    ∃ L : IndexedLinkage G P,
      ∀ i, pathVertexSet (L.path i) ⊆ R i := by
  classical
  have hp (i : ι) :
      ∃ p : G.Path (P.start i) (P.finish i), pathVertexSet p ⊆ R i :=
    exists_path_in_connected_region (R i) (hconn i) (hstart i) (hfinish i)
  let p (i : ι) := Classical.choose (hp i)
  have hps (i : ι) : pathVertexSet (p i) ⊆ R i :=
    Classical.choose_spec (hp i)
  let L : IndexedLinkage G P := {
    path := p
    disjoint := by
      intro i j hij
      exact Set.disjoint_of_subset (hps i) (hps j) (hdis hij)
  }
  exact ⟨L, hps⟩

end Linkedness
end HadwigerLean
