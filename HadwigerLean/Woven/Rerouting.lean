import HadwigerLean.Woven.CommonLemmas
import HadwigerLean.Graph.RootedCliqueMinor.InducedLinkage
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Rerouting a linkage through a woven child

For a path meeting the child, the first hit and the last hit delimit
outer path pieces which meet the child only at their ends. These pieces
are reused after the child supplies an internal linkage.
-/

namespace HadwigerLean

universe u

/-- The two exterior pieces of a path around its first and last visits
to a finite vertex set. -/
structure PathExterior {V : Type u} {G : SimpleGraph V} {s t : V}
    (p : G.Path s t) (H : Finset V) where
  first : V
  last : V
  first_mem : first ∈ H
  last_mem : last ∈ H
  headPath : G.Path s first
  tailPath : G.Path last t
  headPath_subset : pathVertexSet headPath ⊆ pathVertexSet p
  tailPath_subset : pathVertexSet tailPath ⊆ pathVertexSet p
  headPath_hits : ∀ x ∈ pathVertexSet headPath, x ∈ H → x = first
  tailPath_hits : ∀ x ∈ pathVertexSet tailPath, x ∈ H → x = last

namespace PathExterior

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} {s t : V}
  {p : G.Path s t} {H : Finset V}

/-- Every path meeting H admits first and last hit exterior pieces. -/
theorem exists_of_hit (hhit : ∃ x ∈ H, x ∈ pathVertexSet p) :
    Nonempty (PathExterior p H) := by
  classical
  let w : G.Walk s t := p
  have hhitW : {x ∈ H | x ∈ w.support}.Nonempty := by
    obtain ⟨x, hxH, hxp⟩ := hhit
    change x ∈ w.support at hxp
    exact ⟨x, Finset.mem_filter.mpr ⟨hxH, hxp⟩⟩
  obtain ⟨u, huH, huW, hfirst⟩ :=
    w.exists_mem_support_forall_mem_support_imp_eq H hhitW
  have hhitRev : {x ∈ H | x ∈ w.reverse.support}.Nonempty := by
    obtain ⟨x, hxH, hxp⟩ := hhit
    refine ⟨x, Finset.mem_filter.mpr ⟨hxH, ?_⟩⟩
    change x ∈ w.support at hxp
    simpa [SimpleGraph.Walk.support_reverse] using hxp
  obtain ⟨v, hvH, hvRev, hlast⟩ :=
    w.reverse.exists_mem_support_forall_mem_support_imp_eq H hhitRev
  let pre : G.Path s u := ⟨w.takeUntil u huW, p.property.takeUntil huW⟩
  let suf : G.Path v t :=
    ⟨(w.reverse.takeUntil v hvRev).reverse,
      (p.property.reverse.takeUntil hvRev).reverse⟩
  refine ⟨{
    first := u
    last := v
    first_mem := huH
    last_mem := hvH
    headPath := pre
    tailPath := suf
    headPath_subset := ?_
    tailPath_subset := ?_
    headPath_hits := ?_
    tailPath_hits := ?_
  }⟩
  · intro x hx
    exact w.support_takeUntil_subset_support huW hx
  · intro x hx
    have hxRev : x ∈ (w.reverse.takeUntil v hvRev).support := by
      simpa [suf, pathVertexSet, SimpleGraph.Walk.support_reverse] using hx
    have hxWRev := w.reverse.support_takeUntil_subset_support hvRev hxRev
    change x ∈ w.support
    simpa [SimpleGraph.Walk.support_reverse] using hxWRev
  · intro x hx hxH
    exact hfirst x hxH hx
  · intro x hx hxH
    have hxRev : x ∈ (w.reverse.takeUntil v hvRev).support := by
      simpa [suf, pathVertexSet, SimpleGraph.Walk.support_reverse] using hx
    exact hlast x hxH hxRev

end PathExterior

namespace IndexedLinkage

/-- The indices of paths that meet the child vertex set. -/
def HitIndex {V : Type*} {G : SimpleGraph V} {j : ℕ}
    {P : IndexedPairs (Fin j) V} (L : IndexedLinkage G P)
    (H : Finset V) :=
  {i : Fin j // ∃ x ∈ H, x ∈ pathVertexSet (L.path i)}

/-- First and last child hits of one indexed path. -/
noncomputable def exterior {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {j : ℕ} {P : IndexedPairs (Fin j) V}
    (L : IndexedLinkage G P) (H : Finset V)
    (i : L.HitIndex H) : PathExterior (L.path i.1) H :=
  Classical.choice (PathExterior.exists_of_hit i.2)

/-- The child pairs formed by the first and last hits. -/
noncomputable def innerPairs {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {j : ℕ} {P : IndexedPairs (Fin j) V}
    (L : IndexedLinkage G P) (H : Finset V) :
    IndexedPairs (L.HitIndex H) (H : Set V) where
  start := fun i => ⟨(L.exterior H i).first, (L.exterior H i).first_mem⟩
  finish := fun i => ⟨(L.exterior H i).last, (L.exterior H i).last_mem⟩

/-- Inner terminal sets on different old paths remain disjoint. -/
theorem innerPairs_disjointTerminals
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {j : ℕ} {P : IndexedPairs (Fin j) V}
    (L : IndexedLinkage G P) (H : Finset V) :
    (L.innerPairs H).DisjointTerminals := by
  intro i k hik
  apply Set.disjoint_left.mpr
  intro x hxi hxk
  have hi : (x : V) ∈ pathVertexSet (L.path i.1) := by
    rcases hxi with hxi | hxi
    · have hx : (x : V) = (L.exterior H i).first := congrArg Subtype.val hxi
      rw [hx]
      exact (L.exterior H i).headPath_subset
        (pathVertexSet.finish_mem (L.exterior H i).headPath)
    · have hx : (x : V) = (L.exterior H i).last := congrArg Subtype.val hxi
      rw [hx]
      exact (L.exterior H i).tailPath_subset
        (pathVertexSet.start_mem (L.exterior H i).tailPath)
  have hk : (x : V) ∈ pathVertexSet (L.path k.1) := by
    rcases hxk with hxk | hxk
    · have hx : (x : V) = (L.exterior H k).first := congrArg Subtype.val hxk
      rw [hx]
      exact (L.exterior H k).headPath_subset
        (pathVertexSet.finish_mem (L.exterior H k).headPath)
    · have hx : (x : V) = (L.exterior H k).last := congrArg Subtype.val hxk
      rw [hx]
      exact (L.exterior H k).tailPath_subset
        (pathVertexSet.start_mem (L.exterior H k).tailPath)
  have hne : i.1 ≠ k.1 := by
    intro heq
    exact hik (Subtype.ext heq)
  exact (Set.disjoint_left.mp (L.disjoint hne)) hi hk

end IndexedLinkage
namespace IndexedLinkage

/-- Candidate vertex set for a rerouted path. Only paths meeting H are
changed; their exterior pieces are joined by the supplied inner path. -/
noncomputable def rerouteRegion
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {j : ℕ} {P : IndexedPairs (Fin j) V}
    (L : IndexedLinkage G P) (H : Finset V)
    {Q : IndexedPairs (L.HitIndex H) V} (I : IndexedLinkage G Q)
    (i : Fin j) : Set V := by
  classical
  exact if hi : ∃ x ∈ H, x ∈ pathVertexSet (L.path i) then
    pathVertexSet (L.exterior H ⟨i, hi⟩).headPath ∪
      pathVertexSet (I.path ⟨i, hi⟩) ∪
      pathVertexSet (L.exterior H ⟨i, hi⟩).tailPath
    else pathVertexSet (L.path i)

/-- An outside vertex of a rerouted region lies on its original path. -/
theorem rerouteRegion_outside_old
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {j : ℕ} {P : IndexedPairs (Fin j) V}
    (L : IndexedLinkage G P) (H : Finset V)
    {Q : IndexedPairs (L.HitIndex H) V} (I : IndexedLinkage G Q)
    (hI : I.vertices ⊆ (H : Set V))
    (i : Fin j) {x : V}
    (hx : x ∈ L.rerouteRegion H I i) (hxH : x ∉ H) :
    x ∈ pathVertexSet (L.path i) := by
  classical
  by_cases hi : ∃ y ∈ H, y ∈ pathVertexSet (L.path i)
  · simp only [rerouteRegion, dif_pos hi] at hx
    rcases hx with (hx | hx) | hx
    · exact (L.exterior H ⟨i, hi⟩).headPath_subset hx
    · exact False.elim (hxH (hI (Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩)))
    · exact (L.exterior H ⟨i, hi⟩).tailPath_subset hx
  · simpa only [rerouteRegion, dif_neg hi] using hx

/-- A child vertex in a rerouted region lies on that path's inner piece. -/
theorem rerouteRegion_inside_inner
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {j : ℕ} {P : IndexedPairs (Fin j) V}
    (L : IndexedLinkage G P) (H : Finset V)
    {Q : IndexedPairs (L.HitIndex H) V} (I : IndexedLinkage G Q)
    (hQstart : ∀ k, Q.start k = (L.exterior H k).first)
    (hQfinish : ∀ k, Q.finish k = (L.exterior H k).last)
    (i : Fin j) {x : V}
    (hx : x ∈ L.rerouteRegion H I i) (hxH : x ∈ H) :
    ∃ hi : ∃ y ∈ H, y ∈ pathVertexSet (L.path i),
      x ∈ pathVertexSet (I.path ⟨i, hi⟩) := by
  classical
  by_cases hi : ∃ y ∈ H, y ∈ pathVertexSet (L.path i)
  · refine ⟨hi, ?_⟩
    simp only [rerouteRegion, dif_pos hi] at hx
    rcases hx with (hx | hx) | hx
    · have heq := (L.exterior H ⟨i, hi⟩).headPath_hits x hx hxH
      rw [heq]
      simpa only [hQstart ⟨i, hi⟩] using
        (pathVertexSet.start_mem (I.path ⟨i, hi⟩))
    · exact hx
    · have heq := (L.exterior H ⟨i, hi⟩).tailPath_hits x hx hxH
      rw [heq]
      simpa only [hQfinish ⟨i, hi⟩] using
        (pathVertexSet.finish_mem (I.path ⟨i, hi⟩))
  · have hxOld : x ∈ pathVertexSet (L.path i) := by
      simpa only [rerouteRegion, dif_neg hi] using hx
    exact False.elim (hi ⟨x, hxH, hxOld⟩)

end IndexedLinkage
/-- The union of two connected induced subgraphs that share a vertex is
connected. -/
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
namespace IndexedPairs

/-- Surjective reindexing preserves the complete terminal set. -/
theorem allTerminals_reindex_eq_of_surjective
    {ι κ V : Type*} (P : IndexedPairs ι V) (f : κ → ι)
    (hf : Function.Surjective f) :
    (P.reindex f).allTerminals = P.allTerminals := by
  apply Set.Subset.antisymm
  · exact P.allTerminals_reindex_subset f
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, rfl⟩ := hf i
    exact Set.mem_iUnion.mpr ⟨j, hi⟩

end IndexedPairs

namespace IndexedLinkage

/-- Surjective reindexing preserves every vertex used by a linkage. -/
theorem vertices_reindex_eq_of_surjective
    {ι κ V : Type*} {G : SimpleGraph V} {P : IndexedPairs ι V}
    (L : IndexedLinkage G P) (f : κ ↪ ι)
    (hf : Function.Surjective f) :
    (L.reindex f).vertices = L.vertices := by
  apply Set.Subset.antisymm
  · exact L.reindex_vertices_subset f
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, rfl⟩ := hf i
    exact Set.mem_iUnion.mpr ⟨j, hi⟩

end IndexedLinkage

namespace Woven

/-- Up-to-budget wovenness also works for an arbitrary finite index type
+of terminal pairs. -/
theorem for_fintype_index
    {V I : Type*} [Fintype I] {G : SimpleGraph V}
    {a b : ℕ} (hW : Woven G a b)
    (root : Fin a → V) (hroot : Function.Injective root)
    (P : IndexedPairs I V) (hP : P.DisjointTerminals)
    (hcard : Fintype.card I ≤ b) :
    ∃ (Q : IndexedPairs I V)
      (M : RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G root)
      (L : IndexedLinkage G Q),
      (∀ i, Q.start i = P.start i) ∧
      (∀ i, Q.finish i = P.finish i) ∧
      M.toMinorModel.vertices ∩ L.vertices =
        Set.range root ∩ P.allTerminals := by
  classical
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let P' := P.reindex e.symm
  have hP' : P'.DisjointTerminals := by
    intro i j hij
    exact hP (e.symm.injective.ne hij)
  obtain ⟨S⟩ := hW root hroot (Fintype.card I) hcard P' hP'
  let f : I ↪ Fin (Fintype.card I) := e.toEmbedding
  let Q := P'.reindex f
  let L : IndexedLinkage G Q := S.linkage.reindex f
  have hverts : L.vertices = S.linkage.vertices :=
    S.linkage.vertices_reindex_eq_of_surjective f e.surjective
  have hterms : P'.allTerminals = P.allTerminals :=
    P.allTerminals_reindex_eq_of_surjective e.symm e.symm.surjective
  refine ⟨Q, S.model, L, ?_, ?_, ?_⟩
  · intro i
    simp [Q, P', f, IndexedPairs.reindex]
  · intro i
    simp [Q, P', f, IndexedPairs.reindex]
  · rw [hverts, ← hterms]
    exact S.exact_intersection
end Woven

theorem exists_path_in_connected_set
    {V : Type*} {G : SimpleGraph V} {s t : V} (C : Set V)
    (hC : (G.induce C).Connected) (hs : s ∈ C) (ht : t ∈ C) :
    ∃ p : G.Path s t, pathVertexSet p ⊆ C := by
  let a : C := ⟨s, hs⟩
  let b : C := ⟨t, ht⟩
  obtain ⟨w, hw⟩ := hC.exists_isPath a b
  let e : (G.induce C) ↪g G := SimpleGraph.Embedding.induce C
  let p : G.Path s t := SimpleGraph.Path.mapEmbedding e (⟨w, hw⟩ : (G.induce C).Path a b)
  refine ⟨p, ?_⟩
  intro z hz
  change z ∈ (w.map e.toHom).support at hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨q, _, hq⟩ := List.mem_map.mp hz
  exact hq ▸ q.property

namespace IndexedLinkage

theorem rerouteRegion_connected
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {j : ℕ} {P : IndexedPairs (Fin j) V}
    (L : IndexedLinkage G P) (H : Finset V)
    {Q : IndexedPairs (L.HitIndex H) V} (I : IndexedLinkage G Q)
    (hQstart : ∀ k, Q.start k = (L.exterior H k).first)
    (hQfinish : ∀ k, Q.finish k = (L.exterior H k).last)
    (i : Fin j) : (G.induce (L.rerouteRegion H I i)).Connected := by
  classical
  by_cases hi : ∃ y ∈ H, y ∈ pathVertexSet (L.path i)
  · let E := L.exterior H ⟨i, hi⟩
    have hhead : (G.induce (pathVertexSet E.headPath)).Connected :=
      (E.headPath : G.Walk (P.start i) E.first).connected_induce_support
    have hinner : (G.induce (pathVertexSet (I.path ⟨i, hi⟩))).Connected :=
      (I.path ⟨i, hi⟩ : G.Walk (Q.start ⟨i, hi⟩) (Q.finish ⟨i, hi⟩)).connected_induce_support
    have htail : (G.induce (pathVertexSet E.tailPath)).Connected :=
      (E.tailPath : G.Walk E.last (P.finish i)).connected_induce_support
    have hfirstHead : E.first ∈ pathVertexSet E.headPath :=
      pathVertexSet.finish_mem E.headPath
    have hfirstInner : E.first ∈ pathVertexSet (I.path ⟨i, hi⟩) := by
      rw [← hQstart ⟨i, hi⟩]
      exact pathVertexSet.start_mem _
    have hlastInner : E.last ∈ pathVertexSet (I.path ⟨i, hi⟩) := by
      rw [← hQfinish ⟨i, hi⟩]
      exact pathVertexSet.finish_mem _
    have hlastTail : E.last ∈ pathVertexSet E.tailPath :=
      pathVertexSet.start_mem E.tailPath
    have hfront := connected_induce_union_of_common hhead hinner
      hfirstHead hfirstInner
    have hall := connected_induce_union_of_common hfront htail
      (Or.inr hlastInner) hlastTail
    have hregion : L.rerouteRegion H I i =
        pathVertexSet E.headPath ∪ pathVertexSet (I.path ⟨i, hi⟩) ∪
          pathVertexSet E.tailPath := by
      simp only [rerouteRegion, dif_pos hi, E]
    rw [hregion]
    exact hall
  · have hregion : L.rerouteRegion H I i = pathVertexSet (L.path i) := by
      simp only [rerouteRegion, dif_neg hi]
    rw [hregion]
    exact (L.path i : G.Walk (P.start i) (P.finish i)).connected_induce_support

theorem rerouteRegion_start_mem
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {j : ℕ} {P : IndexedPairs (Fin j) V}
    (L : IndexedLinkage G P) (H : Finset V)
    {Q : IndexedPairs (L.HitIndex H) V} (I : IndexedLinkage G Q)
    (i : Fin j) : P.start i ∈ L.rerouteRegion H I i := by
  classical
  by_cases hi : ∃ y ∈ H, y ∈ pathVertexSet (L.path i)
  · simp only [rerouteRegion, dif_pos hi]
    exact Or.inl (Or.inl (pathVertexSet.start_mem _))
  · simpa only [rerouteRegion, dif_neg hi] using pathVertexSet.start_mem (L.path i)

theorem rerouteRegion_finish_mem
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {j : ℕ} {P : IndexedPairs (Fin j) V}
    (L : IndexedLinkage G P) (H : Finset V)
    {Q : IndexedPairs (L.HitIndex H) V} (I : IndexedLinkage G Q)
    (i : Fin j) : P.finish i ∈ L.rerouteRegion H I i := by
  classical
  by_cases hi : ∃ y ∈ H, y ∈ pathVertexSet (L.path i)
  · simp only [rerouteRegion, dif_pos hi]
    exact Or.inr (pathVertexSet.finish_mem _)
  · simpa only [rerouteRegion, dif_neg hi] using pathVertexSet.finish_mem (L.path i)


theorem rerouteRegion_disjoint
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {j : ℕ} {P : IndexedPairs (Fin j) V}
    (L : IndexedLinkage G P) (H : Finset V)
    {Q : IndexedPairs (L.HitIndex H) V} (I : IndexedLinkage G Q)
    (hI : I.vertices ⊆ (H : Set V))
    (hQstart : ∀ k, Q.start k = (L.exterior H k).first)
    (hQfinish : ∀ k, Q.finish k = (L.exterior H k).last)
    {i k : Fin j} (hik : i ≠ k) :
    Disjoint (L.rerouteRegion H I i) (L.rerouteRegion H I k) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxk
  by_cases hxH : x ∈ H
  · obtain ⟨hi, hxInnerI⟩ :=
      L.rerouteRegion_inside_inner H I hQstart hQfinish i hxi hxH
    obtain ⟨hk, hxInnerK⟩ :=
      L.rerouteRegion_inside_inner H I hQstart hQfinish k hxk hxH
    have hne : (⟨i, hi⟩ : L.HitIndex H) ≠ ⟨k, hk⟩ := by
      intro heq
      exact hik (congrArg Subtype.val heq)
    exact (Set.disjoint_left.mp (I.disjoint hne)) hxInnerI hxInnerK
  · exact (Set.disjoint_left.mp (L.disjoint hik))
      (L.rerouteRegion_outside_old H I hI i hxi hxH)
      (L.rerouteRegion_outside_old H I hI k hxk hxH)

/-- Once the child gives disjoint inner paths, each rerouting region
contains a replacement path and the replacement paths are disjoint. -/
theorem exists_rerouted_linkage
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {j : ℕ} {P : IndexedPairs (Fin j) V}
    (L : IndexedLinkage G P) (H : Finset V)
    {Q : IndexedPairs (L.HitIndex H) V} (I : IndexedLinkage G Q)
    (hI : I.vertices ⊆ (H : Set V))
    (hQstart : ∀ k, Q.start k = (L.exterior H k).first)
    (hQfinish : ∀ k, Q.finish k = (L.exterior H k).last) :
    ∃ L' : IndexedLinkage G P,
      ∀ i, pathVertexSet (L'.path i) ⊆ L.rerouteRegion H I i := by
  classical
  have hp (i : Fin j) :
      ∃ p : G.Path (P.start i) (P.finish i),
        pathVertexSet p ⊆ L.rerouteRegion H I i :=
    exists_path_in_connected_set (L.rerouteRegion H I i)
      (L.rerouteRegion_connected H I hQstart hQfinish i)
      (L.rerouteRegion_start_mem H I i)
      (L.rerouteRegion_finish_mem H I i)
  let p (i : Fin j) := Classical.choose (hp i)
  have hps (i : Fin j) : pathVertexSet (p i) ⊆ L.rerouteRegion H I i :=
    Classical.choose_spec (hp i)
  let L' : IndexedLinkage G P := {
    path := p
    disjoint := by
      intro i k hik
      exact Set.disjoint_of_subset (hps i) (hps k)
        (L.rerouteRegion_disjoint H I hI hQstart hQfinish hik)
  }
  exact ⟨L', hps⟩
end IndexedLinkage


/-- Model support commutes with an injective graph-homomorphism image. -/
theorem MinorModel.vertices_map
    {W V X : Type*} {H : SimpleGraph W} {G : SimpleGraph V}
    {J : SimpleGraph X} (M : MinorModel H G) (f : G →g J)
    (hf : Function.Injective f) :
    (M.map f hf).vertices = f '' M.vertices := by
  ext x
  simp only [MinorModel.vertices, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨i, y, hy, rfl⟩
    exact ⟨y, ⟨i, hy⟩, rfl⟩
  · rintro ⟨y, ⟨i, hy⟩, rfl⟩
    exact ⟨i, y, hy, rfl⟩

/-- Forgetting the induced-subgraph subtype maps every linkage vertex
to its original graph vertex. -/
theorem IndexedLinkage.vertices_mapInduce
    {ι V : Type*} {G : SimpleGraph V} {U : Set V}
    {P : IndexedPairs ι U} (L : IndexedLinkage (G.induce U) P) :
    L.mapInduce.vertices = Subtype.val '' L.vertices := by
  let E : (G.induce U) ↪g G := SimpleGraph.Embedding.induce U
  have hpath (i : ι) (v : V) :
      v ∈ pathVertexSet (L.mapInduce.path i) ↔
        ∃ x ∈ pathVertexSet (L.path i), (x : V) = v := by
    constructor
    · intro hv
      change v ∈ ((L.path i : (G.induce U).Walk (P.start i) (P.finish i)).map E.toHom).support at hv
      rw [SimpleGraph.Walk.support_map] at hv
      obtain ⟨x, hx, hxv⟩ := List.mem_map.mp hv
      exact ⟨x, hx, hxv⟩
    · rintro ⟨x, hx, hxv⟩
      change v ∈ ((L.path i : (G.induce U).Walk (P.start i) (P.finish i)).map E.toHom).support
      rw [SimpleGraph.Walk.support_map]
      exact List.mem_map.mpr ⟨x, hx, hxv⟩
  ext v
  constructor
  · intro hv
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
    obtain ⟨x, hx, rfl⟩ := (hpath i v).mp hi
    exact ⟨x, Set.mem_iUnion.mpr ⟨i, hx⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨i, (hpath i _).mpr ⟨x, hi, rfl⟩⟩

namespace IndexedLinkage

/-- The inner first/last hits are vertices of the old linkage. -/
theorem innerPairs_terminals_subset_vertices
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {j : ℕ} {P : IndexedPairs (Fin j) V}
    (L : IndexedLinkage G P) (H : Finset V) :
    (Subtype.val '' (L.innerPairs H).allTerminals) ⊆ L.vertices := by
  rintro x ⟨z, hz, rfl⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  apply L.path_subset_vertices i.1
  rcases hi with hi | hi
  · have hz : (z : V) = (L.exterior H i).first := congrArg Subtype.val hi
    rw [hz]
    exact (L.exterior H i).headPath_subset
      (pathVertexSet.finish_mem (L.exterior H i).headPath)
  · have hz : (z : V) = (L.exterior H i).last := congrArg Subtype.val hi
    rw [hz]
    exact (L.exterior H i).tailPath_subset
      (pathVertexSet.start_mem (L.exterior H i).tailPath)

/-- A model confined to H and meeting the inner linkage only at old
root/linkage vertices remains controlled after rerouting. -/
theorem exists_rerouted_linkage_controlled
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {a j : ℕ} {P : IndexedPairs (Fin j) V}
    (L : IndexedLinkage G P) (H : Finset V)
    (root : Fin a → V)
    (M : RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G root)
    {Q : IndexedPairs (L.HitIndex H) V} (I : IndexedLinkage G Q)
    (hM : M.toMinorModel.vertices ⊆ (H : Set V))
    (hI : I.vertices ⊆ (H : Set V))
    (hMI : M.toMinorModel.vertices ∩ I.vertices ⊆
      Set.range root ∩ L.vertices)
    (hQstart : ∀ k, Q.start k = (L.exterior H k).first)
    (hQfinish : ∀ k, Q.finish k = (L.exterior H k).last) :
    ∃ L' : IndexedLinkage G P,
      L'.vertices ⊆ L.vertices ∪ (H : Set V) ∧
      M.toMinorModel.vertices ∩ L'.vertices ⊆
        Set.range root ∩ L.vertices := by
  obtain ⟨L', hregion⟩ :=
    L.exists_rerouted_linkage H I hI hQstart hQfinish
  refine ⟨L', ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    have hxR := hregion i hxi
    by_cases hxH : x ∈ H
    · exact Or.inr hxH
    · exact Or.inl (L.rerouteRegion_outside_old H I hI i hxR hxH
        |> L.path_subset_vertices i)
  · rintro x ⟨hxM, hxL'⟩
    have hxH := hM hxM
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxL'
    obtain ⟨hi, hxInner⟩ :=
      L.rerouteRegion_inside_inner H I hQstart hQfinish i
        (hregion i hxi) hxH
    exact hMI ⟨hxM, I.path_subset_vertices ⟨i, hi⟩ hxInner⟩

end IndexedLinkage

namespace Woven

/-- Reroute an old linkage through a woven induced child. The replacement
uses only old linkage vertices and child vertices. The model meets the
replacement only at old linkage roots; every root that was an old
terminal still belongs to the intersection. -/
theorem reroute_linkage_through_child
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b j : ℕ} (H : Finset V)
    (hW : Woven (G.induce (H : Set V)) a b)
    (root : Fin a → V) (hroot : Function.Injective root)
    (hrootH : ∀ i, root i ∈ H)
    {P : IndexedPairs (Fin j) V} (L : IndexedLinkage G P)
    (hj : j ≤ b) :
    ∃ (M : RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G root)
      (L' : IndexedLinkage G P),
      M.toMinorModel.vertices ⊆ (H : Set V) ∧
      L'.vertices ⊆ L.vertices ∪ (H : Set V) ∧
      Set.range root ∩ P.allTerminals ⊆
        M.toMinorModel.vertices ∩ L'.vertices ∧
      M.toMinorModel.vertices ∩ L'.vertices ⊆
        Set.range root ∩ L.vertices := by
  classical
  let U : Set V := H
  let rU : Fin a → U := fun i => ⟨root i, hrootH i⟩
  have hrU : Function.Injective rU := by
    intro i k h
    exact hroot (congrArg Subtype.val h)
  letI : Fintype (L.HitIndex H) := Subtype.fintype _
  have hsub : Fintype.card (L.HitIndex H) ≤ Fintype.card (Fin j) :=
    Fintype.card_le_of_injective (fun i : L.HitIndex H => i.1)
      Subtype.val_injective
  have hcard : Fintype.card (L.HitIndex H) ≤ b := by
    simpa using hsub.trans (by simpa using hj)
  obtain ⟨Q, MU, IU, hQstart, hQfinish, hExact⟩ :=
    hW.for_fintype_index rU hrU (L.innerPairs H)
      (L.innerPairs_disjointTerminals H) hcard
  let E : (G.induce U) ↪g G := SimpleGraph.Embedding.induce U
  let I : IndexedLinkage G
      ⟨fun i => (Q.start i : V), fun i => (Q.finish i : V)⟩ :=
    IU.mapInduce
  let M : RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G root := by
    simpa [rU, E, Function.comp_def] using
      (MU.map E.toHom Subtype.coe_injective)
  have hMvertices : M.toMinorModel.vertices =
      Subtype.val '' MU.toMinorModel.vertices := by
    change (MU.toMinorModel.map E.toHom Subtype.coe_injective).vertices =
      Subtype.val '' MU.toMinorModel.vertices
    rw [MinorModel.vertices_map]
    rfl
  have hIvertices : I.vertices = Subtype.val '' IU.vertices := by
    exact IndexedLinkage.vertices_mapInduce IU
  have hM : M.toMinorModel.vertices ⊆ (H : Set V) := by
    rw [hMvertices]
    rintro x ⟨u, _, rfl⟩
    exact u.property
  have hI : I.vertices ⊆ (H : Set V) := by
    rw [hIvertices]
    rintro x ⟨u, _, rfl⟩
    exact u.property
  have hMI : M.toMinorModel.vertices ∩ I.vertices ⊆
      Set.range root ∩ L.vertices := by
    rintro x ⟨hxM, hxI⟩
    rw [hMvertices] at hxM
    rw [hIvertices] at hxI
    obtain ⟨u, huM, rfl⟩ := hxM
    obtain ⟨v, hvI, hv⟩ := hxI
    have huv : v = u := Subtype.coe_injective hv
    subst v
    have hu : u ∈ MU.toMinorModel.vertices ∩ IU.vertices := ⟨huM, hvI⟩
    rw [hExact] at hu
    obtain ⟨huRoot, huTerm⟩ := hu
    obtain ⟨k, hk⟩ := huRoot
    refine ⟨⟨k, ?_⟩, ?_⟩
    · exact congrArg Subtype.val hk
    · exact L.innerPairs_terminals_subset_vertices H ⟨u, huTerm, rfl⟩
  have hQstart' : ∀ k,
      (⟨fun i => (Q.start i : V), fun i => (Q.finish i : V)⟩ :
        IndexedPairs (L.HitIndex H) V).start k =
        (L.exterior H k).first := by
    intro k
    change (Q.start k : V) = (L.exterior H k).first
    rw [hQstart k]
    rfl
  have hQfinish' : ∀ k,
      (⟨fun i => (Q.start i : V), fun i => (Q.finish i : V)⟩ :
        IndexedPairs (L.HitIndex H) V).finish k =
        (L.exterior H k).last := by
    intro k
    change (Q.finish k : V) = (L.exterior H k).last
    rw [hQfinish k]
    rfl
  obtain ⟨L', hsupp, hinter⟩ :=
    L.exists_rerouted_linkage_controlled H root M I
      hM hI hMI hQstart' hQfinish'
  refine ⟨M, L', hM, hsupp, ?_, hinter⟩
  rintro x ⟨⟨i, rfl⟩, hxTerm⟩
  refine ⟨Set.mem_iUnion.mpr ⟨i, M.root_mem i⟩, ?_⟩
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hxTerm
  exact L'.path_subset_vertices k (L'.terminal_subset_path k hk)

/-- If every root is an old terminal, the rerouted model and linkage
intersect exactly in the root set. -/
theorem reroute_linkage_through_child_exact
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b j : ℕ} (H : Finset V)
    (hW : Woven (G.induce (H : Set V)) a b)
    (root : Fin a → V) (hroot : Function.Injective root)
    (hrootH : ∀ i, root i ∈ H)
    {P : IndexedPairs (Fin j) V} (L : IndexedLinkage G P)
    (hj : j ≤ b)
    (hroots_terminal : Set.range root ⊆ P.allTerminals) :
    ∃ (M : RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G root)
      (L' : IndexedLinkage G P),
      M.toMinorModel.vertices ⊆ (H : Set V) ∧
      L'.vertices ⊆ L.vertices ∪ (H : Set V) ∧
      M.toMinorModel.vertices ∩ L'.vertices = Set.range root := by
  obtain ⟨M, L', hM, hsupp, hlo, hhi⟩ :=
    reroute_linkage_through_child H hW root hroot hrootH L hj
  refine ⟨M, L', hM, hsupp, ?_⟩
  apply Set.Subset.antisymm
  · exact hhi.trans Set.inter_subset_left
  · intro x hx
    exact hlo ⟨hx, hroots_terminal hx⟩

end Woven
end HadwigerLean