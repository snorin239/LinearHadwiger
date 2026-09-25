import HadwigerLean.Graph.Linkedness.CoreTransfer
import HadwigerLean.Graph.Linkedness.CoreFanFinal
import HadwigerLean.Graph.RootedCliqueMinor
import Mathlib.Tactic

namespace HadwigerLean
namespace Linkedness

noncomputable def IndexedPairs.reverse {ι V : Type*} (P : IndexedPairs ι V) : IndexedPairs ι V :=
  ⟨P.finish, P.start⟩

private theorem pathVertexSet_reverse {V : Type*} {G : SimpleGraph V}
    {s t : V} (p : G.Path s t) :
    pathVertexSet p.reverse = pathVertexSet p := by
  ext x
  simp [pathVertexSet, SimpleGraph.Path.reverse, SimpleGraph.Walk.support_reverse]

noncomputable def IndexedLinkage.reverse {ι V : Type*} {G : SimpleGraph V}
    {P : IndexedPairs ι V} (L : IndexedLinkage G P) :
    IndexedLinkage G (IndexedPairs.reverse P) where
  path := fun i => (L.path i).reverse
  disjoint := by
    intro i j hij
    change Disjoint (pathVertexSet (L.path i).reverse) (pathVertexSet (L.path j).reverse)
    rw [pathVertexSet_reverse (L.path i), pathVertexSet_reverse (L.path j)]
    exact L.disjoint hij


/-- Trim a path at its first vertex in a set, given any hit. -/
theorem FirstHit.exists_of_hit
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {s t : V}
    (p : G.Path s t) (J : Finset V)
    (hhit : ∃ x ∈ J, x ∈ pathVertexSet p) :
    Nonempty (FirstHit p J) := by
  classical
  let w : G.Walk s t := p
  have hnon : {x ∈ J | x ∈ w.support}.Nonempty := by
    obtain ⟨x, hxJ, hxP⟩ := hhit
    exact ⟨x, Finset.mem_filter.mpr ⟨hxJ, hxP⟩⟩
  obtain ⟨u, huJ, huW, hfirst⟩ :=
    w.exists_mem_support_forall_mem_support_imp_eq J hnon
  let q : G.Path s u := ⟨w.takeUntil u huW, p.property.takeUntil huW⟩
  exact ⟨{
    finish := u
    finish_mem := huJ
    path := q
    path_subset := by
      intro x hx
      exact w.support_takeUntil_subset_support huW hx
    unique_hit := by
      intro x hx hxJ
      exact hfirst x hxJ hx
  }⟩

/-- Trim a disjoint family at first hits, allowing the old finishes to lie outside the hit set. -/
theorem IndexedLinkage.trim_to_first_hit_of_hit
    {ι V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {P : IndexedPairs ι V}
    (L : IndexedLinkage G P) (J : Finset V)
    (hhit : ∀ i, ∃ x ∈ J, x ∈ pathVertexSet (L.path i)) :
    ∃ (P' : IndexedPairs ι V) (L' : IndexedLinkage G P'),
      (∀ i, P'.start i = P.start i) ∧
      (∀ i, P'.finish i ∈ J) ∧
      (∀ i x, x ∈ pathVertexSet (L'.path i) → x ∈ J → x = P'.finish i) ∧
      (∀ i, pathVertexSet (L'.path i) ⊆ pathVertexSet (L.path i)) := by
  classical
  let F (i : ι) : FirstHit (L.path i) J :=
    Classical.choice (FirstHit.exists_of_hit (L.path i) J (hhit i))
  let P' : IndexedPairs ι V := ⟨P.start, fun i => (F i).finish⟩
  let L' : IndexedLinkage G P' := {
    path := fun i => (F i).path
    disjoint := by
      intro i j hij
      exact Set.disjoint_of_subset (F i).path_subset (F j).path_subset (L.disjoint hij)
  }
  exact ⟨P', L', (fun _ => rfl), (fun i => (F i).finish_mem),
    (fun i x hx hxJ => (F i).unique_hit x hx hxJ),
    (fun i => (F i).path_subset)⟩

/-- Restrict a linkage whose paths all lie in a vertex set to the induced graph. -/
noncomputable def IndexedLinkage.induce
    {ι V : Type*} {G : SimpleGraph V} {P : IndexedPairs ι V}
    (L : IndexedLinkage G P) (U : Set V)
    (hU : ∀ i x, x ∈ pathVertexSet (L.path i) → x ∈ U) :
    IndexedLinkage (G.induce U)
      ⟨(fun i => ⟨P.start i, hU i _ (pathVertexSet.start_mem (L.path i))⟩),
       (fun i => ⟨P.finish i, hU i _ (pathVertexSet.finish_mem (L.path i))⟩)⟩ where
  path := by
    intro i
    let w : G.Walk (P.start i) (P.finish i) := L.path i
    let hwi : ∀ x ∈ w.support, x ∈ U := hU i
    refine ⟨w.induce U hwi, ?_⟩
    apply (SimpleGraph.Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce U).toHom))
    rw [SimpleGraph.Walk.map_induce]
    exact (L.path i).property
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hxi' : (x : V) ∈ pathVertexSet (L.path i) := by
      change x ∈ (SimpleGraph.Walk.induce U (L.path i : G.Walk (P.start i) (P.finish i)) (hU i)).support at hxi
      rw [SimpleGraph.Walk.support_induce] at hxi
      exact (List.mem_attachWith (hU i) x).mp hxi
    have hxj' : (x : V) ∈ pathVertexSet (L.path j) := by
      change x ∈ (SimpleGraph.Walk.induce U (L.path j : G.Walk (P.start j) (P.finish j)) (hU j)).support at hxj
      rw [SimpleGraph.Walk.support_induce] at hxj
      exact (List.mem_attachWith (hU j) x).mp hxj
    exact (Set.disjoint_left.mp (L.disjoint hij)) hxi' hxj'

/-- A saturated separator can send every boundary vertex to a distant core
through paths wholly contained in the far side. -/
theorem boundary_core_fan_in_right
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    (J : Finset V) (hJright : ∀ x ∈ J, x ∈ S.right)
    {q : ℕ} (P : IndexedPairs (Fin q) V) (L : IndexedLinkage G P)
    (hfinish : ∀ i, P.finish i ∈ J)
    (hhit : ∀ i, ∃ x ∈ S.separatorFinset,
      x ∈ pathVertexSet (L.path i))
    (hcard : S.separatorFinset.card = q) :
    ∃ (C : IndexedPairs (Fin q) V) (F : IndexedLinkage G C),
      (Finset.univ.image C.start = S.separatorFinset) ∧
      (∀ i, C.finish i ∈ J) ∧
      (∀ i x, x ∈ pathVertexSet (F.path i) → x ∈ S.right) ∧
      (∀ i x, x ∈ pathVertexSet (F.path i) → x ∈ J → x = C.finish i) := by
  classical
  let R := IndexedLinkage.reverse L
  have hhitR : ∀ i, ∃ x ∈ S.separatorFinset,
      x ∈ pathVertexSet (R.path i) := by
    intro i
    obtain ⟨x,hxQ,hxL⟩ := hhit i
    exact ⟨x,hxQ,(pathVertexSet_reverse (L.path i)).symm ▸ hxL⟩
  obtain ⟨P',L',hstart',hfinish',hfirst',hsubset'⟩ :=
    IndexedLinkage.trim_to_first_hit_of_hit R S.separatorFinset hhitR
  have hright : ∀ i x, x ∈ pathVertexSet (L'.path i) → x ∈ S.right := by
    intro i x hx
    have hboundary : ∀ y ∈ (L'.path i : G.Walk (P'.start i) (P'.finish i)).support,
        y ∈ S.symm.separator → y = P'.finish i := by
      intro y hy hyQ
      exact hfirst' i y hy ((S.mem_separatorFinset y).mpr ⟨hyQ.2, hyQ.1⟩)
    exact S.symm.path_support_subset_left_of_boundary_only_at_finish
      (L'.path i : G.Walk (P'.start i) (P'.finish i))
      (L'.path i).property (hJright (P'.start i) (hstart' i ▸ hfinish i))
      hboundary x hx
  have hstarts : Finset.univ.image P'.finish = S.separatorFinset := by
    have hsub : Finset.univ.image P'.finish ⊆ S.separatorFinset := by
      intro x hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact hfinish' i
    apply Finset.eq_of_subset_of_card_le hsub
    have hc : (Finset.univ.image P'.finish).card = q := by
      simp [Finset.card_image_of_injective _ L'.finish_injective]
    omega
  let C0 := IndexedPairs.reverse P'
  let F0 := IndexedLinkage.reverse L'
  have hF0right : ∀ i x, x ∈ pathVertexSet (F0.path i) → x ∈ S.right := by
    intro i x hx
    exact hright i x ((pathVertexSet_reverse (L'.path i)).symm ▸ hx)
  have hF0finish : ∀ i, C0.finish i ∈ J := by
    intro i
    change P'.start i ∈ J
    rw [hstart' i]
    exact hfinish i
  obtain ⟨C,F,hstartC,hfinishC,hfirstC,hsubsetC⟩ :=
    IndexedLinkage.trim_to_first_hit F0 J hF0finish
  refine ⟨C,F,?_,hfinishC,?_,hfirstC⟩
  · calc
      Finset.univ.image C.start = Finset.univ.image C0.start := by
        apply Finset.image_congr
        intro i hi
        exact hstartC i
      _ = S.separatorFinset := hstarts
  · intro i x hx
    exact hF0right i x (hsubsetC i hx)

@[simp] theorem IndexedLinkage.mem_induce_pathVertexSet_iff
    {ι V : Type*} {G : SimpleGraph V} {P : IndexedPairs ι V}
    (L : IndexedLinkage G P) (U : Set V)
    (hU : ∀ i x, x ∈ pathVertexSet (L.path i) → x ∈ U)
    (i : ι) (x : U) :
    x ∈ pathVertexSet ((IndexedLinkage.induce L U hU).path i) ↔
      (x : V) ∈ pathVertexSet (L.path i) := by
  simp [IndexedLinkage.induce, pathVertexSet, SimpleGraph.Walk.support_induce,
    List.mem_attachWith]
end Linkedness
end HadwigerLean
