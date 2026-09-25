import HadwigerLean.Woven.HubRouting

import Mathlib.Tactic

/-!
# Splicing disjoint incoming paths through a hub

A clean incoming linkage meets the hub only at its distinct finishes.
A rooted hub routing pairs those finishes without using any other arrival
internally. The two incoming paths and their hub route can therefore be
concatenated for each pair, with disjoint supports across different pairs.
-/

namespace HadwigerLean
namespace Woven

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
  {G : SimpleGraph V} {P : IndexedPairs ι V} {H : Finset V} {m : ℕ}

/-- Endpoint pairs before adjoining the hub routes. -/
def hubSplicedPairs (P : IndexedPairs ι V)
    (slot : Fin m × Fin 2 ≃ ι) : IndexedPairs (Fin m) V where
  start := fun k => P.start (slot (k,0))
  finish := fun k => P.start (slot (k,1))

/-- The three support pieces of a path spliced through the hub. -/
def hubSplicedSupport (N : IndexedLinkage G P)
    (slot : Fin m × Fin 2 ≃ ι)
    (J : IndexedLinkage G (hubArrivalPairs P.finish slot))
    (k : Fin m) : Set V :=
  pathVertexSet (N.path (slot (k,0))) ∪
    pathVertexSet (J.path k) ∪
    pathVertexSet (N.path (slot (k,1)))

private theorem slot_ne_of_pair_ne (slot : Fin m × Fin 2 ≃ ι)
    {k l : Fin m} (hkl : k ≠ l) (b c : Fin 2) :
    slot (k,b) ≠ slot (l,c) := by
  intro h
  exact hkl (congrArg Prod.fst (slot.injective h))

/-- An incoming path is disjoint from a hub route to which its arrival
was not assigned. -/
theorem incoming_disjoint_hub_route
    (N : IndexedLinkage G P)
    (slot : Fin m × Fin 2 ≃ ι)
    (J : IndexedLinkage G (hubArrivalPairs P.finish slot))
    (hfinj : Function.Injective P.finish)
    (hNhub : ∀ i v, v ∈ pathVertexSet (N.path i) →
      v ∈ H → v = P.finish i)
    (hJhub : ∀ k, pathVertexSet (J.path k) ⊆ (H : Set V))
    (hJavoid : Linkedness.InteriorsAvoid J (hubArrivals P.finish))
    (i : ι) (k : Fin m)
    (hi0 : i ≠ slot (k,0)) (hi1 : i ≠ slot (k,1)) :
    Disjoint (pathVertexSet (N.path i)) (pathVertexSet (J.path k)) := by
  apply Set.disjoint_left.mpr
  intro v hvN hvJ
  have hvH := hJhub k hvJ
  have hvi : v = P.finish i := hNhub i v hvN hvH
  have hvX : v ∈ hubArrivals P.finish := by
    rw [hvi]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hvterm := hJavoid k v hvJ hvX
  rcases hvterm with hv0 | hv1
  · have hi : i = slot (k,0) :=
      hfinj (by simpa [hubArrivalPairs] using hvi.symm.trans hv0)
    exact hi0 hi
  · have hi : i = slot (k,1) :=
      hfinj (by simpa [hubArrivalPairs] using hvi.symm.trans hv1)
    exact hi1 hi

/-- Different matched pairs use disjoint total support, including their
incoming paths and hub routes. -/
theorem hubSplicedSupport_disjoint
    (N : IndexedLinkage G P)
    (slot : Fin m × Fin 2 ≃ ι)
    (J : IndexedLinkage G (hubArrivalPairs P.finish slot))
    (hfinj : Function.Injective P.finish)
    (hNhub : ∀ i v, v ∈ pathVertexSet (N.path i) →
      v ∈ H → v = P.finish i)
    (hJhub : ∀ k, pathVertexSet (J.path k) ⊆ (H : Set V))
    (hJavoid : Linkedness.InteriorsAvoid J (hubArrivals P.finish))
    {k l : Fin m} (hkl : k ≠ l) :
    Disjoint (hubSplicedSupport N slot J k)
      (hubSplicedSupport N slot J l) := by
  apply Set.disjoint_left.mpr
  intro v hvk hvl
  have hNN (b c : Fin 2) :
      Disjoint (pathVertexSet (N.path (slot (k,b))))
        (pathVertexSet (N.path (slot (l,c)))) :=
    N.disjoint (slot_ne_of_pair_ne slot hkl b c)
  have hNJ (b : Fin 2) :
      Disjoint (pathVertexSet (N.path (slot (k,b))))
        (pathVertexSet (J.path l)) :=
    incoming_disjoint_hub_route N slot J hfinj hNhub hJhub hJavoid
      (slot (k,b)) l
      (slot_ne_of_pair_ne slot hkl b 0)
      (slot_ne_of_pair_ne slot hkl b 1)
  have hJN (c : Fin 2) :
      Disjoint (pathVertexSet (J.path k))
        (pathVertexSet (N.path (slot (l,c)))) := by
    exact (incoming_disjoint_hub_route N slot J hfinj hNhub hJhub hJavoid
      (slot (l,c)) k
      (slot_ne_of_pair_ne slot hkl.symm c 0)
      (slot_ne_of_pair_ne slot hkl.symm c 1)).symm
  change v ∈ (pathVertexSet (N.path (slot (k,0))) ∪
      pathVertexSet (J.path k)) ∪
      pathVertexSet (N.path (slot (k,1))) at hvk
  change v ∈ (pathVertexSet (N.path (slot (l,0))) ∪
      pathVertexSet (J.path l)) ∪
      pathVertexSet (N.path (slot (l,1))) at hvl
  rcases hvk with (hvk0 | hvkJ) | hvk1 <;>
    rcases hvl with (hvl0 | hvlJ) | hvl1
  · exact (Set.disjoint_left.mp (hNN 0 0)) hvk0 hvl0
  · exact (Set.disjoint_left.mp (hNJ 0)) hvk0 hvlJ
  · exact (Set.disjoint_left.mp (hNN 0 1)) hvk0 hvl1
  · exact (Set.disjoint_left.mp (hJN 0)) hvkJ hvl0
  · exact (Set.disjoint_left.mp (J.disjoint hkl)) hvkJ hvlJ
  · exact (Set.disjoint_left.mp (hJN 1)) hvkJ hvl1
  · exact (Set.disjoint_left.mp (hNN 1 0)) hvk1 hvl0
  · exact (Set.disjoint_left.mp (hNJ 1)) hvk1 hvlJ
  · exact (Set.disjoint_left.mp (hNN 1 1)) hvk1 hvl1


/-- Walk obtained by coming into the hub, traversing its route, then
following the second incoming path backward. -/
def hubSpliceWalk
    (N : IndexedLinkage G P)
    (slot : Fin m × Fin 2 ≃ ι)
    (J : IndexedLinkage G (hubArrivalPairs P.finish slot))
    (k : Fin m) :
    G.Walk (P.start (slot (k,0))) (P.start (slot (k,1))) := by
  let p : G.Walk (P.start (slot (k,0))) (P.finish (slot (k,0))) :=
    (N.path (slot (k,0))).1
  let q : G.Walk (P.finish (slot (k,0))) (P.finish (slot (k,1))) :=
    (J.path k).1.copy rfl rfl
  let r : G.Walk (P.finish (slot (k,1))) (P.start (slot (k,1))) :=
    ((N.path (slot (k,1))).reverse).1
  exact p.append (q.append r)

/-- A simple path extracted from the three-piece hub walk. -/
noncomputable def hubSplicePath
    (N : IndexedLinkage G P)
    (slot : Fin m × Fin 2 ≃ ι)
    (J : IndexedLinkage G (hubArrivalPairs P.finish slot))
    (k : Fin m) :
    G.Path (P.start (slot (k,0))) (P.start (slot (k,1))) :=
  (hubSpliceWalk N slot J k).toPath

/-- Shortening the three-piece walk cannot add support vertices. -/
theorem hubSplicePath_support_subset
    (N : IndexedLinkage G P)
    (slot : Fin m × Fin 2 ≃ ι)
    (J : IndexedLinkage G (hubArrivalPairs P.finish slot))
    (k : Fin m) :
    pathVertexSet (hubSplicePath N slot J k) ⊆
      hubSplicedSupport N slot J k := by
  intro v hv
  have hw : v ∈ (hubSpliceWalk N slot J k).support :=
    (hubSpliceWalk N slot J k).support_toPath_subset_support hv
  simp only [hubSpliceWalk, SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_reverse] at hw
  simpa [hubSplicedSupport, pathVertexSet, or_assoc] using hw

/-- Splicing through the hub yields disjoint paths between the paired
outside starts. -/
noncomputable def hubSpliceLinkage
    (N : IndexedLinkage G P)
    (slot : Fin m × Fin 2 ≃ ι)
    (J : IndexedLinkage G (hubArrivalPairs P.finish slot))
    (hfinj : Function.Injective P.finish)
    (hNhub : ∀ i v, v ∈ pathVertexSet (N.path i) →
      v ∈ H → v = P.finish i)
    (hJhub : ∀ k, pathVertexSet (J.path k) ⊆ (H : Set V))
    (hJavoid : Linkedness.InteriorsAvoid J (hubArrivals P.finish)) :
    IndexedLinkage G (hubSplicedPairs P slot) where
  path := hubSplicePath N slot J
  disjoint := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro v hvk hvl
    exact (Set.disjoint_left.mp
      (hubSplicedSupport_disjoint N slot J hfinj hNhub hJhub hJavoid hkl))
      (hubSplicePath_support_subset N slot J k hvk)
      (hubSplicePath_support_subset N slot J l hvl)

/-- Every spliced path stays within its two incoming paths and one hub
route. -/
theorem hubSpliceLinkage_support_subset
    (N : IndexedLinkage G P)
    (slot : Fin m × Fin 2 ≃ ι)
    (J : IndexedLinkage G (hubArrivalPairs P.finish slot))
    (hfinj : Function.Injective P.finish)
    (hNhub : ∀ i v, v ∈ pathVertexSet (N.path i) →
      v ∈ H → v = P.finish i)
    (hJhub : ∀ k, pathVertexSet (J.path k) ⊆ (H : Set V))
    (hJavoid : Linkedness.InteriorsAvoid J (hubArrivals P.finish))
    (k : Fin m) :
    pathVertexSet ((hubSpliceLinkage N slot J hfinj hNhub hJhub hJavoid).path k) ⊆
      hubSplicedSupport N slot J k :=
  hubSplicePath_support_subset N slot J k
end Woven
end HadwigerLean
