import HadwigerLean.Woven.DoubleFanIndex
import Mathlib.Tactic

/-!
# Collapsing a full clone linkage to source-rooted paths
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every clone on a saturated disjoint path is its own start:
all other clones start another disjoint path. -/
theorem doubleClone_path_only_own_clone
    (G : SimpleGraph V) (Z H : Finset V)
    (hdis : Disjoint Z H)
    (P : IndexedPairs (Fin (2 * Z.card))
      (DoubleCloneVertex V Z))
    (L : IndexedLinkage (doubleCloneGraph G Z) P)
    (hAB : SetMenger.IsABLinkage L
      (doubleCloneSources Z) (doubleCloneTargets Z H hdis))
    (j : Fin (2 * Z.card))
    (c : DoubleCloneVertex V Z)
    (hc : c ∈ pathVertexSet (L.path j))
    (hcA : c ∈ doubleCloneSources Z) :
    c = P.start j := by
  obtain ⟨l,hl⟩ :=
    doubleClone_start_surjective G Z H hdis P L hAB c hcA
  by_cases hlj : l = j
  · simpa [hlj] using hl.symm
  · have hcl : c ∈ pathVertexSet (L.path l) := by
      rw [← hl]
      exact pathVertexSet.start_mem (L.path l)
    exact False.elim
      ((Set.disjoint_left.mp (L.disjoint (Ne.symm hlj))) hc hcl)

/-- On each saturated clone path, collapsing copies is injective on
the path's support. -/
theorem doubleClone_collapse_injOn_path
    (G : SimpleGraph V) (Z H : Finset V)
    (hdis : Disjoint Z H)
    (P : IndexedPairs (Fin (2 * Z.card))
      (DoubleCloneVertex V Z))
    (L : IndexedLinkage (doubleCloneGraph G Z) P)
    (hAB : SetMenger.IsABLinkage L
      (doubleCloneSources Z) (doubleCloneTargets Z H hdis))
    (j : Fin (2 * Z.card)) :
    ∀ x ∈ pathVertexSet (L.path j),
      ∀ y ∈ pathVertexSet (L.path j),
        doubleCloneCollapse Z x = doubleCloneCollapse Z y →
          x = y := by
  intro x hx y hy hxy
  cases x with
  | inl u =>
    cases y with
    | inl v =>
      exact congrArg Sum.inl (Subtype.ext hxy)
    | inr slot =>
      have hval : u.1 = slot.1.1 := hxy
      exact False.elim (u.2 (hval.symm ▸ slot.1.2))
  | inr slot =>
    cases y with
    | inl v =>
      have hval : slot.1.1 = v.1 := hxy
      exact False.elim (v.2 (hval ▸ slot.1.2))
    | inr t =>
      have hxA : (Sum.inr slot : DoubleCloneVertex V Z) ∈
          doubleCloneSources Z := by
        exact doubleClone_mem_sources Z slot.1 slot.2
      have hyA : (Sum.inr t : DoubleCloneVertex V Z) ∈
          doubleCloneSources Z := by
        exact doubleClone_mem_sources Z t.1 t.2
      have hxstart :=
        doubleClone_path_only_own_clone G Z H hdis P L hAB j
          (.inr slot) hx hxA
      have hystart :=
        doubleClone_path_only_own_clone G Z H hdis P L hAB j
          (.inr t) hy hyA
      exact hxstart.trans hystart.symm

/-- A saturated clone path remains a simple path after collapsing
its private clone to the original source vertex. -/
def collapseClonePath
    (G : SimpleGraph V) (Z H : Finset V)
    (hdis : Disjoint Z H)
    (P : IndexedPairs (Fin (2 * Z.card))
      (DoubleCloneVertex V Z))
    (L : IndexedLinkage (doubleCloneGraph G Z) P)
    (hAB : SetMenger.IsABLinkage L
      (doubleCloneSources Z) (doubleCloneTargets Z H hdis))
    (j : Fin (2 * Z.card)) :
    G.Path (doubleCloneCollapse Z (P.start j))
      (doubleCloneCollapse Z (P.finish j)) := by
  let w : G.Walk (doubleCloneCollapse Z (P.start j))
      (doubleCloneCollapse Z (P.finish j)) :=
    (L.path j : (doubleCloneGraph G Z).Walk
      (P.start j) (P.finish j)).map (doubleCloneCollapseHom G Z)
  refine ⟨w, ?_⟩
  rw [SimpleGraph.Walk.isPath_def]
  change (w.support).Nodup
  change (((L.path j : (doubleCloneGraph G Z).Path
    (P.start j) (P.finish j)).1.map
      (doubleCloneCollapseHom G Z)).support).Nodup
  rw [SimpleGraph.Walk.support_map]
  have hp : (L.path j : (doubleCloneGraph G Z).Walk
      (P.start j) (P.finish j)).support.Nodup := by
    simpa [SimpleGraph.Walk.isPath_def] using (L.path j).property
  apply hp.map_on
  exact doubleClone_collapse_injOn_path G Z H hdis P L hAB j


/-- Support membership after collapsing a clone path is exactly the
image of its clone support. -/
theorem mem_collapseClonePath_iff
    (G : SimpleGraph V) (Z H : Finset V)
    (hdis : Disjoint Z H)
    (P : IndexedPairs (Fin (2 * Z.card))
      (DoubleCloneVertex V Z))
    (L : IndexedLinkage (doubleCloneGraph G Z) P)
    (hAB : SetMenger.IsABLinkage L
      (doubleCloneSources Z) (doubleCloneTargets Z H hdis))
    (j : Fin (2 * Z.card)) (v : V) :
    v ∈ pathVertexSet (collapseClonePath G Z H hdis P L hAB j) ↔
      ∃ c ∈ pathVertexSet (L.path j), doubleCloneCollapse Z c = v := by
  simp [pathVertexSet, collapseClonePath, doubleCloneCollapseHom,
    SimpleGraph.Walk.support_map, List.mem_map]

/-- Two collapsed clone paths can meet only at original cloned
sources, because every exterior vertex has one private copy. -/
theorem collapseClonePath_disjoint_outside
    (G : SimpleGraph V) (Z H : Finset V)
    (hdis : Disjoint Z H)
    (P : IndexedPairs (Fin (2 * Z.card))
      (DoubleCloneVertex V Z))
    (L : IndexedLinkage (doubleCloneGraph G Z) P)
    (hAB : SetMenger.IsABLinkage L
      (doubleCloneSources Z) (doubleCloneTargets Z H hdis))
    (j l : Fin (2 * Z.card)) (hjl : j ≠ l) :
    Disjoint
      (pathVertexSet (collapseClonePath G Z H hdis P L hAB j) \ (Z : Set V))
      (pathVertexSet (collapseClonePath G Z H hdis P L hAB l) \ (Z : Set V)) := by
  apply Set.disjoint_left.mpr
  intro v hvj hvl
  obtain ⟨cj,hcj,hcjv⟩ :=
    (mem_collapseClonePath_iff G Z H hdis P L hAB j v).mp hvj.1
  obtain ⟨cl,hcl,hclv⟩ :=
    (mem_collapseClonePath_iff G Z H hdis P L hAB l v).mp hvl.1
  have hrepj : cj = doubleCloneTarget Z v hvj.2 := by
    cases cj with
    | inl x =>
      apply congrArg Sum.inl
      exact Subtype.ext hcjv
    | inr slot =>
      have hval : slot.1.1 = v := hcjv
      exact False.elim (hvj.2 (hval ▸ slot.1.2))
  have hrepl : cl = doubleCloneTarget Z v hvj.2 := by
    cases cl with
    | inl x =>
      apply congrArg Sum.inl
      exact Subtype.ext hclv
    | inr slot =>
      have hval : slot.1.1 = v := hclv
      exact False.elim (hvj.2 (hval ▸ slot.1.2))
  have heq : cj = cl := hrepj.trans hrepl.symm
  exact (Set.disjoint_left.mp (L.disjoint hjl))
    hcj (heq.symm ▸ hcl)

/-- A collapsed path meets the cloned source set only at its
own source vertex. -/
theorem collapseClonePath_source_only
    (G : SimpleGraph V) (Z H : Finset V)
    (hdis : Disjoint Z H)
    (P : IndexedPairs (Fin (2 * Z.card))
      (DoubleCloneVertex V Z))
    (L : IndexedLinkage (doubleCloneGraph G Z) P)
    (hAB : SetMenger.IsABLinkage L
      (doubleCloneSources Z) (doubleCloneTargets Z H hdis))
    (j : Fin (2 * Z.card)) (v : V)
    (hv : v ∈ pathVertexSet (collapseClonePath G Z H hdis P L hAB j))
    (hvZ : v ∈ Z) :
    v = doubleCloneCollapse Z (P.start j) := by
  obtain ⟨c,hc,hcv⟩ :=
    (mem_collapseClonePath_iff G Z H hdis P L hAB j v).mp hv
  cases c with
  | inl x =>
    have hval : x.1 = v := hcv
    exact False.elim (x.2 (hval.symm ▸ hvZ))
  | inr slot =>
    have hcA : (Sum.inr slot : DoubleCloneVertex V Z) ∈
        doubleCloneSources Z :=
      doubleClone_mem_sources Z slot.1 slot.2
    have hown :=
      doubleClone_path_only_own_clone G Z H hdis P L hAB j
        (.inr slot) hc hcA
    exact hcv.symm.trans (congrArg (doubleCloneCollapse Z) hown)

/-- The end of each clone-to-hub Menger path collapses to an
original vertex in the hub. -/
theorem doubleClone_finish_mem_hub
    (G : SimpleGraph V) (Z H : Finset V)
    (hdis : Disjoint Z H)
    (P : IndexedPairs (Fin (2 * Z.card))
      (DoubleCloneVertex V Z))
    (L : IndexedLinkage (doubleCloneGraph G Z) P)
    (hAB : SetMenger.IsABLinkage L
      (doubleCloneSources Z) (doubleCloneTargets Z H hdis))
    (j : Fin (2 * Z.card)) :
    doubleCloneCollapse Z (P.finish j) ∈ H := by
  classical
  have hmem := hAB.2 j
  unfold doubleCloneTargets at hmem
  obtain ⟨h,hh,heq⟩ := Finset.mem_image.mp hmem
  have hv : doubleCloneCollapse Z (P.finish j) = h.1 := by
    rw [← heq]
    rfl
  exact hv ▸ h.2
end Woven
end HadwigerLean
