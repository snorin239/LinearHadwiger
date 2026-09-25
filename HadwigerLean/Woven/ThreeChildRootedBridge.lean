import HadwigerLean.Woven.ThreeChildLinkage

/-!
# Linked-complement bridge for the three woven children

The parent roots have two distinct neighbors each. After those roots are
deleted, a `2a`-linked graph connects the neighbors to one selected root
in every child branch. The existing three-child assembly then yields a
rooted `K_a` model at the parent roots.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The geometric three-child step, with prescribed connectors supplied by
linkedness after deleting the parent roots. -/
theorem rooted_minor_of_three_woven_children_linked_complement
    (G : SimpleGraph V) {a c b : ℕ}
    (H : Fin 3 → Finset V)
    (hH : Pairwise fun k l : Fin 3 =>
      Disjoint (H k : Set V) (H l : Set V))
    (hW : ∀ k, Woven (G.induce (H k : Set V)) c b)
    (root : Fin a → V) (hroot : Function.Injective root)
    (childRoot : Fin 3 → Fin c → V)
    (hchildRoot : ∀ k, Function.Injective (childRoot k))
    (hchildRootH : ∀ k u, childRoot k u ∈ H k)
    (assignment : Fin (2 * a) ≃ Fin 3 × Fin c)
    (start : Fin (2 * a) → V)
    (hstartinj : Function.Injective start)
    (hstartOutsideRoots : ∀ q i, start q ≠ root i)
    (hstartOutsideH : ∀ q k, start q ∉ H k)
    (hrootOutsideH : ∀ i k, root i ∉ H k)
    (hlinked : Linkedness.KLinked
      (G.induce ((Finset.univ.image root : Finset V) : Set V)ᶜ)
      (2 * a))
    (hbudget : 2 * a ≤ b)
    (hfirst : ∀ i, G.Adj (root i) (start (firstConnector i)))
    (hsecond : ∀ i, G.Adj (root i) (start (secondConnector i)))
    (hdifferent : ∀ i,
      (assignment (firstConnector i)).1 ≠
        (assignment (secondConnector i)).1) :
    HasRootedCliqueMinor G root := by
  classical
  let Rset : Set V := ((Finset.univ.image root : Finset V) : Set V)ᶜ
  let target (q : Fin (2 * a)) : V :=
    childRoot (assignment q).1 (assignment q).2
  have htargetinj : Function.Injective target := by
    intro q r hqr
    by_cases hk : (assignment q).1 = (assignment r).1
    · have hu : (assignment q).2 = (assignment r).2 := by
        apply hchildRoot (assignment q).1
        simpa [target, hk] using hqr
      exact assignment.injective (Prod.ext hk hu)
    · have hqH : target q ∈ H (assignment q).1 :=
        hchildRootH _ _
      have hrH : target r ∈ H (assignment r).1 :=
        hchildRootH _ _
      exact False.elim ((Set.disjoint_left.mp (hH hk)) hqH (hqr ▸ hrH))
  have hstartR (q : Fin (2 * a)) : start q ∈ Rset := by
    intro hmem
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hmem
    exact hstartOutsideRoots q i hi.symm
  have htargetR (q : Fin (2 * a)) : target q ∈ Rset := by
    intro hmem
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hmem
    apply hrootOutsideH i (assignment q).1
    rw [hi]
    exact hchildRootH _ _
  have hstartTarget : Disjoint (Set.range start) (Set.range target) := by
    apply Set.disjoint_left.mpr
    intro v hvS hvT
    obtain ⟨q,rfl⟩ := hvS
    obtain ⟨r,hr⟩ := hvT
    apply hstartOutsideH q (assignment r).1
    rw [← hr]
    exact hchildRootH _ _
  let P' : IndexedPairs (Fin (2 * a)) Rset :=
    ⟨fun q => ⟨start q, hstartR q⟩,
      fun q => ⟨target q, htargetR q⟩⟩
  have hP'start : Function.Injective P'.start := by
    intro q r h
    exact hstartinj (congrArg Subtype.val h)
  have hP'finish : Function.Injective P'.finish := by
    intro q r h
    exact htargetinj (congrArg Subtype.val h)
  have hP'st : Disjoint (Set.range P'.start) (Set.range P'.finish) := by
    apply Set.disjoint_left.mpr
    intro v hvS hvT
    obtain ⟨q,hq⟩ := hvS
    obtain ⟨r,hr⟩ := hvT
    have heq : start q = target r :=
      congrArg Subtype.val (hq.trans hr.symm)
    exact (Set.disjoint_left.mp hstartTarget)
      ⟨q,rfl⟩ ⟨r,heq.symm⟩
  have hP'dis : P'.DisjointTerminals :=
    disjointTerminals_of_injective_ends P' hP'start hP'finish hP'st
  have hP'ne (q : Fin (2 * a)) : P'.start q ≠ P'.finish q := by
    intro h
    exact (Set.disjoint_left.mp hP'st)
      ⟨q,rfl⟩ ⟨q,h.symm⟩
  obtain ⟨L'⟩ := hlinked P' hP'dis hP'ne
  let L : IndexedLinkage G
      ⟨start, fun q => childRoot (assignment q).1 (assignment q).2⟩ := by
    change IndexedLinkage G
      ⟨fun q => (P'.start q : V), fun q => (P'.finish q : V)⟩
    exact L'.mapInduce
  have hrootOutsideL (i : Fin a) : root i ∉ L.vertices := by
    intro hi
    have hmem : root i ∈ Rset :=
      IndexedLinkage.mapInduce_vertices_subset L' hi
    have hrootmem : root i ∈ Finset.univ.image root :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    exact hmem hrootmem
  exact rooted_minor_of_three_woven_children H hH hW root hroot
    childRoot hchildRoot hchildRootH assignment start L hbudget
    hrootOutsideL hrootOutsideH hfirst hsecond hdifferent

end Woven
end HadwigerLean
