import HadwigerLean.Graph.Linkedness.RegionLinkage
import HadwigerLean.Graph.Linkedness.Massed
import Mathlib.Tactic

/-!
# Splicing a rooted fan through a linked core
-/

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A fan, together with an inner linkage which avoids all fan arrival
vertices other than its own ends, yields a linkage between selected fan
starts. -/
theorem exists_spliced_linkage
    {G : SimpleGraph V} {r n : ℕ}
    (P : IndexedPairs (Fin r) V) (F : IndexedLinkage G P)
    (J Y : Finset V)
    (hfinish : ∀ t, P.finish t ∈ J)
    (hfirst : ∀ t x, x ∈ pathVertexSet (F.path t) →
      x ∈ J → x = P.finish t)
    (hY : ∀ t, P.finish t ∈ Y)
    (slot : Fin n × Fin 2 → Fin r) (hslot : Function.Injective slot)
    (Q : IndexedPairs (Fin n) V)
    (hQstart : ∀ i, Q.start i = P.start (slot (i,0)))
    (hQfinish : ∀ i, Q.finish i = P.start (slot (i,1)))
    (C : IndexedPairs (Fin n) V)
    (hCstart : ∀ i, C.start i = P.finish (slot (i,0)))
    (hCfinish : ∀ i, C.finish i = P.finish (slot (i,1)))
    (I : IndexedLinkage G C)
    (hIinside : ∀ i, pathVertexSet (I.path i) ⊆ (J : Set V))
    (hIavoid : ∀ i x, x ∈ pathVertexSet (I.path i) →
      x ∈ Y → x ∈ C.terminals i) :
    ∃ L : IndexedLinkage G Q,
      InteriorsAvoid L (Finset.univ.image P.start) ∧
      ∀ i, pathVertexSet (L.path i) ⊆
        pathVertexSet (F.path (slot (i,0))) ∪
        pathVertexSet (I.path i) ∪
        pathVertexSet (F.path (slot (i,1))) := by
  classical
  let A (i : Fin n) : Set V :=
    pathVertexSet (F.path (slot (i,0))) ∪
      pathVertexSet (F.path (slot (i,1)))
  let B (i : Fin n) : Set V := pathVertexSet (I.path i)
  let R (i : Fin n) : Set V := A i ∪ B i
  have hslotne {i j : Fin n} (hij : i ≠ j) (d e : Fin 2) :
      slot (i,d) ≠ slot (j,e) := by
    intro heq
    have heq' := hslot heq
    exact hij (congrArg Prod.fst heq')
  have hfan_dis {i j : Fin n} (hij : i ≠ j) (d e : Fin 2) :
      Disjoint (pathVertexSet (F.path (slot (i,d))))
        (pathVertexSet (F.path (slot (j,e)))) :=
    F.disjoint (hslotne hij d e)
  have hcross {i j : Fin n} (hij : i ≠ j) (d : Fin 2) :
      Disjoint (pathVertexSet (F.path (slot (i,d)))) (B j) := by
    apply Set.disjoint_left.mpr
    intro x hx hxb
    have hxJ : x ∈ J := hIinside j hxb
    have hxfinish : x = P.finish (slot (i,d)) :=
      hfirst (slot (i,d)) x hx hxJ
    have hxY : x ∈ Y := hxfinish ▸ hY (slot (i,d))
    have hxterm := hIavoid j x hxb hxY
    rcases hxterm with hs | ht
    · have heq : P.finish (slot (i,d)) = P.finish (slot (j,0)) := by
        rw [← hxfinish, ← hCstart j]
        exact hs
      exact hslotne hij d 0 (F.finish_injective heq)
    · have heq : P.finish (slot (i,d)) = P.finish (slot (j,1)) := by
        rw [← hxfinish, ← hCfinish j]
        exact ht
      exact hslotne hij d 1 (F.finish_injective heq)
  have hRshape (i : Fin n) : R i =
      pathVertexSet (F.path (slot (i,0))) ∪ B i ∪
        pathVertexSet (F.path (slot (i,1))) := by
    ext x
    simp only [R, A, Set.mem_union]
    tauto
  have hRconn (i : Fin n) : (G.induce (R i)).Connected := by
    let p := F.path (slot (i,0))
    let q := F.path (slot (i,1))
    have hp : (G.induce (pathVertexSet p)).Connected :=
      (p : G.Walk (P.start (slot (i,0))) (P.finish (slot (i,0)))).connected_induce_support
    have hq : (G.induce (pathVertexSet q)).Connected :=
      (q : G.Walk (P.start (slot (i,1))) (P.finish (slot (i,1)))).connected_induce_support
    have hBconn : (G.induce (B i)).Connected :=
      (I.path i : G.Walk (C.start i) (C.finish i)).connected_induce_support
    have hhit0 : P.finish (slot (i,0)) ∈ B i := by
      rw [← hCstart i]
      exact pathVertexSet.start_mem (I.path i)
    have hfront : (G.induce (pathVertexSet p ∪ B i)).Connected :=
      connected_induce_union_of_common hp hBconn
        (pathVertexSet.finish_mem p) hhit0
    have hhit1 : P.finish (slot (i,1)) ∈ B i := by
      rw [← hCfinish i]
      exact pathVertexSet.finish_mem (I.path i)
    have hfull : (G.induce ((pathVertexSet p ∪ B i) ∪ pathVertexSet q)).Connected :=
      connected_induce_union_of_common hfront hq
        (Or.inr hhit1) (pathVertexSet.finish_mem q)
    rw [hRshape i]
    simpa [p, q, B] using hfull
  have hRstart (i : Fin n) : Q.start i ∈ R i := by
    rw [hQstart i]
    exact Or.inl (Or.inl (pathVertexSet.start_mem (F.path (slot (i,0)))))
  have hRfinish (i : Fin n) : Q.finish i ∈ R i := by
    rw [hQfinish i]
    exact Or.inl (Or.inr (pathVertexSet.start_mem (F.path (slot (i,1)))))
  have hRdis : Pairwise fun i j : Fin n => Disjoint (R i) (R j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    rcases hxi with hAi | hBi
    · rcases hxj with hAj | hBj
      · rcases hAi with hAi0 | hAi1
        · rcases hAj with hAj0 | hAj1
          · exact (Set.disjoint_left.mp (hfan_dis hij 0 0)) hAi0 hAj0
          · exact (Set.disjoint_left.mp (hfan_dis hij 0 1)) hAi0 hAj1
        · rcases hAj with hAj0 | hAj1
          · exact (Set.disjoint_left.mp (hfan_dis hij 1 0)) hAi1 hAj0
          · exact (Set.disjoint_left.mp (hfan_dis hij 1 1)) hAi1 hAj1
      · rcases hAi with hAi0 | hAi1
        · exact (Set.disjoint_left.mp (hcross hij 0)) hAi0 hBj
        · exact (Set.disjoint_left.mp (hcross hij 1)) hAi1 hBj
    · rcases hxj with hAj | hBj
      · rcases hAj with hAj0 | hAj1
        · exact (Set.disjoint_left.mp (hcross hij.symm 0)) hAj0 hBi
        · exact (Set.disjoint_left.mp (hcross hij.symm 1)) hAj1 hBi
      · exact (Set.disjoint_left.mp (I.disjoint hij)) hBi hBj
  obtain ⟨L, hL⟩ :=
    exists_linkage_of_disjoint_connected_regions Q R hRconn hRstart hRfinish hRdis
  have hroot_fan (i : Fin n) (d : Fin 2) (x : V)
      (hx : x ∈ pathVertexSet (F.path (slot (i,d))))
      (hxX : x ∈ (Finset.univ.image P.start : Finset V)) :
      x = P.start (slot (i,d)) := by
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hxX
    have hxt : x ∈ pathVertexSet (F.path t) := by
      rw [← ht]
      exact pathVertexSet.start_mem (F.path t)
    by_cases heq : t = slot (i,d)
    · simpa [heq] using ht.symm
    · exact False.elim ((Set.disjoint_left.mp (F.disjoint heq)) hxt hx)
  have hroot_core (i : Fin n) (x : V)
      (hx : x ∈ B i)
      (hxX : x ∈ (Finset.univ.image P.start : Finset V)) :
      x = P.start (slot (i,0)) ∨ x = P.start (slot (i,1)) := by
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hxX
    have hxt : x ∈ pathVertexSet (F.path t) := by
      rw [← ht]
      exact pathVertexSet.start_mem (F.path t)
    have hxJ : x ∈ J := hIinside i hx
    have hxend : x = P.finish t := hfirst t x hxt hxJ
    have hxY : x ∈ Y := hxend ▸ hY t
    have hxterm := hIavoid i x hx hxY
    rcases hxterm with hs | hf
    · have heq : P.finish t = P.finish (slot (i,0)) := by
        rw [← hxend, ← hCstart i]
        exact hs
      left
      rw [← F.finish_injective heq]
      exact ht.symm
    · have heq : P.finish t = P.finish (slot (i,1)) := by
        rw [← hxend, ← hCfinish i]
        exact hf
      right
      rw [← F.finish_injective heq]
      exact ht.symm
  refine ⟨L, ?_, ?_⟩
  · intro i x hx hxX
    change x = Q.start i ∨ x = Q.finish i
    rcases hL i hx with hA | hB
    · rcases hA with h0 | h1
      · exact Or.inl ((hroot_fan i 0 x h0 hxX).trans (hQstart i).symm)
      · exact Or.inr ((hroot_fan i 1 x h1 hxX).trans (hQfinish i).symm)
    · rcases hroot_core i x hB hxX with h0 | h1
      · exact Or.inl (h0.trans (hQstart i).symm)
      · exact Or.inr (h1.trans (hQfinish i).symm)
  · intro i
    simpa [hRshape i, B] using hL i

end Linkedness
end HadwigerLean
