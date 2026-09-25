import HadwigerLean.Graph.Linkedness.ShortCoreMain
import HadwigerLean.Woven.PathExtension

/-!
# Adding one path to a short partial linkage
-/

namespace HadwigerLean
namespace Linkedness

set_option maxHeartbeats 1000000

namespace ShortPartial

/-- A new short path avoiding the old paths and other terminals
extends a partial short linkage by one index. -/
theorem extend
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {k : ℕ} {P : IndexedPairs (Fin k) V} {X : Finset V}
    (C : ShortPartial G P X) (i : Fin k) (hi : i ∉ C.used)
    (q : G.Path (P.start i) (P.finish i))
    (hqshort : (q : G.Walk (P.start i) (P.finish i)).length ≤ 7)
    (hqavoid : ∀ x ∈ pathVertexSet q, x ∈ X → x ∈ P.terminals i)
    (hqdis : ∀ j : C.used,
      Disjoint (pathVertexSet q) (pathVertexSet (C.path j))) :
    ∃ D : ShortPartial G P X,
      C.used.card < D.used.card := by
  classical
  let U : Finset (Fin k) := insert i C.used
  let p (j : U) : G.Path (P.start j.1) (P.finish j.1) :=
    if h : j.1 = i then by
      simpa only [h] using q
    else
      C.path ⟨j.1, by
        have hjU : j.1 ∈ U := j.2
        exact (Finset.mem_insert.mp hjU).resolve_left h⟩
  have hpnew : p ⟨i, Finset.mem_insert_self _ _⟩ = q := by
    simp [p]
  have hpold (j : C.used) :
      p ⟨j.1, Finset.mem_insert_of_mem j.2⟩ = C.path j := by
    have hne : j.1 ≠ i := by
      intro h
      exact hi (h ▸ j.2)
    simp [p, hne]
  have hgood : ShortPartialGood G P X ⟨U, p⟩ := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      by_cases hji : j.1 = i
      · have hj : j = ⟨i, Finset.mem_insert_self _ _⟩ :=
          Subtype.ext hji
        subst j
        simpa [hpnew] using hqshort
      · have hjC : j.1 ∈ C.used :=
          (Finset.mem_insert.mp j.2).resolve_left hji
        have hp : p j = C.path ⟨j.1,hjC⟩ := by
          simp [p,hji]
        simpa [hp] using C.short ⟨j.1,hjC⟩
    · intro j x hx hxX
      by_cases hji : j.1 = i
      · have hj : j = ⟨i, Finset.mem_insert_self _ _⟩ :=
          Subtype.ext hji
        subst j
        have hxq : x ∈ pathVertexSet q := by simpa [hpnew] using hx
        exact hqavoid x hxq hxX
      · have hjC : j.1 ∈ C.used :=
          (Finset.mem_insert.mp j.2).resolve_left hji
        have hp : p j = C.path ⟨j.1,hjC⟩ := by simp [p,hji]
        exact C.avoids ⟨j.1,hjC⟩ x (by simpa [hp] using hx) hxX
    · intro j l hjl
      by_cases hji : j.1 = i
      · have hj : j = ⟨i, Finset.mem_insert_self _ _⟩ :=
          Subtype.ext hji
        subst j
        have hli : l.1 ≠ i := Ne.symm hjl
        have hlC : l.1 ∈ C.used :=
          (Finset.mem_insert.mp l.2).resolve_left hli
        have hp : p l = C.path ⟨l.1,hlC⟩ := by simp [p,hli]
        simpa [hpnew,hp] using hqdis ⟨l.1,hlC⟩
      · by_cases hli : l.1 = i
        · have hl : l = ⟨i, Finset.mem_insert_self _ _⟩ :=
            Subtype.ext hli
          subst l
          have hjC : j.1 ∈ C.used :=
            (Finset.mem_insert.mp j.2).resolve_left hji
          have hp : p j = C.path ⟨j.1,hjC⟩ := by simp [p,hji]
          simpa [hpnew,hp] using (hqdis ⟨j.1,hjC⟩).symm
        · have hjC : j.1 ∈ C.used :=
            (Finset.mem_insert.mp j.2).resolve_left hji
          have hlC : l.1 ∈ C.used :=
            (Finset.mem_insert.mp l.2).resolve_left hli
          have hpj : p j = C.path ⟨j.1,hjC⟩ := by simp [p,hji]
          have hpl : p l = C.path ⟨l.1,hlC⟩ := by simp [p,hli]
          simpa [hpj,hpl] using
            C.disjoint ⟨j.1,hjC⟩ ⟨l.1,hlC⟩ hjl
  let D : ShortPartial G P X := ⟨⟨U,p⟩,hgood⟩
  refine ⟨D, ?_⟩
  change C.used.card < U.card
  rw [Finset.card_insert_of_notMem hi]
  omega


/-- Adding two outer edges to an induced path and erasing repeated
vertices increases its length by at most two. -/
theorem extendInducedPath_length_le
    {V : Type*} {G : SimpleGraph V} (S : Set V)
    {s t : V} (u w : S)
    (p : (G.induce S).Path u w)
    (hs : G.Adj s u.1) (ht : G.Adj w.1 t) :
    (extendInducedPath S u w p hs ht :
      G.Walk s t).length ≤
      (p : (G.induce S).Walk u w).length + 2 := by
  classical
  let e : (G.induce S) ↪g G := SimpleGraph.Embedding.induce S
  let q : G.Path u.1 w.1 := SimpleGraph.Path.mapEmbedding e p
  let z : G.Walk s t :=
    SimpleGraph.Walk.cons hs
      ((q : G.Walk u.1 w.1).append
        (SimpleGraph.Walk.cons ht SimpleGraph.Walk.nil))
  have hz : (extendInducedPath S u w p hs ht : G.Walk s t) = z.bypass := rfl
  rw [hz]
  calc
    z.bypass.length ≤ z.length := z.length_bypass_le_length
    _ = (p : (G.induce S).Walk u w).length + 2 := by
      simp [z, q, SimpleGraph.Path.mapEmbedding,
        SimpleGraph.Walk.length_append]
      exact SimpleGraph.Walk.length_map e.toHom (p : (G.induce S).Walk u w)

end ShortPartial
end Linkedness
end HadwigerLean
