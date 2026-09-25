import HadwigerLean.Graph.Linkedness.Massed
import Mathlib.Tactic

/-!
# Rooted linkedness across graph isomorphisms
-/

namespace HadwigerLean
namespace Linkedness

/-- Rooted linkedness is invariant under graph isomorphisms, with the
root set transported by the equivalence. -/
theorem rootedLinked_of_iso
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (X : Finset V) (Y : Finset W)
    (hXY : ∀ v, v ∈ X ↔ e v ∈ Y)
    (hG : RootedLinked G X) :
    RootedLinked H Y := by
  classical
  intro n P hP hne hPY
  let Q : IndexedPairs (Fin n) V :=
    ⟨fun i => e.symm (P.start i), fun i => e.symm (P.finish i)⟩
  have hQterm (i : Fin n) (v : V) :
      v ∈ Q.terminals i ↔ e v ∈ P.terminals i := by
    simp only [Q, IndexedPairs.terminals, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · left
        simpa [h]
      · right
        simpa [h]
    · rintro (h | h)
      · left
        exact e.injective (by simpa using h)
      · right
        exact e.injective (by simpa using h)
  have hQ : Q.DisjointTerminals := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro v hvi hvj
    exact (Set.disjoint_left.mp (hP hij))
      ((hQterm i v).mp hvi) ((hQterm j v).mp hvj)
  have hQne : ∀ i, Q.start i ≠ Q.finish i := by
    intro i heq
    exact hne i (e.symm.injective heq)
  have hQX : ∀ i, Q.terminals i ⊆ (X : Set V) := by
    intro i v hv
    exact (hXY v).mpr (hPY i ((hQterm i v).mp hv))
  obtain ⟨L,hLavoid⟩ := hG n Q hQ hQne hQX
  let mappedPath (i : Fin n) : H.Path (P.start i) (P.finish i) := by
    let p := (L.path i).mapEmbedding e.toEmbedding
    exact ⟨(p : H.Walk (e (Q.start i)) (e (Q.finish i))).copy
      (by simp [Q]) (by simp [Q]), by simpa using p.property⟩
  have hsupport (i : Fin n) (v : W) :
      v ∈ pathVertexSet (mappedPath i) ↔
        e.symm v ∈ pathVertexSet (L.path i) := by
    change v ∈ (((L.path i : G.Path (Q.start i) (Q.finish i)).1.map
      e.toHom).copy (by simp [Q]) (by simp [Q])).support ↔
      e.symm v ∈ (L.path i : G.Walk (Q.start i) (Q.finish i)).support
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map]
    constructor
    · intro hv
      obtain ⟨u, hu, huv⟩ := List.mem_map.mp hv
      have heq : e.symm v = u := by simpa [← huv]
      exact heq ▸ hu
    · intro hv
      exact List.mem_map.mpr ⟨e.symm v, hv, e.apply_symm_apply v⟩
  let M : IndexedLinkage H P := {
    path := mappedPath
    disjoint := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro v hvi hvj
      exact (Set.disjoint_left.mp (L.disjoint hij))
        ((hsupport i v).mp hvi) ((hsupport j v).mp hvj)
  }
  refine ⟨M, ?_⟩
  intro i v hv hvY
  have hv' : e.symm v ∈ pathVertexSet (L.path i) :=
    (hsupport i v).mp hv
  have hX : e.symm v ∈ X :=
    (hXY _).mpr (by simpa using hvY)
  have hterm := hLavoid i (e.symm v) hv' hX
  have hterm' : v ∈ P.terminals i := by
    have h := (hQterm i (e.symm v)).mp hterm
    simpa using h
  exact hterm'

end Linkedness
end HadwigerLean
