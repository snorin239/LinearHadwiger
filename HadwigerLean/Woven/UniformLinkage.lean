import HadwigerLean.Woven.Basic
import HadwigerLean.Graph.Linkedness.Final
import Mathlib.Tactic

/-!
# Singleton terminal pairs in high-connectivity linkage

Temporary extra terminals convert singleton pairs to nontrivial pairs.
A linkage of the enlarged family is then shortened back to singleton
paths, preserving disjointness by inclusion of each path support.
-/

namespace HadwigerLean.Woven

universe u

/-- `32b` connectivity links every family of at most `b` disjoint terminal
pairs, including pairs with equal endpoints. -/
theorem indexed_linkage_of_thirtytwo_mul_connected
    {V : Type u} [Fintype V] (G : SimpleGraph V) (b j : ℕ)
    (hconn : VertexConnected G (32 * b)) (hj : j ≤ b)
    (P : IndexedPairs (Fin j) V) (hP : P.DisjointTerminals) :
    Nonempty (IndexedLinkage G P) := by
  classical
  let Y := Linkedness.terminalFinset P
  have hY : Y.card ≤ 2 * j := by
    simpa [Y] using Linkedness.terminalFinset_card_le P
  have hcardV : 32 * b < Fintype.card V := hconn.order_gt
  have hcomp : (Yᶜ).card + Y.card = Fintype.card V :=
    Finset.card_compl_add_card Y
  have hfree : j ≤ (Yᶜ).card := by omega
  have hsubcard : Fintype.card {v : V // v ∉ Y} = (Yᶜ).card := by
    apply Fintype.card_of_finset' (p := {v : V | v ∉ Y}) (Yᶜ)
    intro v
    simp
  obtain ⟨zEmb⟩ : Nonempty (Fin j ↪ {v : V // v ∉ Y}) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa [hsubcard] using hfree
  let z : Fin j → V := fun i => zEmb i
  have hz : ∀ i, z i ∉ Y := fun i => (zEmb i).property
  have hzinj : Function.Injective z := by
    intro i l h
    exact zEmb.injective (Subtype.val_injective h)
  let Q : IndexedPairs (Fin j) V := {
    start := P.start
    finish := fun i => if P.start i = P.finish i then z i else P.finish i
  }
  have hYmem (i : Fin j) {v : V} (hv : v ∈ P.terminals i) : v ∈ Y :=
    Linkedness.terminals_subset_terminalFinset P i hv
  have hQmem (i : Fin j) {v : V} (hv : v ∈ Q.terminals i) :
      v ∈ P.terminals i ∨ v = z i := by
    change v = P.start i ∨
      v = (if P.start i = P.finish i then z i else P.finish i) at hv
    rcases hv with h | h
    · left
      simp [IndexedPairs.terminals, h]
    · by_cases hi : P.start i = P.finish i
      · right
        simpa [hi] using h
      · left
        have hvfin : v = P.finish i := by simpa [hi] using h
        simp [IndexedPairs.terminals, hvfin]
  have hQdisj : Q.DisjointTerminals := by
    intro i l hil
    apply Set.disjoint_left.mpr
    intro v hvi hvl
    rcases hQmem i hvi with hviP | hviZ
    · rcases hQmem l hvl with hvlP | hvlZ
      · exact (Set.disjoint_left.mp (hP hil)) hviP hvlP
      · subst v
        exact hz l (hYmem i hviP)
    · rcases hQmem l hvl with hvlP | hvlZ
      · subst v
        exact hz i (hYmem l hvlP)
      · exact hil (hzinj (hviZ.symm.trans hvlZ))
  have hQne : ∀ i, Q.start i ≠ Q.finish i := by
    intro i
    by_cases hi : P.start i = P.finish i
    · change P.start i ≠ (if P.start i = P.finish i then z i else P.finish i)
      simp only [if_pos hi]
      intro h
      exact hz i (h ▸ hYmem i (by simp [IndexedPairs.terminals]))
    · simpa [Q, hi] using hi
  have hconnj : VertexConnected G (16 * j) :=
    hconn.of_le (by omega)
  obtain ⟨LQ⟩ :=
    Linkedness.kLinked_of_sixteen_mul_vertexConnected G j hconnj Q hQdisj hQne
  let path (i : Fin j) : G.Path (P.start i) (P.finish i) :=
    if hi : P.start i = P.finish i then
      ⟨((SimpleGraph.Path.nil : G.Path (P.start i) (P.start i)) :
          G.Walk (P.start i) (P.start i)).copy rfl hi,
        by simpa using
          (SimpleGraph.Path.nil : G.Path (P.start i) (P.start i)).property⟩
    else
      have hfinish : Q.finish i = P.finish i := by simp [Q, hi]
      ⟨((LQ.path i : G.Path (Q.start i) (Q.finish i)) :
          G.Walk (Q.start i) (Q.finish i)).copy rfl hfinish,
        by simpa using (LQ.path i).property⟩
  have hsubset (i : Fin j) : pathVertexSet (path i) ⊆
      pathVertexSet (LQ.path i) := by
    by_cases hi : P.start i = P.finish i
    · intro v hv
      have hvstart : v = P.start i := by
        simpa [path, hi, pathVertexSet, SimpleGraph.Walk.support_copy] using hv
      subst v
      exact pathVertexSet.start_mem (LQ.path i)
    · intro v hv
      simpa [path, hi, pathVertexSet, SimpleGraph.Walk.support_copy] using hv
  exact ⟨{
    path := path
    disjoint := by
      intro i l hil
      exact (LQ.disjoint hil).mono (hsubset i) (hsubset l)
  }⟩

end HadwigerLean.Woven


