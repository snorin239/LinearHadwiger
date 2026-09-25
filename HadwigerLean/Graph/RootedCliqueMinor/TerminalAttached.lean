import HadwigerLean.Graph.RootedCliqueMinor.SpliceAttached
import HadwigerLean.Graph.RootedCliqueMinor.MengerAlternatives

/-!
# The terminal attached-model case of the rooted-clique-minor induction

Disjoint paths from the prescribed roots to a clique disjoint from those
roots yield an attached clique model by dropping the first vertex of each path.
-/

namespace HadwigerLean

namespace RootAttachedCliqueModel

/-- A root-to-clique linkage whose finishes avoid the roots produces an
attached clique model. Its branch is each path with its root removed. -/
noncomputable def ofLinkageToClique
    {V : Type*} {G : SimpleGraph V} {r : ℕ}
    {root : Fin r → V} {P : IndexedPairs (Fin r) V}
    (L : IndexedLinkage G P)
    (hstart : ∀ i, P.start i = root i)
    (hfinishAway : ∀ i, P.finish i ∉ Set.range root)
    (hclique : ∀ ⦃i j⦄, i ≠ j → G.Adj (P.finish i) (P.finish j)) :
    RootAttachedCliqueModel G root := by
  have hnonempty (i : Fin r) :
      ¬(L.path i : G.Walk (P.start i) (P.finish i)).Nil := by
    intro hnil
    have heq : P.start i = P.finish i := hnil.eq
    exact hfinishAway i ⟨i, (hstart i).symm.trans heq⟩
  have hfinish (i : Fin r) :
      P.finish i ∈ pathAfterStart (L.path i) := by
    rw [pathAfterStart_eq_tail_support (L.path i) (hnonempty i)]
    rw [(L.path i : G.Walk (P.start i) (P.finish i)).support_tail_of_not_nil
      (hnonempty i)]
    exact (L.path i : G.Walk (P.start i) (P.finish i)).end_mem_tail_support
      (hnonempty i)
  refine {
    branch := fun i => pathAfterStart (L.path i)
    root_injective := ?_
    connected := fun i => pathAfterStart_connected (L.path i) (hnonempty i)
    disjoint := ?_
    avoids_roots := ?_
    adjacent := ?_
    attached := ?_
  }
  · intro i j hij
    exact L.start_injective ((hstart i).trans (hij.trans (hstart j).symm))
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro v hvi hvj
    exact (Set.disjoint_left.mp (L.disjoint hij))
      (pathAfterStart_subset (L.path i) hvi)
      (pathAfterStart_subset (L.path j) hvj)
  · intro i j hroot
    have hj : P.start j ∈ pathAfterStart (L.path i) := by
      simpa only [hstart j] using hroot
    by_cases hij : i = j
    · subst j
      exact start_not_mem_pathAfterStart (L.path i) hj
    · exact (Set.disjoint_left.mp (L.disjoint hij))
        (pathAfterStart_subset (L.path i) hj)
        (pathVertexSet.start_mem (L.path j))
  · intro i j hij
    exact ⟨P.finish i, hfinish i, P.finish j, hfinish j, hclique hij⟩
  · intro i
    let w : G.Walk (P.start i) (P.finish i) := L.path i
    refine ⟨w.snd, ?_, ?_⟩
    · rw [pathAfterStart_eq_tail_support (L.path i) (hnonempty i)]
      rw [w.support_tail_of_not_nil (hnonempty i)]
      exact w.snd_mem_tail_support (hnonempty i)
    · simpa only [← hstart i] using w.adj_snd (hnonempty i)

end RootAttachedCliqueModel

/-- An r-connected graph with an r-vertex clique outside the prescribed
roots has an attached rooted K_r model. -/
theorem rootAttachedCliqueModel_of_connected_clique_away
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r : ℕ}
    (hconn : VertexConnected G r)
    (root : Fin r → V) (hroot : Function.Injective root)
    (Q : Finset V) (hQcard : Q.card = r)
    (hQaway : Disjoint (Q : Set V) (Set.range root))
    (hclique : ∀ ⦃u w : V⦄, u ∈ Q → w ∈ Q → u ≠ w → G.Adj u w) :
    Nonempty (RootAttachedCliqueModel G root) := by
  obtain ⟨P, L, hstart, hfinishQ, hfinishCover⟩ :=
    exists_root_target_linkage hconn root hroot Q hQcard
  refine ⟨RootAttachedCliqueModel.ofLinkageToClique L hstart ?_ ?_⟩
  · intro i hrootmem
    exact (Set.disjoint_left.mp hQaway) (hfinishQ i) hrootmem
  · intro i j hij
    apply hclique (hfinishQ i) (hfinishQ j)
    exact L.finish_injective.ne hij

end HadwigerLean
