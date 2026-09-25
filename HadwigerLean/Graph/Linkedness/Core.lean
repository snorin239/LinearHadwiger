import HadwigerLean.Graph.Linkedness.Massed
import HadwigerLean.Graph.Linkedness.EdgeDeletionShore
import HadwigerLean.Graph.Linkedness.IncidenceHandshake
import Mathlib.Combinatorics.Hall.Finite

/-!
# Elementary linked cores

Direct edges link paired roots in a clique. The remaining core lemmas select
distinct intermediate vertices when every prescribed pair has many common
neighbors, the short-path ingredient of Appendix D.
-/

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem singletonPath_vertices {G : SimpleGraph V} {s t : V}
    (h : G.Adj s t) :
    pathVertexSet (SimpleGraph.Path.singleton h) = {s, t} := by
  ext v
  simp [pathVertexSet, SimpleGraph.Path.singleton]

private def twoEdgePath {G : SimpleGraph V} {s m t : V}
    (hsm : G.Adj s m) (hmt : G.Adj m t) (hst : s ≠ t) :
    G.Path s t := by
  let p : G.Path s m := SimpleGraph.Path.singleton hsm
  have ht : t ∉ (p : G.Walk s m).support := by
    simpa [p, SimpleGraph.Path.singleton] using
      (show t ≠ s ∧ t ≠ m from ⟨Ne.symm hst, Ne.symm hmt.ne⟩)
  exact ⟨(p : G.Walk s m).concat hmt, p.property.concat ht hmt⟩

private theorem twoEdgePath_vertices {G : SimpleGraph V} {s m t : V}
    (hsm : G.Adj s m) (hmt : G.Adj m t) (hst : s ≠ t) :
    pathVertexSet (twoEdgePath hsm hmt hst) = {s, m, t} := by
  ext v
  simp [pathVertexSet, twoEdgePath, SimpleGraph.Path.singleton]
/-- Families of `n` finite sets, each of size at least `n`, admit distinct
representatives. This is the Hall step for choosing path middles. -/
theorem representatives_of_large (n : ℕ) (t : Fin n → Finset V)
    (hlarge : ∀ i, n ≤ (t i).card) :
    ∃ f : Fin n → V, Function.Injective f ∧ ∀ i, f i ∈ t i := by
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp
  intro s
  by_cases hs : s.Nonempty
  · obtain ⟨i, hi⟩ := hs
    have hsub : t i ⊆ s.biUnion t := by
      intro v hv
      exact Finset.mem_biUnion.mpr ⟨i, hi, hv⟩
    calc
      s.card ≤ n := by
        simpa using Finset.card_le_card (Finset.subset_univ s)
      _ ≤ (t i).card := hlarge i
      _ ≤ (s.biUnion t).card := Finset.card_le_card hsub
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hempty]
/-- Common neighbors outside the designated roots. -/
noncomputable def commonOutside (G : SimpleGraph V) (X : Finset V)
    (s t : V) : Finset V := by
  classical
  exact (G.neighborFinset s ∩ G.neighborFinset t) \ X

@[simp] theorem mem_commonOutside (G : SimpleGraph V) (X : Finset V)
    (s t v : V) :
    v ∈ commonOutside G X s t ↔ G.Adj s v ∧ G.Adj t v ∧ v ∉ X := by
  classical
  simp [commonOutside, SimpleGraph.mem_neighborFinset, and_assoc]
/-- If the roots form a clique, pairing edges already give a rooted linkage. -/
theorem rootedLinked_of_clique (G : SimpleGraph V) (X : Finset V)
    (hclique : ∀ u ∈ X, ∀ v ∈ X, u ≠ v → G.Adj u v) :
    RootedLinked G X := by
  intro n P hP hne hX
  have hadj (i : Fin n) : G.Adj (P.start i) (P.finish i) :=
    hclique (P.start i) (hX i (by simp [IndexedPairs.terminals]))
      (P.finish i) (hX i (by simp [IndexedPairs.terminals])) (hne i)
  let L : IndexedLinkage G P := {
    path := fun i => SimpleGraph.Path.singleton (hadj i)
    disjoint := by
      intro i j hij
      simpa [singletonPath_vertices, IndexedPairs.terminals] using hP hij
  }
  refine ⟨L, ?_⟩
  intro i v hv hroot
  simpa [L, singletonPath_vertices, IndexedPairs.terminals] using hv


/-- Distinct representatives among sufficiently numerous common neighbors
produce disjoint length-two paths with interiors outside the roots. -/
theorem rooted_linkage_of_common_neighbors (G : SimpleGraph V)
    (X : Finset V) (n : ℕ) (P : IndexedPairs (Fin n) V)
    (hP : P.DisjointTerminals)
    (hne : ∀ i, P.start i ≠ P.finish i)
    (hX : ∀ i, P.terminals i ⊆ (X : Set V))
    (hcommon : ∀ i, n ≤
      (commonOutside G X (P.start i) (P.finish i)).card) :
    ∃ L : IndexedLinkage G P, InteriorsAvoid L X := by
  classical
  let t : Fin n → Finset V := fun i =>
    commonOutside G X (P.start i) (P.finish i)
  obtain ⟨f, hfinj, hf⟩ := representatives_of_large n t hcommon
  have hmid (i : Fin n) :
      G.Adj (P.start i) (f i) ∧
        G.Adj (P.finish i) (f i) ∧ f i ∉ X :=
    (mem_commonOutside G X _ _ _).mp (hf i)
  let q (i : Fin n) : G.Path (P.start i) (P.finish i) :=
    twoEdgePath (hmid i).1 (hmid i).2.1.symm (hne i)
  have hvertices (i : Fin n) :
      pathVertexSet (q i) = P.terminals i ∪ {f i} := by
    ext v
    simp [q, twoEdgePath_vertices, IndexedPairs.terminals, or_assoc, or_comm, or_left_comm]
  let L : IndexedLinkage G P := {
    path := q
    disjoint := by
      intro i j hij
      rw [hvertices i, hvertices j]
      apply Set.disjoint_left.mpr
      intro v hi hj
      rcases hi with hti | hmi
      · rcases hj with htj | hmj
        · exact (Set.disjoint_left.mp (hP hij)) hti htj
        · have hv : v = f j := by simpa using hmj
          exact (hmid j).2.2 (hv ▸ hX i hti)
      · rcases hj with htj | hmj
        · have hv : v = f i := by simpa using hmi
          exact (hmid i).2.2 (hv ▸ hX j htj)
        · have hfi : v = f i := by simpa using hmi
          have hfj : v = f j := by simpa using hmj
          exact hij (hfinj (hfi.symm.trans hfj))
  }
  refine ⟨L, ?_⟩
  intro i v hv hroot
  rw [hvertices i] at hv
  rcases hv with hterm | hmiddle
  · exact hterm
  · have hvf : v = f i := by simpa using hmiddle
    exact False.elim ((hmid i).2.2 (hvf ▸ hroot))

/-- A strengthened form of (D.7) supplies at least `k` common neighbors
outside any set of at most `2k` designated terminals. The four units of
slack removed from (D.7) are available in the `5k`-minimum-degree,
`7k`-vertex core where this will be applied. -/
theorem commonOutside_card_ge_of_minDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (k δ : ℕ) (hdegree : ∀ v, δ ≤ G.degree v)
    (hsize : Fintype.card V + 3 * k ≤ 2 * δ)
    (X : Finset V) (hX : X.card ≤ 2 * k) (s t : V) :
    k ≤ (commonOutside G X s t).card := by
  classical
  let U := G.neighborFinset s
  let W := G.neighborFinset t
  have hU : δ ≤ U.card := by
    simpa [U, G.card_neighborFinset_eq_degree] using hdegree s
  have hW : δ ≤ W.card := by
    simpa [W, G.card_neighborFinset_eq_degree] using hdegree t
  have hunion : (U ∪ W).card ≤ Fintype.card V := Finset.card_le_univ _
  have hinter : (U ∩ W).card ≤ (commonOutside G X s t).card + X.card := by
    have hsubset : U ∩ W ⊆ commonOutside G X s t ∪ X := by
      intro v hv
      by_cases hvX : v ∈ X
      · exact Finset.mem_union.mpr (Or.inr hvX)
      · apply Finset.mem_union.mpr
        left
        have hs : G.Adj s v := by simpa [U] using (Finset.mem_inter.mp hv).1
        have ht : G.Adj t v := by simpa [W] using (Finset.mem_inter.mp hv).2
        exact (mem_commonOutside G X s t v).mpr ⟨hs, ht, hvX⟩
    calc
      (U ∩ W).card ≤ (commonOutside G X s t ∪ X).card :=
        Finset.card_le_card hsubset
      _ ≤ (commonOutside G X s t).card + X.card :=
        Finset.card_union_le _ _
  have hsum := Finset.card_union_add_card_inter U W
  omega

/-- The degree criterion used for the final small component in Appendix D.
It is slightly stronger than (D.7), but the `5k` by `7k` application
meets it exactly. -/
theorem kLinked_of_high_minDegree (G : SimpleGraph V) [DecidableRel G.Adj] (k δ : ℕ)
    (hdegree : ∀ v, δ ≤ G.degree v)
    (hsize : Fintype.card V + 3 * k ≤ 2 * δ) :
    KLinked G k := by
  intro P hP hne
  let X := terminalFinset P
  have hX : X.card ≤ 2 * k := by
    simpa [X] using terminalFinset_card_le P
  have hcommon : ∀ i : Fin k,
      k ≤ (commonOutside G X (P.start i) (P.finish i)).card := by
    intro i
    exact commonOutside_card_ge_of_minDegree G k δ hdegree hsize X hX _ _
  obtain ⟨L, _⟩ := rooted_linkage_of_common_neighbors G X k P hP hne
    (terminals_subset_terminalFinset P) hcommon
  exact ⟨L⟩
/-- A vertex of degree below `2r` whose incident edges each have at least
`r-1` common neighbors lies in an induced core of order at most `2r`
and minimum degree at least `r`. This is the local step of Appendix D. -/
theorem closedNeighborhood_small_dense_core (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (r : ℕ)
    (hdegreeLow : r ≤ G.degree v) (hdegree : G.degree v < 2 * r)
    (hcommon : ∀ u : V, G.Adj v u →
      r - 1 ≤ (G.neighborFinset v ∩ G.neighborFinset u).card) :
    let S : Set V := {w | w = v ∨ G.Adj v w}
    Fintype.card S ≤ 2 * r ∧
      ∀ u : S, r ≤ (G.induce S).degree u := by
  intro S
  have hS : S.toFinset = insert v (G.neighborFinset v) := by
    ext w
    simp [S, SimpleGraph.mem_neighborFinset, eq_comm]
  have hvnot : v ∉ G.neighborFinset v := G.notMem_neighborFinset_self v
  have hsize : Fintype.card S ≤ 2 * r := by
    have hc : Fintype.card S = S.toFinset.card := (Set.toFinset_card S).symm
    rw [hc, hS, Finset.card_insert_of_notMem hvnot]
    rw [G.card_neighborFinset_eq_degree]
    omega
  refine ⟨hsize, ?_⟩
  intro u
  by_cases hu : (u : V) = v
  · have hvS : v ∈ S := Or.inl rfl
    have hueq : u = (⟨v, hvS⟩ : S) := Subtype.ext hu
    subst u
    have hneigh : G.neighborSet v ⊆ S := by
      intro w hw
      exact Or.inr hw
    have hEq := G.degree_induce_of_neighborSet_subset
      (s := S) (v := (⟨v, hvS⟩ : S)) hneigh
    calc
      r ≤ G.degree v := hdegreeLow
      _ = (G.induce S).degree (⟨v, hvS⟩ : S) := hEq.symm
  · have huAdj : G.Adj v u := by
      rcases u.property with heq | hadj
      · exact False.elim (hu heq)
      · exact hadj
    let C := G.neighborFinset v ∩ G.neighborFinset (u : V)
    have hvC : v ∉ C := by simp [C, hvnot]
    have hCcard : r ≤ (insert v C).card := by
      rw [Finset.card_insert_of_notMem hvC]
      have hc := hcommon (u : V) huAdj
      change r - 1 ≤ C.card at hc
      omega
    have hsubset : insert v C ⊆ G.neighborFinset (u : V) ∩ S.toFinset := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr huAdj.symm,
          Set.mem_toFinset.mpr (Or.inl rfl)⟩
      · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hw).2,
          Set.mem_toFinset.mpr (Or.inr ((G.mem_neighborFinset v w).mp
            (Finset.mem_inter.mp hw).1))⟩
    have hmap := G.map_neighborFinset_induce (s := S) u
    have hmapCard : (G.induce S).degree u =
        (G.neighborFinset (u : V) ∩ S.toFinset).card := by
      calc
        (G.induce S).degree u = ((G.induce S).neighborFinset u).card :=
          ((G.induce S).card_neighborFinset_eq_degree u).symm
        _ = (((G.induce S).neighborFinset u).map
            (Function.Embedding.subtype (· ∈ S))).card := by
          rw [Finset.card_map]
        _ = (G.neighborFinset (u : V) ∩ S.toFinset).card :=
          congrArg Finset.card hmap
    rw [hmapCard]
    exact hCcard.trans (Finset.card_le_card hsubset)


/-- The edge-tight and common-neighbor estimates yield the small dense
closed-neighborhood core in Appendix D. -/
theorem exists_small_dense_core_of_tight
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (k : ℕ)
    (hk : 0 < k) (hXlower : 2 ≤ X.card) (hXupper : X.card ≤ 2 * k)
    (hm : MassedPair G (X : Set V) ((8 * k : ℕ) : ℝ))
    (htight : edgeIncidenceSetCount G (X : Set V)ᶜ =
      (8 * k) * (Xᶜ).card + 1)
    (hneighbor : ∀ v ∉ X, ∃ u, G.Adj v u)
    (hcommon : ∀ u v, (u ∉ X ∨ v ∉ X) → G.Adj u v →
      8 * k - 1 ≤ (G.neighborFinset u ∩ G.neighborFinset v).card) :
    ∃ v ∈ Xᶜ,
      let S : Set V := {w | w = v ∨ G.Adj v w}
      Fintype.card S ≤ 16 * k ∧
        ∀ u : S, 8 * k ≤ (G.induce S).degree u := by
  have hroot : ∀ x ∈ X, 2 ≤ (G.neighborFinset x \ X).card := by
    intro x hx
    have h := root_outdegree_ge_six_k G X k hk hXupper hm
      (fun a b ha hb hab => hcommon a b (Or.inr hb) hab) x hx
    omega
  obtain ⟨v, hv, hvlow⟩ :=
    exists_outside_degree_lt_twice_of_tight G X (8 * k) hXlower htight hroot
  have hvnot : v ∉ X := Finset.mem_compl.mp hv
  have hvhigh : 8 * k ≤ G.degree v :=
    outside_degree_ge_of_common_neighbors G X (8 * k) (by omega) hneighbor
      (fun a b ha hab => hcommon a b (Or.inl ha) hab) v hvnot
  refine ⟨v, hv, ?_⟩
  simpa only [show 2 * (8 * k) = 16 * k by omega] using
    (closedNeighborhood_small_dense_core G v (8 * k) hvhigh hvlow
      (fun u hadj => hcommon v u (Or.inl hvnot) hadj))

/-- The D.5 core consequence in the orientation supplied by the edge-contraction
common-neighbor estimate: the second endpoint lies outside the roots. -/
theorem exists_small_dense_core_of_tight_right
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (k : ℕ)
    (hk : 0 < k) (hXlower : 2 ≤ X.card) (hXupper : X.card ≤ 2 * k)
    (hm : MassedPair G (X : Set V) ((8 * k : ℕ) : ℝ))
    (htight : edgeIncidenceSetCount G (X : Set V)ᶜ =
      (8 * k) * (Xᶜ).card + 1)
    (hneighbor : ∀ v ∉ X, ∃ u, G.Adj v u)
    (hcommon : ∀ u v, v ∉ X → G.Adj u v →
      8 * k - 1 ≤ (G.neighborFinset u ∩ G.neighborFinset v).card) :
    ∃ v ∈ Xᶜ,
      let S : Set V := {w | w = v ∨ G.Adj v w}
      Fintype.card S ≤ 16 * k ∧
        ∀ u : S, 8 * k ≤ (G.induce S).degree u := by
  apply exists_small_dense_core_of_tight G X k hk hXlower hXupper hm
    htight hneighbor
  intro u v hout hadj
  rcases hout with hu | hv
  · have h := hcommon v u hu hadj.symm
    simpa only [Finset.inter_comm] using h
  · exact hcommon u v hv hadj
/-- D.3: incidence minimality forces exact global edge tightness at any exterior edge with enough common neighbors. -/
theorem massed_global_edge_tight_of_minimal_bad
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (r : ℕ)
    (hm : MassedPair G (X : Set V) (r : ℝ))
    (hbad : ¬ RootedLinked G X)
    (u v : V) (huv : G.Adj u v)
    (hout : u ∉ X ∨ v ∉ X)
    (hcommon : X.card ≤ (G.neighborFinset u ∩ G.neighborFinset v).card)
    (hminDeleted : MassedPair (G.deleteEdges {s(u,v)})
      (X : Set V) (r : ℝ) →
      RootedLinked (G.deleteEdges {s(u,v)}) X) :
    edgeIncidenceSetCount G (X : Set V)ᶜ =
      r * ((X : Set V)ᶜ).ncard + 1 := by
  have hbadDeleted : ¬ RootedLinked (G.deleteEdges {s(u,v)}) X := by
    intro h
    exact hbad (RootedLinked.mono_graph (G.deleteEdges_le _) X h)
  have hfail : ¬ ((r : ℝ) *
      (Nat.card {w : V // w ∉ (X : Set V)} : ℝ) <
      (edgeIncidenceSetCount (G.deleteEdges {s(u,v)})
        (X : Set V)ᶜ : ℝ)) := by
    intro hg
    have hmDeleted : MassedPair (G.deleteEdges {s(u,v)})
        (X : Set V) (r : ℝ) := by
      refine ⟨hg, ?_⟩
      intro S hroot hsep
      exact massed_shore_delete_edge G X (r : ℝ) hm u v huv
        hcommon S hroot hsep
    exact hbadDeleted (hminDeleted hmDeleted)
  exact massed_global_edge_tight G X r hm u v huv hout hfail


end Linkedness
end HadwigerLean
