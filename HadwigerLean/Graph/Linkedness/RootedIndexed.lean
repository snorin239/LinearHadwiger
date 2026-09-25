import HadwigerLean.Graph.Linkedness.Massed

/-! Rooted linkedness for arbitrary finite families of terminal pairs. -/

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The `Fin n` formulation of rooted linkedness applies to every finite index type. -/
theorem RootedLinked.linkage_finite {G : SimpleGraph V}
    (X : Finset V) (h : RootedLinked G X)
    {ι : Type*} [Fintype ι]
    (P : IndexedPairs ι V)
    (hP : P.DisjointTerminals)
    (hne : ∀ i, P.start i ≠ P.finish i)
    (hX : ∀ i, P.terminals i ⊆ (X : Set V)) :
    ∃ L : IndexedLinkage G P, InteriorsAvoid L X := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let Q : IndexedPairs (Fin (Fintype.card ι)) V := P.reindex e
  have hQ : Q.DisjointTerminals := by
    intro i j hij
    exact hP (fun heq => hij (e.injective heq))
  obtain ⟨M, hM⟩ := h (Fintype.card ι) Q hQ (fun i => hne (e i))
    (fun i => hX (e i))
  have lift (j : Fin (Fintype.card ι)) (i : ι) (hij : e j = i) :
      ∃ p : G.Path (P.start i) (P.finish i),
        pathVertexSet p = pathVertexSet (M.path j) := by
    subst i
    exact ⟨M.path j, rfl⟩
  have hex (i : ι) : ∃ p : G.Path (P.start i) (P.finish i),
      pathVertexSet p = pathVertexSet (M.path (e.symm i)) :=
    lift (e.symm i) i (e.apply_symm_apply i)
  let q (i : ι) : G.Path (P.start i) (P.finish i) := (hex i).choose
  have hq (i : ι) : pathVertexSet (q i) = pathVertexSet (M.path (e.symm i)) :=
    (hex i).choose_spec
  let L : IndexedLinkage G P := {
    path := q
    disjoint := by
      intro i j hij
      rw [hq i, hq j]
      exact M.disjoint (fun heq => hij (e.symm.injective heq))
  }
  refine ⟨L, ?_⟩
  intro i v hv hvX
  have hm := hM (e.symm i) v (by simpa only [L, hq] using hv) hvX
  change v = P.start (e (e.symm i)) ∨ v = P.finish (e (e.symm i)) at hm
  change v = P.start i ∨ v = P.finish i
  simpa [e.apply_symm_apply i] using hm

/-- Equal-endpoint pairs may be represented by singleton paths. -/
theorem RootedLinked.linkage_finite_allow_equal {G : SimpleGraph V}
    (X : Finset V) (h : RootedLinked G X)
    {ι : Type*} [Fintype ι]
    (P : IndexedPairs ι V)
    (hP : P.DisjointTerminals)
    (hX : ∀ i, P.terminals i ⊆ (X : Set V)) :
    ∃ L : IndexedLinkage G P, InteriorsAvoid L X := by
  classical
  let A := {i : ι // P.start i ≠ P.finish i}
  let Q : IndexedPairs A V := P.reindex Subtype.val
  have hQ : Q.DisjointTerminals := by
    intro i j hij
    exact hP (fun heq => hij (Subtype.ext heq))
  obtain ⟨M,hM⟩ := h.linkage_finite X Q hQ
    (fun i => i.property) (fun i => hX i)
  let q (i : ι) : G.Path (P.start i) (P.finish i) :=
    if hi : P.start i ≠ P.finish i then M.path ⟨i,hi⟩
    else by
      have heq : P.start i = P.finish i := of_not_not hi
      rw [← heq]
      exact SimpleGraph.Path.nil
  have hactive (i : ι) (hi : P.start i ≠ P.finish i) :
      pathVertexSet (q i) = pathVertexSet (M.path ⟨i,hi⟩) := by
    simp [q,hi]
    rfl
  have loop_support {s t : V} (p : G.Path s t) (hst : s = t) :
      pathVertexSet p = {s} := by
    subst t
    exact pathVertexSet.loop p
  have hdeg (i : ι) (hi : ¬ P.start i ≠ P.finish i) :
      pathVertexSet (q i) = {P.start i} :=
    loop_support (q i) (of_not_not hi)
  have havoid (i : ι) (v : V) (hv : v ∈ pathVertexSet (q i))
      (hvX : v ∈ X) : v ∈ P.terminals i := by
    by_cases hi : P.start i ≠ P.finish i
    · rw [hactive i hi] at hv
      exact hM ⟨i,hi⟩ v hv hvX
    · rw [hdeg i hi] at hv
      exact Or.inl (by simpa using hv)
  let L : IndexedLinkage G P := {
    path := q
    disjoint := by
      intro i j hij
      by_cases hi : P.start i ≠ P.finish i
      · by_cases hj : P.start j ≠ P.finish j
        · rw [hactive i hi, hactive j hj]
          exact M.disjoint (fun heq => hij (congrArg Subtype.val heq))
        · rw [hdeg j hj]
          apply Set.disjoint_left.mpr
          intro v hvi hvj
          have hvX : v ∈ X := by
            have hvstart : v = P.start j := by simpa using hvj
            exact hvstart ▸ hX j (by simp [IndexedPairs.terminals])
          have hvterm : v ∈ P.terminals i := by
            rw [hactive i hi] at hvi
            exact hM ⟨i,hi⟩ v hvi hvX
          have hvjterm : v ∈ P.terminals j := by
            have hvstart : v = P.start j := by simpa using hvj
            exact hvstart ▸ (by simp [IndexedPairs.terminals])
          exact (Set.disjoint_left.mp (hP hij)) hvterm hvjterm
      · rw [hdeg i hi]
        apply Set.disjoint_left.mpr
        intro v hvi hvj
        have hvterm : v ∈ P.terminals i := by
          have hvstart : v = P.start i := by simpa using hvi
          exact hvstart ▸ (by simp [IndexedPairs.terminals])
        have hvX : v ∈ X := hX i hvterm
        have hvjterm : v ∈ P.terminals j := havoid j v hvj hvX
        exact (Set.disjoint_left.mp (hP hij)) hvterm hvjterm
  }
  exact ⟨L,havoid⟩
end Linkedness
end HadwigerLean
