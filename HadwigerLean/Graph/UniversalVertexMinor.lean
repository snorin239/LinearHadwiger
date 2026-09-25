import HadwigerLean.Graph.Minor

/-!
# Adding a universal vertex to a clique minor

A clique minor in a vertex set extends by one branch when an outside vertex
is adjacent to every vertex of that set.  The neighborhood instance is used
in the small-order clique density induction.
-/

namespace HadwigerLean

universe u

/-- A vertex complete to an induced subgraph extends any clique minor there
by a singleton branch. -/
theorem hasCliqueMinor_succ_of_universal_set {V : Type u} {G : SimpleGraph V}
    (v : V) (S : Set V) (hv : v ∉ S)
    (hcomplete : ∀ x ∈ S, G.Adj v x) {n : ℕ}
    (hminor : HasCliqueMinor (G.induce S) n) :
    HasCliqueMinor G (n + 1) := by
  classical
  obtain ⟨M⟩ := hminor
  let e : (G.induce S) ↪g G := SimpleGraph.Embedding.induce S
  let N : MinorModel (SimpleGraph.completeGraph (Fin n)) G :=
    M.map e.toHom e.injective
  have branch_subset (i : Fin n) : N.branch i ⊆ S := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have branch_disjoint (i : Fin n) : Disjoint ({v} : Set V) (N.branch i) := by
    apply Set.disjoint_left.mpr
    intro x hx hxi
    have hxv : x = v := by simpa using hx
    subst x
    exact hv (branch_subset i hxi)
  refine ⟨{
    branch := Fin.cases {v} N.branch
    connected := ?_
    disjoint := ?_
    adjacent := ?_
  }⟩
  · intro i
    cases i using Fin.cases with
    | zero => simp
    | succ i => exact N.connected i
  · intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => exact branch_disjoint j
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (branch_disjoint i).symm
      | succ j =>
        apply N.disjoint
        intro heq
        exact hij (congrArg Fin.succ heq)
  · intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (hij.ne rfl).elim
      | succ j =>
        let x := N.representative j
        exact ⟨v, by simp, x, N.representative_mem j,
          hcomplete x (branch_subset j (N.representative_mem j))⟩
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        let x := N.representative i
        exact ⟨x, N.representative_mem i, v, by simp,
          (hcomplete x (branch_subset i (N.representative_mem i))).symm⟩
      | succ j =>
        apply N.adjacent
        intro heq
        exact hij.ne (congrArg Fin.succ heq)

/-- A clique minor inside a vertex neighborhood can be enlarged using that
vertex as one more branch. -/
theorem hasCliqueMinor_succ_of_neighbor_minor {V : Type u}
    (G : SimpleGraph V) (v : V) {n : ℕ}
    (hminor : HasCliqueMinor (G.induce (G.neighborSet v)) n) :
    HasCliqueMinor G (n + 1) :=
  hasCliqueMinor_succ_of_universal_set v (G.neighborSet v)
    (by simp) (fun _ hx => hx) hminor

end HadwigerLean
