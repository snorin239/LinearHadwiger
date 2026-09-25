import HadwigerLean.Graph.Linkedness.EdgeDeletionShore
import Mathlib.Tactic

/-! The root-edge version of Appendix F.b edge-deletion shore stability. -/

namespace HadwigerLean.RootedDensity

universe u

private theorem deleted_adj_of_edge_ne
    {V : Type u}
    (G : SimpleGraph V) (u v x y : V) (hxy : G.Adj x y)
    (hne : s(x, y) ≠ s(u, v)) :
    (G.deleteEdges {s(u, v)}).Adj x y := by
  simpa only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] using
    (show G.Adj x y ∧ s(x, y) ≠ s(u, v) from ⟨hxy, hne⟩)

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- For a deleted edge from a root to an outside vertex, common outside
neighbors and other root neighbors of the outside endpoint must all lie
in any newly created adhesion. The F.b budget therefore prevents a new
separator below the number of roots. -/
noncomputable def separation_of_delete_root_edge_of_budget
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (u v : V) (huv : G.Adj u v)
    (hu : u ∈ X) (hv : v ∉ X)
    (hbudget : X.card ≤
      ((G.neighborFinset u ∩ G.neighborFinset v) \ X).card +
        (G.neighborFinset v ∩ X.erase u).card)
    (S : VertexSeparation (G.deleteEdges {s(u,v)}))
    (hroot : (X : Set V) ⊆ S.left)
    (hsmall : Nat.card S.separator < X.card) :
    VertexSeparation G := by
  classical
  let C := (G.neighborFinset u ∩ G.neighborFinset v) \ X
  let R := G.neighborFinset v ∩ X.erase u
  have hsep_card : S.separatorFinset.card = Nat.card S.separator := by
    simp [VertexSeparation.separatorFinset]
  have hcross (huL : u ∈ S.strictLeft) (hvR : v ∈ S.strictRight) :
      C ∪ R ⊆ S.separatorFinset := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzC | hzR
    · have hzu : G.Adj u z :=
        (G.mem_neighborFinset u z).mp (Finset.mem_inter.mp
          (Finset.mem_sdiff.mp hzC).1).1
      have hzv : G.Adj v z :=
        (G.mem_neighborFinset v z).mp (Finset.mem_inter.mp
          (Finset.mem_sdiff.mp hzC).1).2
      have hkeep_u : (G.deleteEdges {s(u,v)}).Adj u z := by
        apply deleted_adj_of_edge_ne G u v u z hzu
        intro heq
        rcases (Sym2.eq_iff.mp heq) with h | h
        · exact hzv.ne h.2.symm
        · exact huv.ne h.1
      have hkeep_v : (G.deleteEdges {s(u,v)}).Adj v z := by
        apply deleted_adj_of_edge_ne G u v v z hzv
        intro heq
        rcases (Sym2.eq_iff.mp heq) with h | h
        · exact huv.ne h.1.symm
        · exact hzu.ne h.2.symm
      have hzRight : z ∈ S.right := by
        by_contra hnot
        have hzLeft : z ∈ S.left := by
          have hcover : z ∈ S.left ∪ S.right := by rw [S.cover]; trivial
          exact hcover.resolve_right hnot
        exact (S.no_cross hzLeft hnot hvR.1 hvR.2) hkeep_v.symm
      have hzLeft : z ∈ S.left := by
        by_contra hnot
        exact (S.no_cross huL.1 huL.2 hzRight hnot) hkeep_u
      exact (S.mem_separatorFinset z).mpr ⟨hzLeft,hzRight⟩
    · have hzRoot : z ∈ X := (Finset.mem_erase.mp (Finset.mem_inter.mp hzR).2).2
      have hzNe : z ≠ u := (Finset.mem_erase.mp (Finset.mem_inter.mp hzR).2).1
      have hzv : G.Adj v z :=
        (G.mem_neighborFinset v z).mp (Finset.mem_inter.mp hzR).1
      have hkeep_v : (G.deleteEdges {s(u,v)}).Adj v z := by
        apply deleted_adj_of_edge_ne G u v v z hzv
        intro heq
        rcases (Sym2.eq_iff.mp heq) with h | h
        · exact huv.ne h.1.symm
        · exact hzNe h.2
      have hzLeft : z ∈ S.left := hroot hzRoot
      have hzRight : z ∈ S.right := by
        by_contra hnot
        exact (S.no_cross hzLeft hnot hvR.1 hvR.2) hkeep_v.symm
      exact (S.mem_separatorFinset z).mpr ⟨hzLeft,hzRight⟩
  have hcrossFalse (huL : u ∈ S.strictLeft) (hvR : v ∈ S.strictRight) : False := by
    have hsub := hcross huL hvR
    have hdis : Disjoint C R := by
      apply Finset.disjoint_left.mpr
      intro z hzC hzR
      exact (Finset.mem_sdiff.mp hzC).2
        (Finset.mem_erase.mp (Finset.mem_inter.mp hzR).2).2
    have hcard : (C ∪ R).card = C.card + R.card :=
      Finset.card_union_of_disjoint hdis
    have hle := Finset.card_le_card hsub
    change X.card ≤ C.card + R.card at hbudget
    omega
  refine {
    left := S.left
    right := S.right
    cover := S.cover
    no_cross := ?_
  }
  intro a b haL haNotR hbR hbNotL hab
  have hdeleted : ¬ (G.deleteEdges {s(u,v)}).Adj a b :=
    S.no_cross haL haNotR hbR hbNotL
  have hed : s(a,b) = s(u,v) := by
    by_contra hne
    exact hdeleted (deleted_adj_of_edge_ne G u v a b hab hne)
  rcases (Sym2.eq_iff.mp hed) with h | h
  · rcases h with ⟨rfl,rfl⟩
    exact hcrossFalse ⟨haL,haNotR⟩ ⟨hbR,hbNotL⟩
  · have hbu : b = u := h.2
    rw [hbu] at hbNotL
    exact hbNotL (hroot hu)

/-- The massed shore inequality survives deletion of a root-to-outside
edge whenever the F.b common-neighbor budget dominates the root count. -/
theorem massed_shore_delete_root_edge
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (α : ℝ) (hm : MassedPair G (X : Set V) α)
    (u v : V) (huv : G.Adj u v) (hu : u ∈ X) (hv : v ∉ X)
    (hbudget : X.card ≤
      ((G.neighborFinset u ∩ G.neighborFinset v) \ X).card +
        (G.neighborFinset v ∩ X.erase u).card)
    (S : VertexSeparation (G.deleteEdges {s(u,v)}))
    (hroot : (X : Set V) ⊆ S.left)
    (hsmall : Nat.card S.separator < Nat.card (X : Set V)) :
    (edgeIncidenceSetCount (G.deleteEdges {s(u,v)}) S.strictRight : ℝ) ≤
      α * (Nat.card S.strictRight : ℝ) := by
  classical
  let T : VertexSeparation G :=
    separation_of_delete_root_edge_of_budget G X u v huv hu hv hbudget S
      hroot (by simpa using hsmall)
  have hshore := hm.shore T hroot hsmall
  have hle := edgeIncidenceSetCount_deleteEdges_le G
    ({s(u,v)} : Set (Sym2 V)) S.strictRight
  exact (by exact_mod_cast hle :
    (edgeIncidenceSetCount (G.deleteEdges {s(u,v)}) S.strictRight : ℝ) ≤
      (edgeIncidenceSetCount G S.strictRight : ℝ)).trans hshore

end HadwigerLean.RootedDensity


