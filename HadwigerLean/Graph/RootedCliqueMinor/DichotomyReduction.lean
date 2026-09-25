import HadwigerLean.Graph.RootedCliqueMinor.ContractionAttached
import HadwigerLean.Graph.RootedCliqueMinor.SeparationPullback

/-!
# The contraction step of the rooted-clique separator dichotomy

An attached model in the quotient lifts through a root-free contraction.
A small quotient separation either already pulls back with order below r,
or gives an order-r separation whose boundary contains the contracted edge.
-/

namespace HadwigerLean

theorem cliqueModel_contract_nonroot_edge_branch
    {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (root : Fin r → V)
    (M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots G (Set.range root)))
    {a b : V} (hab : G.Adj a b)
    (i₀ : Fin (2 * r))
    (ha : a ∈ M.branch i₀) (hb : b ∈ M.branch i₀)
    (j : Fin (2 * r)) :
    (cliqueModel_contract_nonroot_edge root M hab i₀ ha hb).branch j =
      (edgeContractionPartition G hab).index '' M.branch j := by
  let Pplus := edgeContractionPartition (completeRoots G (Set.range root))
    (completeRoots.supergraph hab)
  let P := edgeContractionPartition G hab
  have hindex (x : V) : Pplus.index x = P.index x := by
    apply P.index_eq_of_mem
    exact Pplus.index_mem x
  change Pplus.index '' M.branch j = P.index '' M.branch j
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, hindex x⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (hindex x).symm⟩

/-- The third outcome of a contraction step is the order-r boundary used
for the recursive torso argument. -/
structure RootCliqueCriticalSeparation
    {V : Type*} [Fintype V] (G : SimpleGraph V) {r : ℕ}
    (root : Fin r → V)
    (M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots G (Set.range root)))
    (a b : V) where
  sep : VertexSeparation G
  order_eq : sep.separatorFinset.card = r
  roots_left : ∀ i, root i ∈ sep.left
  branch_far : ∃ j, M.branch j ⊆ sep.strictRight
  a_boundary : a ∈ sep.separatorFinset
  b_boundary : b ∈ sep.separatorFinset

/-- Apply a quotient dichotomy to a contraction in a root-free model
branch. The nonterminal case has an order-r boundary containing the edge. -/
theorem rootClique_contraction_reduction
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r : ℕ}
    (root : Fin r → V)
    (hroot : Function.Injective root)
    (M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots G (Set.range root)))
    {a b : V} (hab : G.Adj a b)
    (i₀ : Fin (2 * r))
    (ha : a ∈ M.branch i₀) (hb : b ∈ M.branch i₀)
    (haR : a ∉ Set.range root) (hbR : b ∉ Set.range root)
    (hD : RootCliqueSeparatorDichotomy (edgeContraction G hab) r) :
    Nonempty (RootAttachedCliqueModel G root) ∨
    Nonempty (RootCliqueSeparatorOutcome G root M) ∨
    Nonempty (RootCliqueCriticalSeparation G root M a b) := by
  classical
  let qroot := edgeContractionRoot hab root
  let Mq := cliqueModel_contract_nonroot_edge root M hab i₀ ha hb
  have hqinj : Function.Injective qroot :=
    edgeContractionRoot_injective hab root hroot haR
  rcases hD qroot hqinj Mq with hA | hS
  · obtain ⟨A⟩ := hA
    exact Or.inl ⟨liftRootAttached_edgeContraction hab root haR hbR A⟩
  · obtain ⟨S⟩ := hS
    let P := edgeContractionPartition G hab
    let T := S.sep.pullbackPartition P
    have horder : T.separatorFinset.card ≤ S.sep.separatorFinset.card + 1 :=
      edgeContraction_pullback_order_le hab S.sep
    have hroots : ∀ i, root i ∈ T.left := by
      intro i
      exact S.roots_left i
    obtain ⟨j, hj⟩ := S.branch_right
    have hfar : M.branch j ⊆ T.strictRight := by
      apply S.sep.branch_subset_strictRight_pullback P (M.branch j)
      change (cliqueModel_contract_nonroot_edge root M hab i₀ ha hb).branch j ⊆ S.sep.strictRight at hj
      rw [cliqueModel_contract_nonroot_edge_branch root M hab i₀ ha hb j] at hj
      exact hj
    by_cases hsmall : T.separatorFinset.card < r
    · exact Or.inr (Or.inl ⟨⟨T, hsmall, hroots, j, hfar⟩⟩)
    · have hX : T.separatorFinset.card = r := by
        have hquot := S.small
        omega
      have haX : a ∈ T.separatorFinset := by
        by_contra hnot
        have hle := edgeContraction_pullback_order_le_of_a_not_mem hab S.sep hnot
        change T.separatorFinset.card ≤ S.sep.separatorFinset.card at hle
        have hquot : S.sep.separatorFinset.card < r := S.small
        omega
      have hbX : b ∈ T.separatorFinset := by
        have hidx : P.index b = P.index a := by
          apply P.index_eq_of_mem
          have hblock : b ∈ P.block (P.index a) := by
            have haidx : P.index a = none := P.index_eq_of_mem (by
              simp [P, edgeContractionPartition, edgeContractionBlock])
            rw [haidx]
            simp [P, edgeContractionPartition, edgeContractionBlock]
          exact hblock
        have haSep := (T.mem_separatorFinset a).mp haX
        exact (T.mem_separatorFinset b).mpr (by
          change P.index a ∈ S.sep.left ∧ P.index a ∈ S.sep.right at haSep
          change P.index b ∈ S.sep.left ∧ P.index b ∈ S.sep.right
          rw [hidx]
          exact haSep)
      exact Or.inr (Or.inr ⟨⟨T, hX, hroots, ⟨j, hfar⟩, haX, hbX⟩⟩)

end HadwigerLean
