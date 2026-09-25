import HadwigerLean.Graph.RootedCliqueMinor.TerminalAttached
import HadwigerLean.Graph.RootedCliqueMinor.ABSeparation

/-!
# Terminal branch of the rooted-clique separator dichotomy

If every model branch avoiding the roots is a singleton, then r of those
vertices form an actual clique. Menger either links all roots to it or
separates an entire singleton model branch from the roots.
-/

namespace HadwigerLean

theorem rootClique_terminal_dichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r : ℕ}
    (root : Fin r → V) (hroot : Function.Injective root)
    (M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots G (Set.range root)))
    (hsingle : ∀ i : Fin (2 * r),
      Disjoint (M.branch i) (Set.range root) →
        ∃ x : V, M.branch i = {x}) :
    Nonempty (RootAttachedCliqueModel G root) ∨
      Nonempty (RootCliqueSeparatorOutcome G root M) := by
  classical
  obtain ⟨e, he⟩ := exists_root_avoiding_branches root M
  let q : Fin r → V := fun i => M.representative (e i)
  have hqinj : Function.Injective q :=
    M.representative_injective.comp e.injective
  have hsingleton : ∀ i : Fin r, M.branch (e i) = {q i} := by
    intro i
    obtain ⟨x, hx⟩ := hsingle (e i) (he i)
    have hqx : q i = x := by
      have hmem := M.representative_mem (e i)
      simpa [q, hx] using hmem
    simpa [q, hqx] using hx
  let Q : Finset V := Finset.univ.image q
  have hQcard : Q.card = r := by
    simp [Q, Finset.card_image_of_injective _ hqinj]
  have hQaway : Disjoint (Q : Set V) (Set.range root) := by
    apply Set.disjoint_left.mpr
    intro x hx hR
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact (Set.disjoint_left.mp (he i))
      (M.representative_mem (e i)) hR
  have hclique : ∀ ⦃u v : V⦄, u ∈ Q → v ∈ Q →
      u ≠ v → G.Adj u v := by
    intro u v hu hv huv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
    have hij : i ≠ j := by
      intro h
      exact huv (congrArg q h)
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      cliqueModel_adjacent_of_avoids_roots M (e.injective.ne hij) (he i)
    have hxi : x = q i := by simpa [hsingleton i] using hx
    have hyj : y = q j := by simpa [hsingleton j] using hy
    simpa [hxi, hyj] using hxy
  rcases root_target_linkage_or_separator G root hroot Q hQcard with hL | hT
  · obtain ⟨P, L, hstart, hfinish, _⟩ := hL
    left
    refine ⟨RootAttachedCliqueModel.ofLinkageToClique L hstart ?_ ?_⟩
    · intro i hR
      exact (Set.disjoint_left.mp hQaway) (hfinish i) hR
    · intro i j hij
      apply hclique (hfinish i) (hfinish j)
      exact L.finish_injective.ne hij
  · obtain ⟨T, hTcard, hAB⟩ := hT
    let R : Finset V := Finset.univ.image root
    let S := SetMenger.reachableSeparation G R T
    have hroots : ∀ i, root i ∈ S.left := by
      intro i
      exact SetMenger.reachableSeparation_left_of_mem G R T
        (root i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    have hpick : T.card < Q.card := by omega
    obtain ⟨x, hxQ, hxT⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card hpick
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hxQ
    have hxfar : q i ∈ S.strictRight :=
      SetMenger.reachableSeparation_strictRight_of_ABSeparator
        G R T Q hAB (q i) (hi ▸ hxQ) (hi ▸ hxT)
    have hfar : M.branch (e i) ⊆ S.strictRight := by
      intro v hv
      have hvq : v = q i := by simpa [hsingleton i] using hv
      exact hvq ▸ hxfar
    have hsmall : S.separatorFinset.card < r := by
      change (SetMenger.reachableSeparation G R T).separatorFinset.card < r
      rw [SetMenger.reachableSeparation_separatorFinset]
      exact hTcard
    right
    exact ⟨⟨S, hsmall, hroots, e i, hfar⟩⟩

end HadwigerLean
