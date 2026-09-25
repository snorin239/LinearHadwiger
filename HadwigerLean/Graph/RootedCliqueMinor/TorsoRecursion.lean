import HadwigerLean.Graph.RootedCliqueMinor.CriticalTorso
import HadwigerLean.Graph.RootedCliqueMinor.TorsoGluing
import HadwigerLean.Graph.RootedCliqueMinor.SpliceAttached

/-!
# Recursive torso step in the rooted-clique separator dichotomy

A full linkage from the original roots to the order-r boundary permits
either outcome of the smaller right-torso dichotomy to lift back to G.
-/

namespace HadwigerLean

theorem RootCliqueCriticalSeparation.recurse_with_linkage
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r : ℕ}
    {root : Fin r → V}
    {M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots G (Set.range root))}
    {a b : V} (C : RootCliqueCriticalSeparation G root M a b)
    [Fintype C.sep.right]
    {P : IndexedPairs (Fin r) V} (L : IndexedLinkage G P)
    (hstart : ∀ i, P.start i = root i)
    (hfinish : ∀ i, P.finish i ∈ C.sep.separatorFinset)
    (hsurj : ∀ x ∈ C.sep.separatorFinset, ∃ i, P.finish i = x)
    (hD : RootCliqueSeparatorDichotomy (G.induce C.sep.right) r) :
    Nonempty (RootAttachedCliqueModel G root) ∨
      Nonempty (RootCliqueSeparatorOutcome G root M) := by
  classical
  let S := C.sep
  obtain ⟨xroot, hxfinish, hxinj, hxrange, _⟩ :=
    C.torso_model_at_linkage_finishes L hfinish hsurj
  have hR : Set.range root ⊆ S.left := by
    rintro x ⟨i, rfl⟩
    exact C.roots_left i
  obtain ⟨j₀, hj₀⟩ := C.branch_far
  have hmeet := S.cliqueBranches_meet_right (Set.range root) hR M j₀ hj₀
  let N := S.restrictCompletedRootModel_at_roots
    (Set.range root) hR M hmeet xroot hxrange
  rcases hD xroot hxinj N with hA | hO
  · obtain ⟨A⟩ := hA
    have hleft : ∀ i, pathVertexSet (L.path i) ⊆ S.left :=
      S.linkage_to_boundary_stays_left P L
        (fun i => hstart i ▸ C.roots_left i) hsurj
    have hstartFun : P.start = root := funext hstart
    left
    exact ⟨hstartFun ▸ spliceAcrossSeparation S L xroot hxfinish hsurj hleft A⟩
  · obtain ⟨O⟩ := hO
    have hboundaryLeft : ∀ x : S.right,
        (x : V) ∈ S.left → x ∈ O.sep.left := by
      intro x hxL
      have hxR : x ∈ Set.range xroot := by
        rw [hxrange]
        exact hxL
      obtain ⟨i, hi⟩ := hxR
      exact hi ▸ O.roots_left i
    let T : VertexSeparation S.torso := {
      left := O.sep.left
      right := O.sep.right
      cover := O.sep.cover
      no_cross := by
        intro x y hxL hxNR hyR hyNL hxy
        rcases hxy with hxy | ⟨_, hyX, _⟩
        · exact O.sep.no_cross hxL hxNR hyR hyNL hxy
        · exact hyNL (hboundaryLeft y hyX)
    }
    let U := S.glueRight T hboundaryLeft
    have hsmall : U.separatorFinset.card < r := by
      have hcard := S.glueRight_separatorFinset_card T hboundaryLeft
      change U.separatorFinset.card = T.separatorFinset.card at hcard
      have hcardT : T.separatorFinset.card = O.sep.separatorFinset.card := rfl
      have hsmallO : O.sep.separatorFinset.card < r := O.small
      omega
    have hroots : ∀ i, root i ∈ U.left := by
      intro i
      exact Or.inl (C.roots_left i)
    obtain ⟨j, hj⟩ := O.branch_right
    have hfar : M.branch j ⊆ U.strictRight := by
      apply S.completed_branch_strictRight_glueRight
        (Set.range root) hR M hmeet T hboundaryLeft j
      change N.branch j ⊆ T.strictRight
      exact hj
    right
    exact ⟨⟨U, hsmall, hroots, j, hfar⟩⟩

end HadwigerLean
