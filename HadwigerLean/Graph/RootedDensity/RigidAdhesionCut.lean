import HadwigerLean.Graph.Linkedness.RigidMinCut
import Mathlib.Tactic

/-! The Menger dichotomy for a rigid shore whose adhesion may exceed the
number of roots. -/

namespace HadwigerLean.RootedDensity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A near-shore fan reaches the entire root set, or a smaller separator has
paths from each of its boundary vertices into the original adhesion.  The
adhesion is allowed to be larger than the root set. -/
theorem rigid_full_fan_or_saturated_cut_ge
    (G : SimpleGraph V) (S : VertexSeparation G) [Fintype S.left]
    (X : Finset V) (hX : (X : Set V) ⊆ S.left)
    (horder : X.card ≤ S.separatorFinset.card) :
    (∃ (n : ℕ) (P : IndexedPairs (Fin n) S.left)
        (_ : IndexedLinkage (G.induce S.left) P),
      n = X.card ∧
      Finset.univ.image P.start = Linkedness.torsoRootFinset S X ∧
      (∀ i, P.finish i ∈ Linkedness.torsoBoundaryFinset G S)) ∨
    ∃ (n : ℕ) (T : VertexSeparation (G.induce S.left))
      (C : IndexedPairs (Fin n) S.left)
      (F : IndexedLinkage (G.induce S.left) C),
      T.separatorFinset.card = n ∧ n < X.card ∧
      (Linkedness.torsoRootFinset S X : Set S.left) ⊆ T.left ∧
      (∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right) ∧
      Finset.univ.image C.start = T.separatorFinset ∧
      (∀ i, (C.finish i : V) ∈ S.separator) ∧
      (∀ i x, x ∈ pathVertexSet (F.path i) → x ∈ T.right) ∧
      (∀ i x, x ∈ pathVertexSet (F.path i) →
        (x : V) ∈ S.right → x = C.finish i) := by
  classical
  let Y := Linkedness.torsoRootFinset S X
  let J := Linkedness.torsoBoundaryFinset G S
  have hYcard : Y.card = X.card := Linkedness.torsoRootFinset_card S X hX
  have hJcard : X.card ≤ J.card := by
    rw [Linkedness.torsoBoundaryFinset_card_eq]
    exact horder
  obtain ⟨Q,n,P,L,hQ,hAB,hQcard,_⟩ :=
    SetMenger.finite_set_menger (G.induce S.left) Y J
  have hnle : n ≤ X.card := by
    have hstart : Finset.univ.image P.start ⊆ Y := by
      intro x hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact hAB.1 i
    have hc : (Finset.univ.image P.start).card = n := by
      simp [Finset.card_image_of_injective _ L.start_injective]
    have hle := Finset.card_le_card hstart
    omega
  by_cases hn : n = X.card
  · left
    have hstart : Finset.univ.image P.start = Y := by
      have hsub : Finset.univ.image P.start ⊆ Y := by
        intro x hx
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
        exact hAB.1 i
      apply Finset.eq_of_subset_of_card_le hsub
      have hc : (Finset.univ.image P.start).card = n := by
        simp [Finset.card_image_of_injective _ L.start_injective]
      omega
    exact ⟨n,P,L,hn,hstart,hAB.2⟩
  · right
    have hnlt : n < X.card := by omega
    let T := SetMenger.reachableSeparation (G.induce S.left) Y Q
    have hJright : ∀ x ∈ J, x ∈ T.right := by
      intro x hx
      exact SetMenger.reachableSeparation_right_of_ABSeparator
        (G.induce S.left) Y Q J hQ x hx
    have hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right := by
      intro u hu
      exact hJright u ((Linkedness.mem_torsoBoundaryFinset G S u).mpr hu)
    have hTcard : T.separatorFinset.card = n := by
      simpa [T, SetMenger.reachableSeparation_separatorFinset] using hQcard
    have hhit : ∀ i, ∃ x ∈ T.separatorFinset,
        x ∈ pathVertexSet (L.path i) := by
      intro i
      obtain ⟨q,hqQ,hqPath⟩ :=
        hQ (P.start i) (hAB.1 i) (P.finish i) (hAB.2 i) (L.path i)
      exact ⟨q, by simpa [T, SetMenger.reachableSeparation_separatorFinset] using hqQ,
        hqPath⟩
    obtain ⟨C,F,hCstart,hCfinish,hFright,hFfirst⟩ :=
      Linkedness.boundary_core_fan_in_right T J hJright P L hAB.2 hhit hTcard
    have hrootT : (Y : Set S.left) ⊆ T.left := by
      intro x hx
      exact SetMenger.reachableSeparation_left_of_mem
        (G.induce S.left) Y Q x hx
    refine ⟨n,T,C,F,hTcard,hnlt,hrootT,hBoundary,hCstart,?_,hFright,?_⟩
    · intro i
      exact ⟨(C.finish i).property,
        (Linkedness.mem_torsoBoundaryFinset G S (C.finish i)).mp (hCfinish i)⟩
    · intro i x hx hxS
      exact hFfirst i x hx ((Linkedness.mem_torsoBoundaryFinset G S x).mpr hxS)

end HadwigerLean.RootedDensity
