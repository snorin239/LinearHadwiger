import HadwigerLean.Graph.RootedDensity.UniversalFarFan
import HadwigerLean.Graph.SetMengerTheorem
import Mathlib.Tactic

/-! The Menger dichotomy at an H-universal induced core, Appendix F.c. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- From an H-universal induced core, either every prescribed partial
target model can be rooted at `X`, or a smaller adhesion separates `X`
from a proper far shore universal at its boundary. -/
theorem universalAt_or_rigid_shore_of_universal_core
    {W : Type u} [Fintype W] {V : Type v} [Fintype V] [DecidableEq V]
    (H : SimpleGraph W) (G : SimpleGraph V)
    (X J : Finset V) (hX : X.card ≤ Fintype.card W)
    (hW : 0 < Fintype.card W)
    (hcore : Universal (G.induce (J : Set V)) H) :
    UniversalAt G H X ∨
      ∃ S : VertexSeparation G,
        (X : Set V) ⊆ S.left ∧
        S.strictRight.Nonempty ∧
        Nat.card S.separator < X.card ∧
        (letI : Fintype S.right := Fintype.ofFinite S.right;
         UniversalAt (G.induce S.right) H
          (Linkedness.separationBoundaryFinset S)) := by
  classical
  have hJ : X.card ≤ J.card := by
    have hc : Fintype.card W ≤ J.card := by simpa using hcore.1
    omega
  obtain ⟨Q, n, P, L, hQ, hAB, hcard, _⟩ :=
    SetMenger.finite_set_menger G X J
  by_cases hn : X.card ≤ n
  · let e := Fin.castLEEmb hn
    let C : IndexedPairs (Fin X.card) V := P.reindex e
    let F : IndexedLinkage G C := L.reindex e
    have hfinish : ∀ i, C.finish i ∈ J := fun i => hAB.2 (e i)
    have hstartsSubset : Finset.univ.image C.start ⊆ X := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hAB.1 (e i)
    have hstartsCard : (Finset.univ.image C.start).card = X.card := by
      rw [Finset.card_image_of_injective _ F.start_injective]
      simp
    have hstarts : Finset.univ.image C.start = X := by
      apply Finset.eq_of_subset_of_card_le hstartsSubset
      omega
    left
    have huni := universalAt_of_universal_core_and_full_fan_image
      H G J hcore hW C F hfinish
    simpa only [hstarts] using huni
  · have hn' : n < X.card := by omega
    let S := SetMenger.reachableSeparation G X Q
    have hJoutside : ∃ j ∈ J, j ∉ Q := by
      by_contra h
      push Not at h
      have hsub : J ⊆ Q := by
        intro j hj
        exact h j hj
      have hc := Finset.card_le_card hsub
      omega
    obtain ⟨j, hj, hjQ⟩ := hJoutside
    have hJright : ∀ x ∈ J, x ∈ S.right := by
      intro x hx
      exact SetMenger.reachableSeparation_right_of_ABSeparator G X Q J hQ x hx
    have hhit : ∀ i, ∃ x ∈ S.separatorFinset,
        x ∈ pathVertexSet (L.path i) := by
      intro i
      obtain ⟨x,hxQ,hxP⟩ := hQ (P.start i) (hAB.1 i)
        (P.finish i) (hAB.2 i) (L.path i)
      exact ⟨x,SetMenger.reachableSeparation_separatorFinset G X Q ▸ hxQ,hxP⟩
    have hScard : S.separatorFinset.card = n := by
      simpa [S, SetMenger.reachableSeparation_separatorFinset] using hcard
    obtain ⟨C,F,hstarts,hfinish,hpathRight,_⟩ :=
      Linkedness.boundary_core_fan_in_right S J hJright P L hAB.2 hhit hScard
    letI : Fintype S.right := Fintype.ofFinite S.right
    have hfarUni : UniversalAt (G.induce S.right) H
        (Linkedness.separationBoundaryFinset S) :=
      universalAt_right_of_boundary_core_fan S H hW J hJright hcore
        C F hstarts hfinish hpathRight
    right
    refine ⟨S, ?_, ?_, ?_, hfarUni⟩
    · intro x hx
      exact SetMenger.reachableSeparation_left_of_mem G X Q x hx
    · exact ⟨j, SetMenger.reachableSeparation_strictRight_of_ABSeparator
        G X Q J hQ j hj hjQ⟩
    · have hsep : Nat.card S.separator = S.separatorFinset.card := by
        simp [VertexSeparation.separatorFinset]
      rw [hsep, hScard]
      omega

end HadwigerLean.RootedDensity

