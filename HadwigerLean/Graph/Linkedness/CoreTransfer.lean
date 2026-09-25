import HadwigerLean.Graph.RootedCliqueMinor.MengerAlternatives
import HadwigerLean.Graph.RootedCliqueMinor.ABSeparation
import HadwigerLean.Graph.Linkedness.Massed
import HadwigerLean.Graph.Linkedness.FirstHit
import Mathlib.Tactic

/-!
# Linking roots to a large linked core, or finding a small separator
-/

namespace HadwigerLean
namespace Linkedness

/-- Set Menger with a prescribed enumeration of the starts and an
arbitrary target set. -/
theorem root_set_linkage_or_separator
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {r : ℕ}
    (root : Fin r → V) (hroot : Function.Injective root)
    (J : Finset V) :
    (∃ (P : IndexedPairs (Fin r) V) (L : IndexedLinkage G P),
      (∀ i, P.start i = root i) ∧ (∀ i, P.finish i ∈ J)) ∨
    ∃ Q : Finset V, Q.card < r ∧
      SetMenger.IsABSeparator G (Finset.univ.image root) J Q := by
  classical
  let R : Finset V := Finset.univ.image root
  obtain ⟨Q, n, P, L, hQ, hAB, hcard, _⟩ :=
    SetMenger.finite_set_menger G R J
  by_cases hn : r ≤ n
  · left
    let e : Fin r ↪ Fin n := Fin.castLEEmb hn
    let P' := P.reindex e
    let L' : IndexedLinkage G P' := L.reindex e
    let F : Finset V := Finset.univ.image P'.finish
    have hFcard : F.card = r := by
      simp [F, Finset.card_image_of_injective _ L'.finish_injective]
    have hAB' : SetMenger.IsABLinkage L' R F := by
      constructor
      · intro i
        exact hAB.1 (e i)
      · intro i
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    obtain ⟨P'', L'', hstart, hfinish, _⟩ :=
      reindex_root_target_linkage root hroot F hFcard L' hAB'
    refine ⟨P'', L'', hstart, ?_⟩
    intro i
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hfinish i)
    exact hj ▸ hAB.2 (e j)
  · right
    exact ⟨Q, by omega, hQ⟩

/-- A failed full root-to-core fan gives a genuine graph separation of
order below the number of roots, with a nonempty far shore containing
an untouched core vertex. -/
theorem root_core_fan_or_separation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {r : ℕ}
    (root : Fin r → V) (hroot : Function.Injective root)
    (J : Finset V) (hJ : r ≤ J.card) :
    (∃ (P : IndexedPairs (Fin r) V) (L : IndexedLinkage G P),
      (∀ i, P.start i = root i) ∧ (∀ i, P.finish i ∈ J)) ∨
    ∃ S : VertexSeparation G,
      (∀ i, root i ∈ S.left) ∧
      (∀ j ∈ J, j ∈ S.right) ∧
      S.separatorFinset.card < r ∧
      S.strictRight.Nonempty := by
  classical
  rcases root_set_linkage_or_separator G root hroot J with hL | ⟨Q, hQcard, hAB⟩
  · exact Or.inl hL
  right
  let R : Finset V := Finset.univ.image root
  let S := SetMenger.reachableSeparation G R Q
  have hJoutside : ∃ j ∈ J, j ∉ Q := by
    by_contra h
    push Not at h
    have hsub : J ⊆ Q := by
      intro j hj
      exact h j hj
    have hcard := Finset.card_le_card hsub
    omega
  obtain ⟨j, hj, hjQ⟩ := hJoutside
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · intro i
    exact SetMenger.reachableSeparation_left_of_mem G R Q
      (root i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  · intro x hx
    exact SetMenger.reachableSeparation_right_of_ABSeparator G R Q J hAB x hx
  · simpa [S, SetMenger.reachableSeparation_separatorFinset] using hQcard
  · exact ⟨j, SetMenger.reachableSeparation_strictRight_of_ABSeparator
      G R Q J hAB j hj hjQ⟩


/-- The full fan can be trimmed so its paths avoid the core until their
last vertices. -/
theorem root_core_trimmed_fan_or_separation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {r : ℕ}
    (root : Fin r → V) (hroot : Function.Injective root)
    (J : Finset V) (hJ : r ≤ J.card) :
    (∃ (P : IndexedPairs (Fin r) V) (L : IndexedLinkage G P),
      (∀ i, P.start i = root i) ∧
      (∀ i, P.finish i ∈ J) ∧
      (∀ i x, x ∈ pathVertexSet (L.path i) → x ∈ J → x = P.finish i)) ∨
    ∃ S : VertexSeparation G,
      (∀ i, root i ∈ S.left) ∧
      (∀ j ∈ J, j ∈ S.right) ∧
      S.separatorFinset.card < r ∧
      S.strictRight.Nonempty := by
  classical
  rcases root_core_fan_or_separation G root hroot J hJ with
    ⟨P, L, hstart, hfinish⟩ | hS
  · left
    obtain ⟨P', L', hstart', hfinish', hhit, _⟩ :=
      Linkedness.IndexedLinkage.trim_to_first_hit L J hfinish
    exact ⟨P', L', (fun i => (hstart' i).trans (hstart i)), hfinish', hhit⟩
  · exact Or.inr hS

end Linkedness
end HadwigerLean
