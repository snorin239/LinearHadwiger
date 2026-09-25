import HadwigerLean.Inseparability.ShortestStem
import HadwigerLean.Inseparability.CheapTreeColoring
import HadwigerLean.Graph.Linkedness.RegionLinkage
import Mathlib.Tactic

/-!
# One cheap-tree extension

Add a shortest stem from a new terminal to an already constructed connected
piece. Three marked vertices pay for the stem's start, finish, and
penultimate vertex. The unmarked stem interior is anticomplete to the old
piece and reuses its two colors.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

/-- Extend a connected two-color-off-marks piece to contain one new terminal
outside it, adding at most three marked vertices. -/
theorem cheap_tree_add_outside
    (hconn : G.Connected)
    (Q₀ T₀ : Finset V) (v : V)
    (hQconn : (G.induce (Q₀ : Set V)).Connected)
    (hTQ : T₀ ⊆ Q₀)
    (hχ : chromatic (G.induce ((Q₀ \ T₀ : Finset V) : Set V)) ≤ 2)
    (hv : v ∉ Q₀) :
    ∃ Q T : Finset V,
      Q₀ ⊆ Q ∧ v ∈ Q ∧
      T₀ ⊆ T ∧ v ∈ T ∧ T ⊆ Q ∧
      T.card ≤ T₀.card + 3 ∧
      (G.induce (Q : Set V)).Connected ∧
      chromatic (G.induce ((Q \ T : Finset V) : Set V)) ≤ 2 := by
  classical
  have hQne : Q₀.Nonempty := by
    obtain ⟨z⟩ := hQconn.nonempty
    exact ⟨z.1,z.2⟩
  obtain ⟨b,p,hb,hpath,hchord,hmeet,hno⟩ :=
    exists_shortest_stem_to_set hconn Q₀ hQne v
  let Pset : Finset V := p.support.toFinset
  have hPmem (z : V) : z ∈ Pset ↔ z ∈ p.support := by
    simp [Pset]
  have hPset : (Pset : Set V) = {z | z ∈ p.support} := by
    ext z
    exact hPmem z
  have hvP : v ∈ Pset :=
    (hPmem v).mpr (by simp)
  have hbP : b ∈ Pset :=
    (hPmem b).mpr (by simp)
  have hpenP : p.penultimate ∈ Pset :=
    (hPmem _).mpr (p.getVert_mem_support (p.length - 1))
  let Q : Finset V := Q₀ ∪ Pset
  let marks : Finset V := {v,b,p.penultimate}
  let T : Finset V := T₀ ∪ marks
  have hPconn : (G.induce (Pset : Set V)).Connected := by
    rw [hPset]
    exact p.connected_induce_support
  have hQnew : (G.induce (Q : Set V)).Connected := by
    have hQset : (Q : Set V) = (Q₀ : Set V) ∪ (Pset : Set V) := by
      ext z
      simp [Q]
    rw [hQset]
    exact Linkedness.connected_induce_union_of_common hQconn hPconn hb hbP
  have hTcard : T.card ≤ T₀.card + 3 := by
    have hle := Finset.card_union_le T₀ marks
    have hmark : marks.card ≤ 3 := by
      dsimp [marks]
      have h1 := Finset.card_insert_le v ({b,p.penultimate} : Finset V)
      have h2 := Finset.card_insert_le b ({p.penultimate} : Finset V)
      simp at h1 h2 ⊢
      omega
    exact hle.trans (Nat.add_le_add_left hmark T₀.card)
  have hTsub : T ⊆ Q := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzT₀ | hzM
    · exact Finset.mem_union.mpr (Or.inl (hTQ hzT₀))
    · have hzP : z ∈ Pset := by
        simp only [marks, Finset.mem_insert, Finset.mem_singleton] at hzM
        rcases hzM with rfl | rfl | rfl
        · exact hvP
        · exact hbP
        · exact hpenP
      exact Finset.mem_union.mpr (Or.inr hzP)
  let A : Finset V := Q₀ \ T₀
  let B : Finset V := Pset \ marks
  have hPχ : chromatic (G.induce (Pset : Set V)) ≤ 2 := by
    have c := ReedSeymour.chordless_path_support_bicoloring p hpath hchord
    apply (chromatic_le_iff_colorable _ _).mpr
    rw [hPset]
    simpa using c.colorable
  have hBχ : chromatic (G.induce (B : Set V)) ≤ 2 :=
    (chromatic_induce_mono_finset G
      (S := B) (T := Pset) Finset.sdiff_subset).trans hPχ
  have hcross : ∀ {a b' : V}, a ∈ A → b' ∈ B → ¬ G.Adj a b' := by
    intro a b' ha hb' hab
    have haQ : a ∈ Q₀ := (Finset.mem_sdiff.mp ha).1
    have hbP' : b' ∈ p.support :=
      (hPmem b').mp (Finset.mem_sdiff.mp hb').1
    have hbmarks : b' ∉ marks := (Finset.mem_sdiff.mp hb').2
    have hbb : b' ≠ b := by
      intro heq
      exact hbmarks (by simp [marks,heq])
    have hbpen : b' ≠ p.penultimate := by
      intro heq
      exact hbmarks (by simp [marks,heq])
    exact hno b' hbP' hbb hbpen a haQ hab.symm
  have hABχ : chromatic (G.induce ((A ∪ B : Finset V) : Set V)) ≤ 2 :=
    chromatic_union_le_two_of_no_cross A B hχ hBχ hcross
  have hrem : Q \ T ⊆ A ∪ B := by
    intro z hz
    have hzQ := (Finset.mem_sdiff.mp hz).1
    have hzT := (Finset.mem_sdiff.mp hz).2
    rcases Finset.mem_union.mp hzQ with hzQ₀ | hzP
    · apply Finset.mem_union.mpr
      left
      exact Finset.mem_sdiff.mpr ⟨hzQ₀,by
        intro hzT₀
        exact hzT (Finset.mem_union.mpr (Or.inl hzT₀))⟩
    · apply Finset.mem_union.mpr
      right
      exact Finset.mem_sdiff.mpr ⟨hzP,by
        intro hzmarks
        exact hzT (Finset.mem_union.mpr (Or.inr hzmarks))⟩
  refine ⟨Q,T,Finset.subset_union_left,hvP |> Finset.mem_union_right Q₀,
    Finset.subset_union_left,?_,hTsub,hTcard,hQnew,?_⟩
  · exact Finset.mem_union.mpr (Or.inr (by simp [marks]))
  · exact (chromatic_induce_mono_finset G hrem).trans hABχ

end Inseparability
end HadwigerLean


