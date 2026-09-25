import HadwigerLean.Graph.IndexedLinkage
import Mathlib.Tactic

/-!
# Shortcuts through a vertex outside a path
-/

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Replacing a sufficiently long segment of a path by a two-edge detour through an
outside vertex shortens the path without introducing other vertices. -/
theorem path_shortcut_of_distant_neighbors
    {G : SimpleGraph V} {s t x a b : V} (p : G.Path s t)
    (ha : a ∈ (p : G.Walk s t).support)
    (hb : b ∈ (p : G.Walk s t).support)
    (hax : G.Adj a x) (hxb : G.Adj x b)
    (hgap : (p : G.Walk s t).support.idxOf a + 3 ≤
      (p : G.Walk s t).support.idxOf b) :
    ∃ q : G.Path s t,
      pathVertexSet q ⊆ pathVertexSet p ∪ {x} ∧
      (q : G.Walk s t).length < (p : G.Walk s t).length := by
  let detour : G.Walk a b := .cons hax (.cons hxb .nil)
  let w : G.Walk s t :=
    ((p : G.Walk s t).takeUntil a ha).append
      (detour.append ((p : G.Walk s t).dropUntil b hb))
  refine ⟨w.toPath, ?_, ?_⟩
  · intro v hv
    have hvw := w.support_toPath_subset_support hv
    change v ∈ (((p : G.Walk s t).takeUntil a ha).append
      (detour.append ((p : G.Walk s t).dropUntil b hb))).support at hvw
    rw [SimpleGraph.Walk.mem_support_append_iff] at hvw
    rcases hvw with hleft | hrest
    · exact Or.inl ((p : G.Walk s t).support_takeUntil_subset_support ha hleft)
    rw [SimpleGraph.Walk.mem_support_append_iff] at hrest
    rcases hrest with hdetour | hright
    · have hmem : v = a ∨ v = x ∨ v = b := by
        simpa [detour, SimpleGraph.Walk.support_cons] using hdetour
      rcases hmem with rfl | rfl | rfl
      · exact Or.inl ha
      · exact Or.inr (by simp)
      · exact Or.inl hb
    · exact Or.inl ((p : G.Walk s t).support_dropUntil_subset_support hb hright)
  · have hwlen : w.length < (p : G.Walk s t).length := by
      simp only [w, detour, SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil,
        SimpleGraph.Walk.length_takeUntil, SimpleGraph.Walk.length_dropUntil]
      have hbidx := List.idxOf_lt_length_of_mem hb
      simp only [SimpleGraph.Walk.length_support] at hbidx
      omega
    exact lt_of_le_of_lt w.length_bypass_le_length hwlen

end Linkedness
end HadwigerLean

namespace HadwigerLean
namespace Linkedness

private theorem four_indices_have_gap (J : Finset ℕ) (hcard : 4 ≤ J.card) :
    ∃ i ∈ J, ∃ j ∈ J, i + 3 ≤ j := by
  by_contra h
  push_neg at h
  have hne : J.Nonempty := Finset.card_pos.mp (by omega)
  let m := J.min' hne
  have hm : m ∈ J := Finset.min'_mem J hne
  have hsubset : J ⊆ Finset.Icc m (m + 2) := by
    intro j hj
    have hmle : m ≤ j := Finset.min'_le J j hj
    have hgap := h m hm j hj
    exact Finset.mem_Icc.mpr ⟨hmle, by omega⟩
  have hbound := Finset.card_le_card hsubset
  have hsmall : (Finset.Icc m (m + 2)).card = 3 := by simp; omega
  omega

/-- Four neighbors on a path yield a two-edge shortcut through their common neighbor. -/
theorem path_shortcut_of_four_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {s t x : V} (p : G.Path s t)
    (hfour : 4 ≤ (G.neighborFinset x ∩
      (p : G.Walk s t).support.toFinset).card) :
    ∃ q : G.Path s t,
      pathVertexSet q ⊆ pathVertexSet p ∪ {x} ∧
      (q : G.Walk s t).length < (p : G.Walk s t).length := by
  let S : Finset V := G.neighborFinset x ∩ (p : G.Walk s t).support.toFinset
  let J : Finset ℕ := S.image (fun v => (p : G.Walk s t).support.idxOf v)
  have hinj : Set.InjOn (fun v => (p : G.Walk s t).support.idxOf v) S := by
    intro u hu v hv huv
    have hup : u ∈ (p : G.Walk s t).support := by
      exact List.mem_toFinset.mp (Finset.mem_inter.mp hu).2
    exact (List.idxOf_inj hup).mp huv
  have hJcard : 4 ≤ J.card := by
    rw [show J.card = S.card from Finset.card_image_iff.mpr hinj]
    exact hfour
  obtain ⟨i, hi, j, hj, hgap⟩ := four_indices_have_gap J hJcard
  obtain ⟨a, haS, haidx⟩ := Finset.mem_image.mp hi
  obtain ⟨b, hbS, hbidx⟩ := Finset.mem_image.mp hj
  have ha : a ∈ (p : G.Walk s t).support := by
    exact List.mem_toFinset.mp (Finset.mem_inter.mp haS).2
  have hb : b ∈ (p : G.Walk s t).support := by
    exact List.mem_toFinset.mp (Finset.mem_inter.mp hbS).2
  have hax : G.Adj a x := by
    exact (G.adj_comm x a).mp ((G.mem_neighborFinset x a).mp (Finset.mem_inter.mp haS).1)
  have hxb : G.Adj x b :=
    (G.mem_neighborFinset x b).mp (Finset.mem_inter.mp hbS).1
  exact path_shortcut_of_distant_neighbors p ha hb hax hxb (by simpa [haidx, hbidx] using hgap)

end Linkedness
end HadwigerLean
