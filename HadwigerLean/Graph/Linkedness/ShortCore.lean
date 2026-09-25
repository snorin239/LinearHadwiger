import HadwigerLean.Graph.Linkedness.Theorem
import Mathlib.Tactic

/-!
# Seven-edge path count for the linked small core

The small-core proof uses short paths only to bound the number of
vertices occupied outside its prescribed terminal set. This module
records that count independently of the later maximal-path argument.
-/

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A simple path of length at most seven whose distinct endpoints are
terminals occupies at most six additional vertices. -/
theorem short_path_nonterminal_card_le_six
    {G : SimpleGraph V} {s t : V}
    (X : Finset V) (p : G.Path s t)
    (hs : s ∈ X) (ht : t ∈ X) (hne : s ≠ t)
    (hlen : (p : G.Walk s t).length ≤ 7) :
    (((p : G.Walk s t).support.toFinset) \ X).card ≤ 6 := by
  classical
  let W : Finset V := (p : G.Walk s t).support.toFinset
  have hWcard : W.card = (p : G.Walk s t).length + 1 := by
    change ((p : G.Walk s t).support.toFinset).card =
      (p : G.Walk s t).length + 1
    rw [List.toFinset_card_of_nodup p.property.support_nodup]
    exact (p : G.Walk s t).length_support
  have hpair : ({s, t} : Finset V) ⊆ W ∩ X := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨by simpa [W] using
        (p : G.Walk s t).start_mem_support, hs⟩
    · exact Finset.mem_inter.mpr ⟨by simpa [W] using
        (p : G.Walk s t).end_mem_support, ht⟩
  have htwo : 2 ≤ (W ∩ X).card := by
    have hcard : ({s, t} : Finset V).card = 2 := by simp [hne]
    rw [← hcard]
    exact Finset.card_le_card hpair
  have hsplit := Finset.card_sdiff_add_card_inter W X
  change (W \ X).card ≤ 6
  omega

end Linkedness
end HadwigerLean
