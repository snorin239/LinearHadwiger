import HadwigerLean.Graph.Linkedness.SmallRootedCore
import HadwigerLean.Graph.Linkedness.NestedRootedTransport
import Mathlib.Tactic

/-!
# A rooted-linked core in an ambient graph
-/

namespace HadwigerLean
namespace Linkedness

/-- A small dense induced graph supplies an ambient induced core that
links every pairing of up to `2k` arrival roots. -/
theorem exists_ambient_small_rooted_core
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : S.Nonempty)
    (k : ℕ) (hk : 0 < k)
    (horder : S.card ≤ 16 * k)
    (hdegree : ∀ v : (S : Set V),
      8 * k ≤ (G.induce (S : Set V)).degree v) :
    ∃ J : Finset V, J.Nonempty ∧ J ⊆ S ∧
      2 * k ≤ J.card ∧ J.card ≤ 16 * k ∧
      (∀ Y : Finset (J : Set V), Y.card ≤ 2 * k →
        RootedLinked (G.induce (J : Set V)) Y) := by
  classical
  obtain ⟨v,hv⟩ := hS
  letI : Nonempty (S : Set V) := ⟨⟨v,hv⟩⟩
  have horder' : Fintype.card (S : Set V) ≤ 16 * k := by
    simpa using horder
  obtain ⟨T,hTnon,hTlo,hThi,hTrooted⟩ :=
    exists_small_rooted_induced_core (G.induce (S : Set V)) k hk
      hdegree horder'
  let J : Finset V := T.image Subtype.val
  have hJnon : J.Nonempty := by
    obtain ⟨x,hx⟩ := hTnon
    exact ⟨x.1, Finset.mem_image.mpr ⟨x,hx,rfl⟩⟩
  have hJsub : J ⊆ S := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  have hJcard : J.card = T.card := by
    exact Finset.card_image_of_injective T Subtype.val_injective
  have hJrooted : ∀ Y : Finset (J : Set V), Y.card ≤ 2 * k →
      RootedLinked (G.induce (J : Set V)) Y := by
    exact rootedLinked_induce_image_of_nested G (S : Set V) T k hTrooted
  exact ⟨J,hJnon,hJsub,hJcard.symm ▸ hTlo,
    hJcard.symm ▸ hThi,hJrooted⟩

end Linkedness
end HadwigerLean
