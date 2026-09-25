import HadwigerLean.Graph.Linkedness.DenseCoreTransfer
import HadwigerLean.Graph.Linkedness.KLinkedRooted
import HadwigerLean.Graph.Linkedness.RootedLinkedIso
import Mathlib.Tactic

/-!
# A small dense graph contains an induced core linked at every small root set
-/

namespace HadwigerLean
namespace Linkedness

/-- The two cases of Appendix D's small-core proof now have a common
rooted-linked conclusion. -/
theorem exists_small_rooted_induced_core
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 0 < k)
    (hdegree : ∀ x, 8 * k ≤ G.degree x)
    (horder : Fintype.card V ≤ 16 * k) :
    ∃ T : Finset V, T.Nonempty ∧ 2 * k ≤ T.card ∧ T.card ≤ 16 * k ∧
      (∀ Y : Finset (T : Set V), Y.card ≤ 2 * k →
        RootedLinked (G.induce (T : Set V)) Y) := by
  classical
  by_cases hG : KLinked G k
  · let T : Finset V := Finset.univ
    have hTnon : T.Nonempty := Finset.univ_nonempty
    have hTcard : T.card = Fintype.card V := by simp [T]
    have hlo : 2 * k ≤ T.card := by
      let v : V := Classical.choice inferInstance
      have hlt := G.degree_lt_card_verts v
      have hdeg := hdegree v
      omega
    refine ⟨T, hTnon, hlo, by omega, ?_⟩
    intro Y hY
    let X : Finset V := Y.image Subtype.val
    have hXcard : X.card ≤ 2 * k := by
      have heq : X.card = Y.card := by
        simpa [X] using Finset.card_image_of_injective Y Subtype.val_injective
      omega
    have hGX : RootedLinked G X :=
      rootedLinked_of_kLinked_and_order G k hG (by omega) X hXcard
    have hTset : (T : Set V) = Set.univ := by
      ext v
      simp [T]
    let eU : G.induce Set.univ ≃g G.induce (T : Set V) := {
      toEquiv := Equiv.setCongr hTset.symm
      map_rel_iff' := by
        intro x y
        rfl
    }
    let e : G ≃g G.induce (T : Set V) := G.induceUnivIso.symm.trans eU
    have hXY : ∀ v, v ∈ X ↔ e v ∈ Y := by
      intro v
      constructor
      · intro hv
        obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
        have heq : e v = u := by
          apply Subtype.ext
          change v = u.1
          exact huv.symm
        exact heq ▸ hu
      · intro hv
        exact Finset.mem_image.mpr ⟨e v, hv, by rfl⟩
    exact rootedLinked_of_iso e X Y hXY hGX
  · obtain ⟨T, hnon, hlo, hhi, hdeg, _⟩ :=
      exists_dense_induced_core_of_not_kLinked G k hdegree horder hG
    refine ⟨T, hnon, hlo, by omega, ?_⟩
    intro Y hY
    have horderT : Fintype.card (T : Set V) ≤ 7 * k := by
      simpa using hhi
    exact rootedLinked_of_five_mul_degree_seven_mul_order
      (G.induce (T : Set V)) k hdeg horderT Y hY

end Linkedness
end HadwigerLean
