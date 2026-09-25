import HadwigerLean.Graph.Linkedness.ShortCoreStrong
import HadwigerLean.Graph.Linkedness.InducedTransport
import HadwigerLean.Graph.VertexConnectivityIso
import Mathlib.Tactic

/-!
# Transfer of a dense linked core from a residual graph
-/

namespace HadwigerLean
namespace Linkedness

/-- When a dense graph of order at most `16k` is not `k`-linked, its
residual linked component gives an induced linked core in the original
graph. This retains both the order and degree bounds. -/
theorem exists_dense_induced_core_of_not_kLinked
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ)
    (hdegree : ∀ x, 8 * k ≤ G.degree x)
    (horder : Fintype.card V ≤ 16 * k)
    (hnot : ¬ KLinked G k) :
    ∃ T : Finset V, T.Nonempty ∧ 2 * k ≤ T.card ∧ T.card ≤ 7 * k ∧
      (∀ v : (T : Set V), 5 * k ≤ (G.induce (T : Set V)).degree v) ∧
      KLinked (G.induce (T : Set V)) k := by
  classical
  obtain ⟨P, C, S, hSnon, hSlo, hShi, hSdeg, hSlinked⟩ :=
    exists_dense_nested_induced_core_of_not_kLinked G k hdegree horder hnot
  let R : Set V := {x | x ∉ C.occupied}
  let T : Finset V := S.image (fun x : R => x.1)
  have hTset : (T : Set V) = Subtype.val '' (S : Set R) := by
    ext v
    simp [T]
  let e : (G.induce R).induce (S : Set R) ≃g G.induce (T : Set V) := {
    toEquiv := (Equiv.Set.image (fun x : R => (x : V)) (S : Set R)
      Subtype.val_injective).trans (Equiv.setCongr hTset.symm)
    map_rel_iff' := by
      intro x y
      rfl
  }
  have hTcard : T.card = S.card := by
    exact Finset.card_image_of_injective S Subtype.val_injective
  have hTnon : T.Nonempty := by
    obtain ⟨x, hx⟩ := hSnon
    exact ⟨x.1, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  have hTdeg : ∀ v : (T : Set V), 5 * k ≤ (G.induce (T : Set V)).degree v := by
    intro v
    let x := e.symm v
    have hx := hSdeg x
    rw [degree_eq_of_iso e x] at hx
    change 5 * k ≤ (G.induce (T : Set V)).degree (e (e.symm v)) at hx
    rw [e.apply_symm_apply] at hx
    exact hx
  exact ⟨T, hTnon, hTcard.symm ▸ hSlo, hTcard.symm ▸ hShi,
    hTdeg, kLinked_of_iso e k hSlinked⟩

/-- A core of order at most `7k` and minimum degree at least `5k`
links every pairing of at most `2k` prescribed roots while avoiding all
other roots. -/
theorem rootedLinked_of_five_mul_degree_seven_mul_order
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hdegree : ∀ v, 5 * k ≤ G.degree v)
    (horder : Fintype.card V ≤ 7 * k)
    (Y : Finset V) (hY : Y.card ≤ 2 * k) :
    RootedLinked G Y := by
  classical
  intro n P hP hne hPY
  have hsubset : terminalFinset P ⊆ Y := by
    intro v hv
    rcases (mem_terminalFinset P v).mp hv with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact hPY i (by simp [IndexedPairs.terminals, hi])
    · exact hPY i (by simp [IndexedPairs.terminals, hi])
  have hcard := terminalFinset_card_eq_two_mul n P hP hne
  have hcardY := Finset.card_le_card hsubset
  have hn : n ≤ k := by omega
  have hsize : Fintype.card V + 3 * k ≤ 2 * (5 * k) := by omega
  apply rooted_linkage_of_common_neighbors G Y n P hP hne hPY
  intro i
  exact hn.trans (commonOutside_card_ge_of_minDegree G k (5 * k)
    hdegree hsize Y hY (P.start i) (P.finish i))

/-- In the nonlinked case, the retained dense core is rooted linked at
every root set of size at most `2k`. -/
theorem exists_rooted_dense_induced_core_of_not_kLinked
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ)
    (hdegree : ∀ x, 8 * k ≤ G.degree x)
    (horder : Fintype.card V ≤ 16 * k)
    (hnot : ¬ KLinked G k) :
    ∃ T : Finset V, T.Nonempty ∧ 2 * k ≤ T.card ∧ T.card ≤ 7 * k ∧
      (∀ Y : Finset (T : Set V), Y.card ≤ 2 * k →
        RootedLinked (G.induce (T : Set V)) Y) := by
  classical
  obtain ⟨T, hnon, hlo, hhi, hdeg, _⟩ :=
    exists_dense_induced_core_of_not_kLinked G k hdegree horder hnot
  refine ⟨T, hnon, hlo, hhi, ?_⟩
  intro Y hY
  apply rootedLinked_of_five_mul_degree_seven_mul_order
    (G.induce (T : Set V)) k hdeg
  · simpa using hhi
  · exact hY
end Linkedness
end HadwigerLean
