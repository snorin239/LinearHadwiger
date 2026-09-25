import HadwigerLean.Graph.RootedDensity.UniversalInduced
import HadwigerLean.Graph.Linkedness.Massed

/-! Graph-order minimality excludes isolated outside vertices in Appendix F.b. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- If every one-vertex massed deletion is universal, a nonuniversal
massed pair has no isolated vertex outside its root set. -/
theorem outside_has_neighbor_of_universal_vertex_deletions
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (α : ℝ) (hα : 0 ≤ α)
    (hm : MassedPair G (X : Set V) α)
    (hbad : ¬ UniversalAt G H X)
    (hminimal : ∀ z : V, z ∉ X →
      let S : Set V := {v : V | v ≠ z}
      letI : Fintype S := Fintype.ofFinite S
      let Y : Finset S := Finset.univ.filter (fun u : S => (u : V) ∈ X)
      MassedPair (G.induce S) (Y : Set S) α →
        UniversalAt (G.induce S) H Y) :
    ∀ z ∉ X, ∃ w, G.Adj z w := by
  classical
  intro z hz
  by_contra hnone
  push Not at hnone
  let S : Set V := {v | v ≠ z}
  letI : Fintype S := Fintype.ofFinite S
  let Y : Finset S := Finset.univ.filter (fun u : S => (u : V) ∈ X)
  have hmass : MassedPair (G.induce S) (Y : Set S) α := by
    have h := Linkedness.massed_delete_isolated G X α hα hm z hz hnone
    simpa [S,Y] using h
  have huni : UniversalAt (G.induce S) H Y :=
    hminimal z hz (by simpa [S,Y] using hmass)
  have hXS : (X : Set V) ⊆ S := by
    intro x hx heq
    exact hz (heq ▸ hx)
  have hY : ∀ y : S, y ∈ Y ↔ (y : V) ∈ X := by
    intro y
    simp [Y]
  exact hbad (UniversalAt.of_induce G H S X Y hXS hY huni)

end HadwigerLean.RootedDensity
