import HadwigerLean.Graph.RootedDensity.F5FromFB
import HadwigerLean.Graph.RootedDensity.NumericalFinal

/-! The common-neighbor output of F.b already gives the F.2 contradiction. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- A vertex with the degree and edge common-neighbor bounds of Appendix
F.b produces an induced graph universal for the target. The root-edge
bound only counts total common neighbors and is therefore weaker than the
outside-root bound stated in F.b. -/
theorem exists_ambient_universal_induced_of_FB
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (c : ℝ) (hc : 1 < c) (hforces : DensityForcesMinor.{u,v} H c)
    (hh : 3 ≤ Fintype.card W)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hX : X.card ≤ Fintype.card W)
    (z : V)
    (hdeg : (G.degree z : ℝ) ≤
      2 * (12 * c + 5000 * (Fintype.card W : ℝ)))
    (hnonisolated : ∃ w : V, G.Adj z w)
    (hout : ∀ w : V, G.Adj z w → w ∉ X →
      Nat.floor (12 * c + 5000 * (Fintype.card W : ℝ)) ≤
        Fintype.card (G.commonNeighbors z w))
    (hroot : ∀ w : V, G.Adj z w → w ∈ X →
      Nat.floor (12 * c + 5000 * (Fintype.card W : ℝ)) ≤
        Fintype.card (G.commonNeighbors z w) + (X.erase w).card) :
    ∃ S : Finset V, Universal (G.induce (S : Set V)) H := by
  classical
  let α : ℝ := 12 * c + 5000 * (Fintype.card W : ℝ)
  let D : Finset V := closedNeighborhoodFinset G z
  obtain ⟨hne, horder, hmin⟩ :=
    closedNeighborhood_F5_of_FB G X (Fintype.card W) α hX (by omega)
      z hdeg hnonisolated hout hroot
  apply exists_ambient_universal_induced_of_F5 H c hc hforces hh G D hne
  · dsimp [α] at horder
    nlinarith
  · intro x
    have hx := hmin x
    dsimp [α] at hx
    nlinarith

end HadwigerLean.RootedDensity
