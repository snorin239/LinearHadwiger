import HadwigerLean.Graph.RootedDensity.NumericalClosure
import HadwigerLean.Graph.RootedDensity.UniversalNested

/-! Ambient form of the Appendix F.2 universal-subgraph contradiction. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- The F.5 neighborhood bounds force an induced H-universal subgraph. -/
theorem exists_universal_induced_of_F5
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (c : ℝ) (hc : 1 < c) (hforces : DensityForcesMinor.{u,v} H c)
    (hh : 3 ≤ Fintype.card W)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (horder : (Fintype.card V : ℝ) ≤
      24 * c + 10000 * (Fintype.card W : ℝ) + 1)
    (hmin : ∀ x : V,
      12 * c + 4999 * (Fintype.card W : ℝ) ≤ (G.degree x : ℝ)) :
    ∃ S : Finset V, Universal (G.induce (S : Set V)) H := by
  exact exists_universal_induced_of_universal_or_induced G H
    (universal_or_universal_induced_of_F5 H c hc hforces hh G horder hmin)

/-- Apply the numerical closure to a dense induced neighborhood in an
ambient graph, and flatten the resulting induced universal subgraph. -/
theorem exists_ambient_universal_induced_of_F5
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (c : ℝ) (hc : 1 < c) (hforces : DensityForcesMinor.{u,v} H c)
    (hh : 3 ≤ Fintype.card W)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (hDne : D.Nonempty)
    (horder : (D.card : ℝ) ≤
      24 * c + 10000 * (Fintype.card W : ℝ) + 1)
    (hmin : ∀ x : ↥(D : Set V),
      12 * c + 4999 * (Fintype.card W : ℝ) ≤
        ((G.induce (D : Set V)).degree x : ℝ)) :
    ∃ S : Finset V, Universal (G.induce (S : Set V)) H := by
  classical
  letI : Nonempty ↥(D : Set V) := by
    obtain ⟨x, hx⟩ := hDne
    exact ⟨⟨x, hx⟩⟩
  have horder' : (Fintype.card ↥(D : Set V) : ℝ) ≤
      24 * c + 10000 * (Fintype.card W : ℝ) + 1 := by
    simpa using horder
  obtain ⟨N, hN⟩ := exists_universal_induced_of_F5 H c hc hforces hh
    (G.induce (D : Set V)) horder' hmin
  exact ⟨N.image Subtype.val,
    Universal.induce_image_of_nested G H (D : Set V) N hN⟩

end HadwigerLean.RootedDensity
