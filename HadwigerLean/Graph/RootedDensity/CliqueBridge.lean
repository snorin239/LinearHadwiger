import HadwigerLean.Graph.RootedDensity.Universal
import HadwigerLean.Graph.RootedCliqueMinor.Dichotomy
import HadwigerLean.Graph.CliqueDensity.Theorem
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-! A rooted clique model also realizes any smaller edge set on its labels. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- Kawarabayashi's rooted clique theorem immediately realizes any target
on the same number of labels. -/
theorem rootedMinor_of_connected_cliqueMinor
    {W : Type u} {V : Type v} [Fintype W] [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V)
    (hconn : VertexConnected G (Fintype.card W))
    (hminor : HasCliqueMinor G (2 * Fintype.card W))
    (root : W → V) (hroot : Function.Injective root) :
    Nonempty (RootedMinorModel H G root) := by
  classical
  let e : W ≃ Fin (Fintype.card W) := Fintype.equivFin W
  let rf : Fin (Fintype.card W) → V := root ∘ e.symm
  have hrfin : Function.Injective rf := by
    intro i j hij
    exact e.symm.injective (hroot hij)
  obtain ⟨M⟩ := rootedCliqueMinor_of_connected_cliqueMinor hconn hminor rf hrfin
  refine ⟨{
    toMinorModel := {
      branch := fun w => M.branch (e w)
      connected := fun w => M.connected (e w)
      disjoint := ?_
      adjacent := ?_
    }
    root_mem := ?_
  }⟩
  · intro i j hij
    apply M.disjoint
    exact e.injective.ne hij
  · intro i j hij
    apply M.adjacent
    simpa using e.injective.ne (H.ne_of_adj hij)
  · intro i
    simpa [rf] using M.root_mem (e i)

/-- A universal, unconditional density-to-rooted-target bound obtained by
first forcing a clique minor. The sharper linear-in-`h` threshold of
Appendix F requires the massed-pair argument. -/
theorem rootedMinor_of_clique_density
    {W : Type u} {V : Type v} [Fintype W] [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V)
    (hh : 1 ≤ Fintype.card W)
    (hconn : VertexConnected G (Fintype.card W))
    (hdense : 60 * (Fintype.card W : ℝ) *
      Real.sqrt (Real.log (2 * (Fintype.card W : ℝ))) ≤ edgeDensity G)
    (root : W → V) (hroot : Function.Injective root) :
    Nonempty (RootedMinorModel H G root) := by
  classical
  have hr : 2 ≤ 2 * Fintype.card W := by omega
  have hkt : 30 * ((2 * Fintype.card W : ℕ) : ℝ) *
      Real.sqrt (Real.log ((2 * Fintype.card W : ℕ) : ℝ)) ≤ edgeDensity G := by
    convert hdense using 1 <;> push_cast <;> ring
  have hm : HasCliqueMinor G (2 * Fintype.card W) :=
    hasCliqueMinor_of_edgeDensity_ge G (2 * Fintype.card W) hr hkt
  exact rootedMinor_of_connected_cliqueMinor H G hconn hm root hroot
end HadwigerLean.RootedDensity


