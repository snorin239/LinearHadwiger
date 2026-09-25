import HadwigerLean.Graph.RootedDensity.CliqueBridge
import HadwigerLean.Graph.CliqueMinorOrder
import Mathlib.Tactic

/-! The unconditional complete-minor route to arbitrary-target rooted universality. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- A complete minor of order twice the target order roots every induced
subtarget at every prescribed root set of size at most that order. -/
theorem universalAt_of_connected_cliqueMinor
    {W : Type v} {V : Type u} [Fintype W] [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V) (X : Finset V)
    (hconn : VertexConnected G (Fintype.card W))
    (hminor : HasCliqueMinor G (2 * Fintype.card W)) :
    UniversalAt G H X := by
  intro Y root hinj _
  have hk : Fintype.card ↥(Y : Set W) ≤ Fintype.card W := by
    simpa using Y.card_le_univ
  have hconnY : VertexConnected G (Fintype.card ↥(Y : Set W)) :=
    hconn.of_le hk
  have hminorY : HasCliqueMinor G (2 * Fintype.card ↥(Y : Set W)) :=
    hasCliqueMinor_of_le hminor (by omega)
  exact rootedMinor_of_connected_cliqueMinor (H.induce (Y : Set W)) G
    hconnY hminorY root hinj

/-- The KT density bound is an unconditional rooted-density threshold for
every finite target. It is weaker than Appendix F's linear-in-`h` bound. -/
theorem rootedDensity_of_clique_density
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (hh : 1 ≤ Fintype.card W) :
    RootedDensityConclusion.{u,v} H
      (60 * (Fintype.card W : ℝ) *
        Real.sqrt (Real.log (2 * (Fintype.card W : ℝ)))) := by
  intro V _ G X _ hconn hedge
  classical
  have hn : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast (Nat.zero_lt_of_lt hconn.order_gt)
  have hdense : 60 * (Fintype.card W : ℝ) *
      Real.sqrt (Real.log (2 * (Fintype.card W : ℝ))) ≤ edgeDensity G := by
    unfold edgeDensity
    exact (le_div_iff₀ hn).2 hedge
  have hr : 2 ≤ 2 * Fintype.card W := by omega
  have hkt : 30 * ((2 * Fintype.card W : ℕ) : ℝ) *
      Real.sqrt (Real.log ((2 * Fintype.card W : ℕ) : ℝ)) ≤ edgeDensity G := by
    convert hdense using 1 <;> push_cast <;> ring
  have hm : HasCliqueMinor G (2 * Fintype.card W) :=
    hasCliqueMinor_of_edgeDensity_ge G (2 * Fintype.card W) hr hkt
  exact universalAt_of_connected_cliqueMinor H G X hconn hm

end HadwigerLean.RootedDensity
