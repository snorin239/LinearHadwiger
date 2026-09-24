import HadwigerLean.Graph.SimplicialElimination
import HadwigerLean.Graph.CliqueMinor
import HadwigerLean.ReedSeymour.QuotientWeight
import HadwigerLean.ReedSeymour.LPBridge

/-!
# The Reed--Seymour bound from egg decompositions

This module assembles the checked LP, quotient-coloring, and weighted-yolk
steps. The remaining combinatorial theorem is stated explicitly as a
hypothesis in `reed_seymour_bound_of_egg_decompositions`; its proof belongs in
the decomposition modules.
-/

namespace HadwigerLean

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [Nonempty I] {G : SimpleGraph V}

omit [DecidableEq V] in
/-- Every egg partition with a simplicial-elimination touching quotient
produces the weighted stable set at the Reed--Seymour constant. -/
theorem weighted_stable_of_egg_partition
    (P : ConnectedPartition G I) (w : V → ℝ)
    (hEgg : ∀ i, IsEgg G w (P.block i))
    (hElim : HasSimplicialElimination P.touchingQuotient) :
    ∃ s : Finset V, G.IsIndepSet (s : Set V) ∧
      (∑ v, w v) ≤ 2 * (cliqueMinorNumber G : ℝ) * ∑ v ∈ s, w v := by
  have hclique : P.touchingQuotient.cliqueNum ≤ cliqueMinorNumber G :=
    (cliqueNum_le_cliqueMinorNumber P.touchingQuotient).trans
      P.cliqueMinorNumber_touchingQuotient_le
  have hcolor : P.touchingQuotient.Colorable (cliqueMinorNumber G) := by
    apply (chromatic_le_iff_colorable P.touchingQuotient _).mp
    rw [hElim.chromatic_eq_cliqueNum]
    exact hclique
  exact exists_weighted_stable_finset_of_colored_egg_partition
    P w hEgg hcolor

/-- The Reed--Seymour inequality follows once the egg-decomposition theorem is
available for every nonnegative vertex weight. The hypothesis is the exact
remaining combinatorial obligation; it is not assumed elsewhere as an axiom. -/
theorem reed_seymour_bound_of_egg_decompositions
    (G : SimpleGraph V) [Nonempty V]
    (hdecomp : ∀ (w : V → ℝ), (∀ v, 0 ≤ w v) →
      ∃ n : ℕ, ∃ P : ConnectedPartition G (Fin n),
        (∀ i, IsEgg G w (P.block i)) ∧
        HasSimplicialElimination P.touchingQuotient) :
    fractionalChromaticNumber G ≤ 2 * (cliqueMinorNumber G : ℝ) := by
  apply fractionalChromaticNumber_le_twice_cliqueMinorNumber_of_weighted G
  intro w hw
  obtain ⟨n, P, hEgg, hElim⟩ := hdecomp w hw
  let v : V := Classical.choice inferInstance
  letI : Nonempty (Fin n) := ⟨Classical.choose (P.cover v)⟩
  exact weighted_stable_of_egg_partition P w hEgg hElim
/-- The empty-graph case of the Reed--Seymour bound. -/
theorem reed_seymour_bound_empty [IsEmpty V] (G : SimpleGraph V) :
    fractionalChromaticNumber G ≤ 2 * (cliqueMinorNumber G : ℝ) := by
  simp
end HadwigerLean
