import HadwigerLean.Inseparability.ModelTrimmingStage
import HadwigerLean.Inseparability.StageNormalizeRoots
import HadwigerLean.Graph.CliqueMinorOrder
import Mathlib.Tactic

/-!
# Iterating the sequential chromatic-inseparability stage

The geometric part of one stage constructs a raw rooted clique model and a
connected chromatic region. Cheap-tree trimming and restoration close that
stage, and induction eventually yields the forbidden clique minor.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem chromatic_separable_of_raw_stage_extension
    (G : SimpleGraph V) (t r x k m q : ℕ)
    (b : ℕ → ℕ)
    (hminor : ¬ HasCliqueMinor G t)
    (horder : t ≤ r * x)
    (hzero : b 0 = 0)
    (hbound : ∀ u, u ≤ r → b u ≤ b r)
    (hlocal : ∀ X : Finset V, X.card ≤ 3 * b r →
      chromatic (G.induce (X : Set V)) ≤ q)
    (hk : 0 < k)
    (hbaseBudget : 12 * k ≤ m)
    (hχ : q + 2 * (r * x) + 7 * k ≤ chromatic G)
    (hreserve : q + 2 * (r * x) + 6 * k ≤ m / 2)
    (hbudget : m / 2 + k ≤ m)
    (hraw : ¬ Bootstrap.ChromaticSeparable G m →
      ∀ u, u < r →
        (S : StageState G (u * x) k (m / 2) (b u)) →
        (∀ i, S.root i ∈ S.core) →
        (∀ i, S.root i ∈ S.region) →
        Nonempty (StageState G ((u + 1) * x) k m (b (u + 1)))) :
    Bootstrap.ChromaticSeparable G m := by
  classical
  by_contra hinsep
  have hstage : ∀ u, u ≤ r →
      Nonempty (StageState G (u * x) k (m / 2) (b u)) := by
    intro u
    induction u with
    | zero =>
      intro _
      simpa [hzero] using
        exists_stage_zero G k m hk (by omega : 7 * k ≤ chromatic G)
          hbaseBudget
    | succ u ih =>
      intro hu
      obtain ⟨S⟩ := ih (by omega)
      let S₀ := S.normalizeRoots
      obtain ⟨R⟩ := hraw hinsep u (by omega) S₀
        (fun i => S.normalizeRoots_root_in_core i)
        (fun i => S.normalizeRoots_root_in_region i)
      have hlocalR : ∀ X : Finset V, X.card ≤ 3 * R.core.card →
          chromatic (G.induce (X : Set V)) ≤ q := by
        intro X hX
        apply hlocal X
        have hcore := R.core_card_le
        have hb := hbound (u + 1) (by omega)
        nlinarith
      have hχR : q + 2 * ((u + 1) * x) + 7 * k ≤ chromatic G := by
        have hux : (u + 1) * x ≤ r * x := Nat.mul_le_mul_right x (by omega)
        omega
      have hreserveR : q + 2 * ((u + 1) * x) + 6 * k ≤ m / 2 := by
        have hux : (u + 1) * x ≤ r * x := Nat.mul_le_mul_right x (by omega)
        omega
      exact R.exists_trimmed_and_restored_auto
        hlocalR hk hχR hreserveR hbudget hinsep
  obtain ⟨S⟩ := hstage r le_rfl
  have hclique : HasCliqueMinor G (r * x) :=
    ⟨S.model.toMinorModel⟩
  exact hminor (hasCliqueMinor_of_le hclique horder)

end Inseparability
end HadwigerLean


