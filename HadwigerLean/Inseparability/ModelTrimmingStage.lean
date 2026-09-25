import HadwigerLean.Inseparability.ModelTrimming
import HadwigerLean.Inseparability.StageRestoreFromColor
import HadwigerLean.Inseparability.StageNormalizeRoots
import Mathlib.Tactic

/-!
# Trim and restore a sequential inseparability stage

This packages the last step of the nonzero stage: cheap-tree trimming gives a
low-chromatic model, additive GN finds a highly chromatic connected region
disjoint from it, and chromatic inseparability joins the old and new regions.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {s k m coreBound q : ℕ}

/-- Abstract final step of Section 7.4. The model and its core have already
been assembled. The local chromatic bound is needed only on sets of size at
most three times the core. -/
theorem StageState.exists_trimmed_and_restored
    (S : StageState G s k m coreBound)
    (hrootcore : ∀ i, S.root i ∈ S.core)
    (hrootregion : ∀ i, S.root i ∈ S.region)
    (hlocal : ∀ X : Finset V, X.card ≤ 3 * S.core.card →
      chromatic (G.induce (X : Set V)) ≤ q)
    (hk : 0 < k)
    (hχ : q + 2 * s + 7 * k ≤ chromatic G)
    (hreserve : q + 2 * s + 6 * k ≤ m / 2)
    (hbudget : m / 2 + k ≤ m)
    (hinsep : ¬ Bootstrap.ChromaticSeparable G m) :
    Nonempty (StageState G s k (m / 2) coreBound) := by
  classical
  obtain ⟨Q,T,hQsub,hQconn,hcoreQ,hTQ,hXcard,hmodelχ⟩ :=
    exists_cheap_branch_sets S.root S.model S.core hrootcore
  let S' : StageState G s k m coreBound :=
    stage_of_restricted_model S hrootcore hrootregion Q
      hQsub hQconn hcoreQ
  let A : Finset V := (Finset.univ : Finset (Fin s)).biUnion Q
  let X : Finset V := (Finset.univ : Finset (Fin s)).biUnion T
  have hA : S'.model.toMinorModel.vertices = (A : Set V) := by
    ext v
    simp [S', A, stage_of_restricted_model,
      rootedModel_restrict_through_core, MinorModel.vertices]
  have hAχ : chromatic (G.induce (A : Set V)) ≤ q + 2 * s := by
    have hXχ := hlocal X hXcard
    have hmodelχ' : chromatic (G.induce (A : Set V)) ≤
        chromatic (G.induce (X : Set V)) + 2 * s := by
      simpa [A, X] using hmodelχ
    omega
  have hmodel : S'.model.toMinorModel.vertices ⊆ (A : Set V) := by
    rw [hA]
  apply S'.exists_restored_from_model_color A hmodel hk
  · omega
  · omega
  · exact hbudget
  · exact hinsep

/-- The root-alignment version needed by the induction: the unique region
+tangencies are chosen as roots before trimming. -/
theorem StageState.exists_trimmed_and_restored_auto
    (S : StageState G s k m coreBound)
    (hlocal : ∀ X : Finset V, X.card ≤ 3 * S.core.card →
      chromatic (G.induce (X : Set V)) ≤ q)
    (hk : 0 < k)
    (hχ : q + 2 * s + 7 * k ≤ chromatic G)
    (hreserve : q + 2 * s + 6 * k ≤ m / 2)
    (hbudget : m / 2 + k ≤ m)
    (hinsep : ¬ Bootstrap.ChromaticSeparable G m) :
    Nonempty (StageState G s k (m / 2) coreBound) := by
  let R := S.normalizeRoots
  exact R.exists_trimmed_and_restored
    (fun i => S.normalizeRoots_root_in_core i)
    (fun i => S.normalizeRoots_root_in_region i)
    hlocal hk hχ hreserve hbudget hinsep
end Inseparability
end HadwigerLean


