import HadwigerLean.Inseparability.RegionRestoration
import HadwigerLean.Inseparability.RegionExtraction

/-!
# Restore a stage after controlling its model's chromatic number

Once the newly built model lies in a low-chromatic finite set, additive GN
finds a connected region avoiding it. Chromatic inseparability and a large
overlap then restore the stage invariant.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {s k m coreBound : ℕ}

/-- The final bookkeeping step in every nonzero stage. -/
theorem StageState.exists_restored_from_model_color
    (S : StageState G s k m coreBound)
    (A : Finset V)
    (hmodel : S.model.toMinorModel.vertices ⊆ (A : Set V))
    (hk : 0 < k)
    (hχ : chromatic (G.induce (A : Set V)) + 7 * k ≤ chromatic G)
    (hreserve : chromatic (G.induce (A : Set V)) + 6 * k ≤ m / 2)
    (hbudget : m / 2 + k ≤ m)
    (hinsep : ¬ Bootstrap.ChromaticSeparable G m) :
    Nonempty (StageState G s k (m / 2) coreBound) := by
  obtain ⟨B,hBsub,hBconn,hBχ⟩ :=
    exists_connected_region_avoiding G A k (m / 2) hk hχ hreserve
  have hBavoid : Disjoint (B : Set V) S.model.toMinorModel.vertices := by
    apply Set.disjoint_left.mpr
    intro v hvB hvM
    exact (Finset.mem_compl.mp (hBsub hvB)) (hmodel hvM)
  exact ⟨S.restoreRegion B hBconn hBχ hbudget hinsep hBavoid⟩

end Inseparability
end HadwigerLean
