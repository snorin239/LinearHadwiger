import HadwigerLean.Woven.DoubleFanCost
import HadwigerLean.Woven.ThreeChildGN
import Mathlib.Tactic

/-!
# Chromatic extraction of the residual graph after a double fan
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {Z H : Finset V}

/-- Remove proxy vertices, the hub, and a four-colors-per-source fan,
then apply chromatic connectivity to the residual. -/
theorem exists_connected_fan_residual
    (F : DoubleFan G Z H)
    (hfan : chromatic (G.induce (F.vertexFinset : Set V)) ≤
      4 * Z.card)
    (h : ℕ)
    (hHub : chromatic (G.induce (H : Set V)) ≤ h)
    (k : ℕ) (hk : 0 < k)
    (hχ : Z.card + h + 4 * Z.card + 7 * k ≤ chromatic G) :
    ∃ U : Finset V,
      U ⊆ (Z ∪ H ∪ F.vertexFinset)ᶜ ∧
      VertexConnected (G.induce (U : Set V)) k ∧
      chromatic G ≤
        chromatic (G.induce (U : Set V)) +
          (Z.card + h + 4 * Z.card + 6 * k) := by
  classical
  let R : Finset V := (Z ∪ H ∪ F.vertexFinset)ᶜ
  have hcolor := F.chromatic_le_source_hub_fan_residual hfan
  have hcolor' : chromatic G ≤
      Z.card + h + 4 * Z.card +
        chromatic (G.induce (R : Set V)) := by
    have hRset : (R : Set V) =
        ((Z ∪ H ∪ F.vertexFinset : Finset V) : Set V)ᶜ := by
      ext v
      simp [R]
    rw [← hRset] at hcolor
    omega
  have hR : 7 * k ≤ chromatic (G.induce (R : Set V)) := by omega
  obtain ⟨U,hUR,hconn,hchiU⟩ :=
    exists_chromatic_connected_inside G R k hk hR
  refine ⟨U,hUR,hconn,?_⟩
  omega

end Woven
end HadwigerLean
