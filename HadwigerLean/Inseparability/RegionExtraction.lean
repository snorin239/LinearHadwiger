import HadwigerLean.Inseparability.SmallPieces
import HadwigerLean.Woven.ThreeChildGN

/-!
# Recover a high-chromatic connected region after model construction

After the new clique-model union is shown to have small chromatic number,
delete it and apply additive chromatic connectivity. The extracted region
avoids every model vertex and loses only six more colors.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

/-- Extract a `k`-connected high-chromatic induced region in the complement
of a low-chromatic finite set. -/
theorem exists_connected_region_avoiding
    (G : SimpleGraph V) (A : Finset V) (k loss : ℕ)
    (hk : 0 < k)
    (hχ : chromatic (G.induce (A : Set V)) + 7 * k ≤ chromatic G)
    (hbudget : chromatic (G.induce (A : Set V)) + 6 * k ≤ loss) :
    ∃ H : Finset V,
      H ⊆ Aᶜ ∧
      VertexConnected (G.induce (H : Set V)) k ∧
      chromatic G ≤ chromatic (G.induce (H : Set V)) + loss := by
  classical
  have hsplit := chromatic_le_piece_and_complement G A
  have hresidual : 7 * k ≤
      chromatic (G.induce (Aᶜ : Finset V)) := by
    omega
  obtain ⟨H,hHsub,hHconn,hHχ⟩ :=
    Woven.exists_chromatic_connected_inside G Aᶜ k hk hresidual
  refine ⟨H,hHsub,hHconn,?_⟩
  omega

end Inseparability
end HadwigerLean
