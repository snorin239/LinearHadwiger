import HadwigerLean.Inseparability.StageTangentDeletion
import HadwigerLean.Inseparability.SmallPiecesInside
import Mathlib.Tactic

/-!
# Choose the small connected pieces for the next stage

The previous model's tangencies are deleted from the chromatic region.
The SC packing consequence then supplies disjoint connected pieces entirely
away from that old model.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {s k m coreBound : ℕ}

theorem StageState.exists_small_pieces_after_tangent_deletion
    (S : StageState G s k m coreBound)
    (hrootregion : ∀ i, S.root i ∈ S.region)
    (t ℓ r N q : ℕ)
    (ht : 3 ≤ t) (htk : t ≤ ℓ)
    (hminor : ¬ HasCliqueMinor G t)
    (hsize : (480 * 6400 : ℝ)^2 * (t : ℝ) *
      (Real.log (t : ℝ))^3 ≤ (N : ℝ))
    (hlocal : ∀ U : Finset V, U.card ≤ r * N →
      chromatic (G.induce (U : Set V)) ≤ q)
    (hconnect : s + ℓ ≤ k)
    (hχ : q + 2 * (480 * 6400 * ℓ) + m + s < chromatic G) :
    ∃ J : Fin r → Finset V,
      VertexConnected
        (G.induce
          ((S.region \ S.tangentFinset : Finset V) : Set V)) ℓ ∧
      (∀ i, J i ⊆ S.region \ S.tangentFinset ∧
        (J i).card ≤ N ∧
        VertexConnected (G.induce (J i : Set V)) ℓ ∧
        Disjoint (J i : Set V) S.model.toMinorModel.vertices) ∧
      (Pairwise fun i j => Disjoint (J i) (J j)) := by
  classical
  let R : Finset V := S.region \ S.tangentFinset
  obtain ⟨hRconn,hRχ,hMdisj⟩ :=
    S.after_remove_tangencies hrootregion ℓ hconnect
  have hχR : q + 2 * (480 * 6400 * ℓ) <
      chromatic (G.induce (R : Set V)) := by
    change chromatic G ≤ chromatic (G.induce (R : Set V)) + m + s at hRχ
    omega
  obtain ⟨J,hJ,hJpair⟩ :=
    exists_disjoint_small_connected_pieces_inside_of_SC
      G R t ℓ r N q ht htk hminor hsize
      (fun U _ hU => hlocal U hU) hχR
  refine ⟨J,hRconn,?_,hJpair⟩
  intro i
  obtain ⟨hJR,hJsize,hJconn⟩ := hJ i
  refine ⟨hJR,hJsize,hJconn,?_⟩
  apply Set.disjoint_left.mpr
  intro v hvJ hvM
  exact (Set.disjoint_left.mp hMdisj) hvM (hJR hvJ)

end Inseparability
end HadwigerLean
