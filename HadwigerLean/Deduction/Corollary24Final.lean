import HadwigerLean.Deduction.Corollary24Numerics
import HadwigerLean.Deduction.PowerThree
import HadwigerLean.Graph.ChromaticConnectivity.Theorem
import HadwigerLean.Graph.CliqueMinorOrder
import HadwigerLean.Woven.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
# The final GN and minor step of Corollary 24
-/

namespace HadwigerLean.Deduction

/-- The top-scale woven conclusion implies the advertised chromatic bound.
The outer induction supplies the `hW` premise. -/
theorem cor24_final_of_top_woven
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (t T d : ℕ)
    (ht : 100 ≤ t)
    (hT : Bootstrap.IsLeastPowerOfThreeAtLeast t T)
    (hminor : ¬ HasCliqueMinor G t)
    (hW : ∀ U : Finset V,
      VertexConnected (G.induce (U : Set V)) (10000 * T) →
      2000 * T + cor24B d * T ≤ chromatic (G.induce (U : Set V)) →
      Woven (G.induce (U : Set V)) T (3 * T)) :
    chromatic G < 3 * (cor24B d + 62000) * t := by
  classical
  by_contra hbound
  have hχ : 3 * (cor24B d + 62000) * t ≤ chromatic G := by omega
  have hTlt : T < 3 * t :=
    least_power_of_three_lt_three_mul (by omega) hT
  have hB : 8000 ≤ cor24B d := by
    dsimp [cor24B]
    omega
  have hfactor : 0 < cor24B d + 62000 := by omega
  have htop : (cor24B d + 62000) * T ≤ chromatic G := by
    have hm := Nat.mul_lt_mul_of_pos_left hTlt hfactor
    calc
      _ ≤ (cor24B d + 62000) * (3 * t) := le_of_lt hm
      _ = 3 * (cor24B d + 62000) * t := by ring
      _ ≤ chromatic G := hχ
  have hGN : 7 * (10000 * T) ≤ chromatic G := by
    have hcoef : 70000 ≤ cor24B d + 62000 := by omega
    have hm := Nat.mul_le_mul_right T hcoef
    omega
  obtain ⟨U, hUconn, hUχ⟩ :=
    exists_chromatic_connected_induced G (10000 * T)
      (by have htT := hT.2.1; omega) hGN
  have hχU : 2000 * T + cor24B d * T ≤
      chromatic (G.induce (U : Set V)) := by
    have heq : (2000 * T + cor24B d * T) + 6 * (10000 * T) =
        (cor24B d + 62000) * T := by ring
    omega
  have hTcard : T ≤ Fintype.card (U : Set V) := by
    have horder := hUconn.order_gt
    omega
  obtain ⟨e⟩ : Nonempty (Fin T ↪ (U : Set V)) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa using hTcard
  have hminorU : HasCliqueMinor (G.induce (U : Set V)) T :=
    (hW U hUconn hχU).clique_minor e e.injective
  have hminorG : HasCliqueMinor G T := by
    let f : G.induce (U : Set V) ↪g G := SimpleGraph.Embedding.induce _
    exact hasCliqueMinor_map f.toHom f.injective hminorU
  exact hminor (hasCliqueMinor_of_le hminorG hT.2.1)

end HadwigerLean.Deduction
