import HadwigerLean.Deduction.SubgraphRatioBridge
import HadwigerLean.Deduction.Corollary24Final
import Mathlib.Tactic

/-! The final GN, ratio, and clique-minor step of Theorem 4. -/

namespace HadwigerLean.Deduction

/-- The top-scale woven conclusion implies the exact paper Theorem 4 bound
with the same constant in the coefficient and order cutoff. -/
theorem theorem4_final_of_top_woven
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D t T : ℕ) (hD : 2000 ≤ D) (ht : 3 ≤ t)
    (hT : Bootstrap.IsLeastPowerOfThreeAtLeast t T)
    (hminor : ¬ HadwigerLean.HasCliqueMinor G t)
    (hW : ∀ U : Finset V,
      HadwigerLean.VertexConnected (G.induce (U : Set V)) (D * T) →
      (D : ℝ) * ((T : ℝ) + 276 * (T : ℝ) *
        (1 + theorem4ScaleMaxRatio (G.induce (U : Set V)) D T)) ≤
        (HadwigerLean.chromatic (G.induce (U : Set V)) : ℝ) →
      HadwigerLean.Woven (G.induce (U : Set V)) T (3 * T)) :
    (HadwigerLean.chromatic G : ℝ) ≤
      ((3 ^ 9 * D : ℕ) : ℝ) * (t : ℝ) *
        (1 + theorem4MaxRatio G (3 ^ 9 * D) t) := by
  classical
  let C : ℕ := 3 ^ 9 * D
  let fG : ℝ := theorem4MaxRatio G C t
  have hfG0 : 0 ≤ fG := theorem4MaxRatio_nonneg G C t
  have hTlt : T < 3 * t :=
    least_power_of_three_lt_three_mul (by omega) hT
  have hT3 : (T : ℝ) ≤ 3 * (t : ℝ) := by
    exact_mod_cast hTlt.le
  by_contra hbound
  have hχ : (C : ℝ) * (t : ℝ) * (1 + fG) <
      (HadwigerLean.chromatic G : ℝ) := by
    exact lt_of_not_ge (by simpa only [C, fG] using hbound)
  have hGNbudget : 7 * (D : ℝ) * (T : ℝ) ≤
      (C : ℝ) * (t : ℝ) * (1 + fG) := by
    calc
      7 * (D : ℝ) * (T : ℝ) ≤
          7 * (D : ℝ) * (3 * (t : ℝ)) := by gcongr
      _ = 21 * (D : ℝ) * (t : ℝ) := by ring
      _ ≤ (C : ℝ) * (t : ℝ) := by
        have hc : 21 * (D : ℝ) ≤ (C : ℝ) := by
          simp [C]
          nlinarith
        exact mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ (C : ℝ) * (t : ℝ) * (1 + fG) := by
        have hh := mul_nonneg
          (show 0 ≤ (C : ℝ) * (t : ℝ) by positivity) hfG0
        nlinarith
  have hGN : 7 * (D * T) ≤ HadwigerLean.chromatic G := by
    have hh : ((7 * (D * T) : ℕ) : ℝ) ≤
        (HadwigerLean.chromatic G : ℝ) := by
      calc
        ((7 * (D * T) : ℕ) : ℝ) = 7 * (D : ℝ) * (T : ℝ) := by
          push_cast
          ring
        _ ≤ (C : ℝ) * (t : ℝ) * (1 + fG) := hGNbudget
        _ ≤ (HadwigerLean.chromatic G : ℝ) := hχ.le
    exact_mod_cast hh
  obtain ⟨U, hUconn, hUχ⟩ :=
    HadwigerLean.exists_chromatic_connected_induced G (D * T)
      (by
        have htT := hT.2.1
        have hTp : 0 < T := by omega
        have hDp : 0 < D := by omega
        exact Nat.mul_pos hDp hTp) hGN
  let F := G.induce (U : Set V)
  let fF : ℝ := theorem4ScaleMaxRatio F D T
  have hfF0 : 0 ≤ fF := theorem4ScaleMaxRatio_nonneg F D T
  have hff : fF ≤ fG := by
    exact theorem4ScaleMaxRatio_induce_le_theorem4MaxRatio
      G U D t T ht hT.2.1 hTlt hminor
  have hcoeff : 3 * (283 + 276 * fG) ≤ 19683 * (1 + fG) := by
    nlinarith
  have hbudget : (D : ℝ) * (T : ℝ) * (283 + 276 * fF) ≤
      (C : ℝ) * (t : ℝ) * (1 + fG) := by
    calc
      (D : ℝ) * (T : ℝ) * (283 + 276 * fF) ≤
          (D : ℝ) * (3 * (t : ℝ)) * (283 + 276 * fF) := by
            gcongr
      _ ≤ (D : ℝ) * (3 * (t : ℝ)) * (283 + 276 * fG) := by
        gcongr
      _ = ((D : ℝ) * (t : ℝ)) * (3 * (283 + 276 * fG)) := by ring
      _ ≤ ((D : ℝ) * (t : ℝ)) * (19683 * (1 + fG)) :=
        mul_le_mul_of_nonneg_left hcoeff (by positivity)
      _ = (C : ℝ) * (t : ℝ) * (1 + fG) := by
        simp [C]
        ring
  have hUχreal : (HadwigerLean.chromatic G : ℝ) ≤
      (HadwigerLean.chromatic F : ℝ) + 6 * (D : ℝ) * (T : ℝ) := by
    have hh : (HadwigerLean.chromatic G : ℝ) ≤
        (HadwigerLean.chromatic (G.induce (U : Set V)) : ℝ) +
          ((6 * (D * T) : ℕ) : ℝ) := by exact_mod_cast hUχ
    dsimp [F]
    convert hh using 1 <;> push_cast <;> ring
  have hFχ : (D : ℝ) * ((T : ℝ) + 276 * (T : ℝ) * (1 + fF)) ≤
      (HadwigerLean.chromatic F : ℝ) := by
    have hh : (D : ℝ) * (T : ℝ) * (277 + 276 * fF) ≤
        (HadwigerLean.chromatic F : ℝ) := by
      nlinarith [hbudget, hχ, hUχreal]
    convert hh using 1 <;> ring
  have hTcard : T ≤ Fintype.card (U : Set V) := by
    have horder := hUconn.order_gt
    have hDT : T ≤ D * T := by
      simpa only [one_mul] using Nat.mul_le_mul_right T (by omega : 1 ≤ D)
    omega
  obtain ⟨e⟩ : Nonempty (Fin T ↪ (U : Set V)) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa using hTcard
  have hminorF : HadwigerLean.HasCliqueMinor F T :=
    (hW U hUconn hFχ).clique_minor e e.injective
  have hminorG : HadwigerLean.HasCliqueMinor G T := by
    let f : F ↪g G := SimpleGraph.Embedding.induce _
    exact HadwigerLean.hasCliqueMinor_map f.toHom f.injective hminorF
  exact hminor (HadwigerLean.hasCliqueMinor_of_le hminorG hT.2.1)

end HadwigerLean.Deduction


