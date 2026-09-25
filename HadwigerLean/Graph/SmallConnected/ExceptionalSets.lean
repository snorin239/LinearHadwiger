import HadwigerLean.Graph.SmallConnected.PackedMaximality
import HadwigerLean.Graph.SmallConnected.TBound
import HadwigerLean.Graph.SmallConnected.KTBound
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Exceptional sets in the quotient graph
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable def highCrossVertices
    (Q : SimpleGraph V) [DecidableRel Q.Adj]
    (X : Finset V) (k : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => v ∉ X ∧
    3 * 6400 * (k : ℝ) ≤ ((Q.neighborFinset v ∩ X).card : ℝ)

noncomputable def highDegreeVertices
    (Q : SimpleGraph V) [DecidableRel Q.Adj]
    (X Y : Finset V) (d t : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => v ∉ X ∧ v ∉ Y ∧
    20 * (d : ℝ) * Real.log (t : ℝ) ≤ (Q.degree v : ℝ)

/-- The packed blocks, their high-incidence neighbors, and high-degree
vertices occupy at most `3N/(10 log t)` quotient vertices. -/
theorem exists_small_exceptional_set
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : ConnectedBlockFamily G) [DecidableRel F.quotient.Adj]
    (h p d t k N : ℕ)
    (ht : 3 ≤ t) (htk : t ≤ k)
    (hd : d = 480 * 6400 * k)
    (hh : 1 ≤ h)
    (hN : Fintype.card V = N) (hNpos : 0 < N)
    (hexact : edgeCount G = d * N)
    (hminor : ¬ HasCliqueMinor G t)
    (hgood : GoodPackedFamily G h p F)
    (hscale : 10 * (Real.log (t : ℝ))^2 * (t : ℝ)^2 ≤
      ((h - 1 : ℕ) : ℝ) * (k : ℝ)^2) :
    ∃ T : Finset F.Vertex,
      F.blockVertices ⊆ T ∧
      10 * Real.log (t : ℝ) * (T.card : ℝ) ≤ (3 * N : ℝ) ∧
      (∀ v ∈ Tᶜ,
        2 * ((F.quotient.neighborFinset v ∩ F.blockVertices).card : ℝ) <
          48 * 6400 * (k : ℝ)) ∧
      (∀ v ∈ Tᶜ,
        (F.quotient.degree v : ℝ) <
          20 * (d : ℝ) * Real.log (t : ℝ)) := by
  classical
  let Q := F.quotient
  let X := F.blockVertices
  let Y := highCrossVertices Q X k
  let Z := highDegreeVertices Q X Y d t
  let T := X ∪ Y ∪ Z
  have hXY : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro v hvX hvY
    exact (Finset.mem_filter.mp hvY).2.1 hvX
  have hXZ : Disjoint X Z := by
    apply Finset.disjoint_left.mpr
    intro v hvX hvZ
    exact (Finset.mem_filter.mp hvZ).2.1 hvX
  have hYZ : Disjoint Y Z := by
    apply Finset.disjoint_left.mpr
    intro v hvY hvZ
    exact (Finset.mem_filter.mp hvZ).2.2.1 hvY
  have hL : 0 ≤ Real.log (t : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ t))
  have hk : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hKT := density_forces_k_le_kt_scale G t k ht htk hminor
    (by omega) (by rw [hN, hexact, hd])
  have hKT2 : (k : ℝ)^2 ≤ (t : ℝ)^2 * Real.log (t : ℝ) := by
    have ht0 : (0 : ℝ) ≤ t := by positivity
    have hs := mul_self_le_mul_self hk.le hKT
    have hsqrt := Real.sq_sqrt hL
    nlinarith
  have hY : (k : ℝ)^2 * (Y.card : ℝ) ≤
      (t : ℝ)^2 * Real.log (t : ℝ) * (X.card : ℝ) := by
    apply high_cross_degree_card_bound Q X Y hXY t k ht htk
      (F.quotient_cliqueMinor_free t hminor) hKT
    intro y hy
    exact (Finset.mem_filter.mp hy).2.2
  have heQ : edgeCount Q ≤ d * N := by
    rw [← hexact]
    exact hgood.2.2
  have hZ : 10 * Real.log (t : ℝ) * (Z.card : ℝ) ≤ (N : ℝ) := by
    apply high_degree_card_bound Q Z d N (Real.log (t : ℝ))
      (by omega) hL heQ
    intro v hv
    exact (Finset.mem_filter.mp hv).2.2.2
  have hsav : F.blocks.card * (h - 1) ≤ N := by
    simpa [hN] using hgood.savings_le_card G h p hh
  have hXcard : X.card = F.blocks.card := F.blockVertices_card
  have hpack : 10 * Real.log (t : ℝ)^2 * (t : ℝ)^2 * (X.card : ℝ) ≤
      (N : ℝ) * (k : ℝ)^2 := by
    calc
      10 * Real.log (t : ℝ)^2 * (t : ℝ)^2 * (X.card : ℝ) ≤
          (((h - 1 : ℕ) : ℝ) * (k : ℝ)^2) * (X.card : ℝ) :=
            mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg _)
      _ = ((F.blocks.card * (h - 1) : ℕ) : ℝ) * (k : ℝ)^2 := by
        rw [hXcard]
        push_cast
        ring
      _ ≤ (N : ℝ) * (k : ℝ)^2 :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hsav) (sq_nonneg _)
  have hnum := exceptional_set_numerical_bound
    (X.card : ℝ) (Y.card : ℝ) (Z.card : ℝ) (N : ℝ)
    (t : ℝ) (k : ℝ) (Real.log (t : ℝ))
    (Nat.cast_nonneg _) hL hk hKT2 hpack hY hZ
  have hTcard : T.card ≤ X.card + Y.card + Z.card := by
    dsimp [T]
    calc
      (X ∪ Y ∪ Z).card ≤ (X ∪ Y).card + Z.card := Finset.card_union_le _ _
      _ ≤ X.card + Y.card + Z.card := by
        have hxy := Finset.card_union_le X Y
        omega
  have hTbound : 10 * Real.log (t : ℝ) * (T.card : ℝ) ≤
      (3 * N : ℝ) := by
    have hc : (T.card : ℝ) ≤ X.card + Y.card + Z.card := by
      exact_mod_cast hTcard
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 10 * Real.log (t : ℝ) by positivity)
      (sub_nonneg.mpr hc)]
  refine ⟨T, ?_, hTbound, ?_, ?_⟩
  · exact Finset.subset_union_left.trans Finset.subset_union_left
  · intro v hvT
    have hvnotT := Finset.mem_compl.mp hvT
    have hvnotX : v ∉ X := by
      intro hvX
      exact hvnotT (by simp [T, hvX])
    have hvnotY : v ∉ Y := by
      intro hvY
      exact hvnotT (by simp [T, hvY])
    have hlow : ((Q.neighborFinset v ∩ X).card : ℝ) <
        3 * 6400 * (k : ℝ) := by
      by_contra hnot
      have hy : v ∈ Y := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hvnotX, le_of_not_gt hnot⟩
      exact hvnotY hy
    linarith
  · intro v hvT
    have hvnotT := Finset.mem_compl.mp hvT
    have hvnotX : v ∉ X := by
      intro hvX
      exact hvnotT (by simp [T, hvX])
    have hvnotY : v ∉ Y := by
      intro hvY
      exact hvnotT (by simp [T, hvY])
    have hvnotZ : v ∉ Z := by
      intro hvZ
      exact hvnotT (by simp [T, hvZ])
    have hlow : (Q.degree v : ℝ) < 20 * (d : ℝ) * Real.log (t : ℝ) := by
      by_contra hnot
      have hz : v ∈ Z := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hvnotX, hvnotY, le_of_not_gt hnot⟩
      exact hvnotZ hz
    exact hlow

end HadwigerLean