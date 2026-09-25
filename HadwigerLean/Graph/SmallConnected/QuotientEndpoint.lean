import HadwigerLean.Graph.SmallConnected.OrderNumerics
import HadwigerLean.Graph.SmallConnected.GlobalCore
import HadwigerLean.Graph.SmallConnected.LocalEndpoint
import Mathlib.Tactic

/-!
# Bounded connected witness in the packing quotient
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The exact-density Section 8 argument yields a k-connected witness
among uncovered vertices of a maximal packing quotient. -/
theorem exists_small_connected_quotient_witness
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t k N : ℕ) (ht : 3 ≤ t) (htk : t ≤ k)
    (hN : Fintype.card V = N) (hNpos : 0 < N)
    (hminor : ¬ HasCliqueMinor G t)
    (hexact : edgeCount G = (480 * 6400 * k) * N) :
    ∃ F : ConnectedBlockFamily G,
      ∃ (W : Type u) (_ : Fintype W) (f : W ↪ F.Vertex),
        (Fintype.card W : ℝ) ≤
          (480 * 6400 : ℝ)^2 * (t : ℝ) * (Real.log (t : ℝ))^3 ∧
        (∀ w, f w ∉ F.blockVertices) ∧
        VertexConnected (F.quotient.comap f) k := by
  classical
  let h := smallConnectedBlockSize t k
  let p := 48 * 6400 * k
  let d := 480 * 6400 * k
  have hk : 0 < k := by omega
  have hh : 1 ≤ h := by simp [h, smallConnectedBlockSize]
  have hscale : 10 * Real.log (t : ℝ)^2 * (t : ℝ)^2 ≤
      ((h - 1 : ℕ) : ℝ) * (k : ℝ)^2 :=
    smallConnectedBlockSize_lower t k hk
  obtain ⟨F, hgood, hmaxF⟩ :=
    exists_maximal_good_packed_family G h p
  letI : DecidableRel F.quotient.Adj := Classical.decRel _
  obtain ⟨T, hXT, hTbound, hcross, hdegree⟩ :=
    exists_small_exceptional_set G F h p d t k N ht htk rfl hh
      hN hNpos (by simpa [d] using hexact) hminor hgood hscale
  have horder : Fintype.card F.Vertex ≤ N := by
    have hcount := F.vertex_card_add_savings hgood.1 hh
    rw [hN] at hcount
    omega
  have hret : (9 / 10 : ℝ) * (480 * 6400 * (k : ℝ)) * (N : ℝ) ≤
      (edgeCount F.quotient : ℝ) := by
    have hexactP : edgeCount G = 10 * p * N := by
      rw [hexact]
      dsimp [p]
      ring
    have hretNat := hgood.retained_edges G h p hh F N hN hexactP
    have hretR : ((9 * p * N : ℕ) : ℝ) ≤ (edgeCount F.quotient : ℝ) := by
      exact_mod_cast hretNat
    have hcoef : (9 / 10 : ℝ) * (480 * 6400 * (k : ℝ)) * (N : ℝ) =
        ((9 * p * N : ℕ) : ℝ) := by
      simp only [p, Nat.cast_mul, Nat.cast_ofNat]
      ring
    rw [hcoef]
    exact hretR
  obtain ⟨S, hSne, hST, hminR, hratioR⟩ :=
    exists_trimmed_residual_set F.quotient T t k N
      ht htk hNpos (F.quotient_cliqueMinor_free t hminor)
      horder hTbound hret
  have hSX : Disjoint S F.blockVertices := by
    apply Finset.disjoint_left.mpr
    intro v hvS hvX
    exact (Finset.mem_compl.mp (hST hvS)) (hXT hvX)
  have hmin : ∀ v ∈ S,
      4 * p ≤ (F.quotient.neighborFinset v ∩ S).card := by
    intro v hv
    have hminv := hminR v hv
    exact_mod_cast hminv
  have hratio : ∀ v ∈ S,
      F.quotient.degree v ≤
        3 * (F.quotient.neighborFinset v ∩ S).card := by
    intro v hv
    have hratioV := hratioR v hv
    exact_mod_cast hratioV
  obtain ⟨H, hH, hmaxH⟩ :=
    exists_maximal_lowLossConnectedSet F.quotient S h p hSne hh
  have hshort : H.card < h :=
    lowLossConnectedSet_card_lt_of_maximal_family G h p F
      hgood hmaxF S H hSX hH
  have hmaxcost := maximal_lowLoss_extension_cost F.quotient S
    F.blockVertices H h p hH hmaxH hshort
  have hXcap : ∀ v ∈ S,
      2 * (F.quotient.neighborFinset v ∩ F.blockVertices).card < p := by
    intro v hv
    have hbound := hcross v (hST hv)
    exact_mod_cast hbound
  obtain ⟨W, instW, f, hWcard, hfR, hWconn⟩ :=
    local_connected_witness F.quotient H F.blockVertices S p k
      (by omega) (by dsimp [p]; omega)
      hH.1 hH.2.1 hSX hmin hratio hH.2.2.2.2 hmaxcost hXcap
  letI : Fintype W := instW
  have hcap : ∀ v ∈ S,
      (F.quotient.degree v : ℝ) ≤
        20 * (d : ℝ) * Real.log (t : ℝ) := by
    intro v hv
    exact le_of_lt (hdegree v (hST hv))
  have hRcard := localR_card_le_degree_cap F.quotient H
    F.blockVertices S d (Real.log (t : ℝ)) hH.2.1 hcap
  have hKT := density_forces_k_le_kt_scale G t k ht htk hminor
    (by omega) (by rw [hN, hexact])
  have hL : 0 ≤ Real.log (t : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ t))
  have hKT2 : (k : ℝ)^2 ≤
      (t : ℝ)^2 * Real.log (t : ℝ) := by
    have hsq := mul_self_le_mul_self
      (by exact_mod_cast (Nat.zero_le k) : (0 : ℝ) ≤ k) hKT
    have hsqrt := Real.sq_sqrt hL
    nlinarith
  have hsize := smallConnectedBlockSize_upper t k ht hk hKT2
  have horderR : ((localR F.quotient H F.blockVertices).card : ℝ) ≤
      (480 * 6400 : ℝ)^2 * (t : ℝ) * (Real.log (t : ℝ))^3 := by
    apply small_connected_order_numerical
      _ (H.card : ℝ) (t : ℝ) (k : ℝ) (Real.log (t : ℝ))
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (by exact_mod_cast (by omega : 0 < t))
      (by exact_mod_cast htk) hL
    · convert hRcard using 1 <;> norm_num [d] <;> ring
    · have hHcard : (H.card : ℝ) ≤ h := by
        exact_mod_cast hH.2.2.1
      have hk2 : (0 : ℝ) ≤ (k : ℝ)^2 := sq_nonneg _
      nlinarith [mul_nonneg hk2 (sub_nonneg.mpr hHcard)]
  refine ⟨F, W, instW, f, ?_, ?_, hWconn⟩
  · exact (by exact_mod_cast hWcard :
      (Fintype.card W : ℝ) ≤
      ((localR F.quotient H F.blockVertices).card : ℝ)).trans horderR
  · intro w
    have hmem := hfR w
    exact (Finset.mem_sdiff.mp hmem).2

end HadwigerLean