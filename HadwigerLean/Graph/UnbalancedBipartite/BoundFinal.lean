import HadwigerLean.Graph.UnbalancedBipartite.Bound
import HadwigerLean.Graph.UnbalancedBipartite.BoundStructural
import HadwigerLean.Graph.UnbalancedBipartite.NearCompleteSelection

import Mathlib.Tactic

set_option maxHeartbeats 1000000

namespace HadwigerLean

universe u

private theorem bipartite_card_sum
    {W : Type u} [Fintype W] [DecidableEq W]
    (A B : Finset W)
    (hdisj : Disjoint A B) (hcover : A ∪ B = Finset.univ) :
    Fintype.card W = A.card + B.card := by
  calc
    Fintype.card W = (Finset.univ : Finset W).card := rfl
    _ = (A ∪ B).card := by rw [hcover]
    _ = A.card + B.card := Finset.card_union_of_disjoint hdisj

/-- Appendix C's coefficient-6400 edge bound for a finite bipartite graph. -/
theorem unbalanced_bipartite_edge_bound
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (t : ℕ) (ht : 3 ≤ t)
    (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hcover : A ∪ B = Finset.univ) (hminor : ¬ HasCliqueMinor G t) :
    (edgeCount G : ℝ) ≤
      6400 * ((t : ℝ) * Real.sqrt (Real.log (t : ℝ))) *
        Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) +
      ((t - 2 : ℕ) : ℝ) * ((A.card : ℝ) + (B.card : ℝ)) := by
  classical
  have main :
      ∀ N : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W],
        (H : SimpleGraph W) → [DecidableRel H.Adj] → (L R : Finset W) →
        H.IsBipartiteWith (L : Set W) (R : Set W) →
        L ∪ R = Finset.univ →
        ¬ HasCliqueMinor H t →
        Fintype.card W = N →
        (edgeCount H : ℝ) ≤
          6400 * ((t : ℝ) * Real.sqrt (Real.log (t : ℝ))) *
            Real.sqrt ((L.card : ℝ) * (R.card : ℝ)) +
          ((t - 2 : ℕ) : ℝ) * ((L.card : ℝ) + (R.card : ℝ)) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro W _ _ H _ L R hH hcoverH hminorH hcardH
      classical
      have ordered (A B : Finset W)
          (hBip : H.IsBipartiteWith (A : Set W) (B : Set W))
          (hCover : A ∪ B = Finset.univ)
          (hOrder : B.card ≤ A.card) :
          (edgeCount H : ℝ) ≤
            6400 * ((t : ℝ) * Real.sqrt (Real.log (t : ℝ))) *
              Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) +
            ((t - 2 : ℕ) : ℝ) * ((A.card : ℝ) + (B.card : ℝ)) := by
        have hDisj : Disjoint A B := by
          apply Finset.disjoint_left.mpr
          intro x hxA hxB
          exact (Set.disjoint_left.mp hBip.disjoint) hxA hxB
        have hcard : N = A.card + B.card := by
          rw [← hcardH]
          exact bipartite_card_sum A B hDisj hCover
        let τ : ℝ := (t : ℝ) * Real.sqrt (Real.log (t : ℝ))
        let κ : ℝ := ((t - 2 : ℕ) : ℝ)
        obtain ⟨hτge, hτsq⟩ := kt_scale_ge_order_and_square t ht
        have hτpos : 0 < τ := by
          have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
          dsimp [τ]
          linarith
        have hκ : 0 ≤ κ := by positivity
        by_cases hBsmall : B.card ≤ t - 2
        · have hlin := edgeCount_le_linear_term_of_small_right H A B hBip t hBsmall
          have hlinR : (edgeCount H : ℝ) ≤ κ * ((A.card : ℝ) + (B.card : ℝ)) := by
            dsimp [κ]
            exact_mod_cast hlin
          have hroot : 0 ≤ Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) :=
            Real.sqrt_nonneg _
          change (edgeCount H : ℝ) ≤
            6400 * τ * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) +
              κ * ((A.card : ℝ) + (B.card : ℝ))
          nlinarith
        · have hBlarge : t - 1 ≤ B.card := by omega
          have hbNat : 1 ≤ B.card := by omega
          have haNat : 1 ≤ A.card := by omega
          have hb : (1 : ℝ) ≤ B.card := by exact_mod_cast hbNat
          have ha : (1 : ℝ) ≤ A.card := by exact_mod_cast haNat
          have hba : (B.card : ℝ) ≤ A.card := by exact_mod_cast hOrder
          let α : ℝ := (A.card : ℝ) /
            Real.sqrt ((A.card : ℝ) * (B.card : ℝ))
          have hαge : 1 ≤ α := aspect_ratio_ge_one _ _ (by linarith)
            (by linarith) hba
          have hαpos : 0 < α := by linarith
          have hroot : 0 < Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by
            apply Real.sqrt_pos.mpr
            nlinarith
          by_contra hbound
          have hcounter :
              6400 * τ * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) +
                κ * ((A.card : ℝ) + (B.card : ℝ)) <
                  (edgeCount H : ℝ) := by
            exact lt_of_not_ge hbound
          have hdelete (v : W) (hv : v ∈ A) :
              3200 * τ * (B.card : ℝ) /
                  Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) + κ <
                (H.degree v : ℝ) := by
            let S : Set W := ({v} : Set W)ᶜ
            let A' : Finset S := Finset.univ.filter (fun x => (x : W) ∈ A)
            let B' : Finset S := Finset.univ.filter (fun x => (x : W) ∈ B)
            have hdata := bipartite_vertex_deletion_data H A B hBip hCover v hv
            change (H.induce S).IsBipartiteWith (A' : Set S) (B' : Set S) ∧
              A'.card + 1 = A.card ∧ B'.card = B.card ∧
              A' ∪ B' = Finset.univ ∧
              edgeCount (H.induce S) + H.degree v = edgeCount H at hdata
            obtain ⟨hDBip, hAc, hBc, hDCover, hLoss⟩ := hdata
            have hDminor : ¬ HasCliqueMinor (H.induce S) t := by
              intro h
              exact hminorH (hasCliqueMinor_of_minor (induce_isMinor H S) h)
            have hsmall : Fintype.card S < N := by
              rw [← hcardH]
              exact Fintype.card_subtype_lt (x := v) (by simp [S])
            have hD := ih (Fintype.card S) hsmall S (H.induce S)
              A' B' hDBip hDCover hDminor rfl
            have hAcR : (A'.card : ℝ) = (A.card : ℝ) - 1 := by
              have h := congrArg (fun k : ℕ => (k : ℝ)) hAc
              norm_num at h
              linarith
            have hBcR : (B'.card : ℝ) = (B.card : ℝ) := by
              exact_mod_cast hBc
            change (edgeCount (H.induce S) : ℝ) ≤
              6400 * τ * Real.sqrt ((A'.card : ℝ) * (B'.card : ℝ)) +
              κ * ((A'.card : ℝ) + (B'.card : ℝ)) at hD
            rw [hAcR, hBcR] at hD
            have hLossR : (edgeCount (H.induce S) : ℝ) +
                (H.degree v : ℝ) = (edgeCount H : ℝ) := by
              exact_mod_cast hLoss
            exact degree_lower_of_vertex_deletion _ _ _ _ _ _ _
              ha (by linarith) hτpos.le hcounter hD hLossR
          have hcardpos : 0 < Fintype.card W := by
            rw [hcardH, hcard]
            omega
          have hKT0 := edgeCount_lt_kt_threshold_of_no_clique_minor H t
            (by omega) hminorH hcardpos
          have hKT1 : (edgeCount H : ℝ) < 30 * τ * (Fintype.card W : ℝ) := by
            simpa only [τ, mul_assoc] using hKT0
          rw [hcardH, hcard, Nat.cast_add] at hKT1
          have hsum : (A.card : ℝ) + (B.card : ℝ) ≤
              2 * (A.card : ℝ) := by linarith
          have hscaled := mul_le_mul_of_nonneg_left hsum
            (by positivity : 0 ≤ 30 * τ)
          have hKT : (edgeCount H : ℝ) < 60 * τ * (A.card : ℝ) := by
            nlinarith [hKT1]
          have hcoeff : 60 * τ ≤ 1600 * α * τ := by
            nlinarith [mul_nonneg (show 0 ≤ α - 1 by linarith) hτpos.le]
          have hscaled' := mul_le_mul_of_nonneg_left hcoeff
            (by positivity : 0 ≤ (A.card : ℝ))
          have heLower : (edgeCount H : ℝ) <
              (A.card : ℝ) * (1600 * α * τ) := by nlinarith
          have hAne : A.Nonempty := Finset.card_pos.mp (by omega : 0 < A.card)
          obtain ⟨v₀, hv₀, hlow⟩ :=
            exists_left_degree_lt_of_edgeCount_lt H A B hBip hAne
              (1600 * α * τ) heLower
          have hpair (x y : W)
              (hx : x ∈ H.neighborFinset v₀)
              (hy : y ∈ H.neighborFinset v₀)
              (hxy : x ≠ y) :
              1600 * α * τ <
                (((H.neighborFinset x ∩ H.neighborFinset y).erase v₀).card : ℝ) := by
            have hvx : H.Adj v₀ x := (H.mem_neighborFinset v₀ x).mp hx
            have hvy : H.Adj v₀ y := (H.mem_neighborFinset v₀ y).mp hy
            have hxB : x ∈ B := hBip.mem_of_mem_adj hv₀ hvx
            have hyB : y ∈ B := hBip.mem_of_mem_adj hv₀ hvy
            let S : Set W := twoNeighborContractionSet v₀ y
            let P : SimpleGraph S := twoNeighborContractionGraph H v₀ x y
            let A' : Finset S := Finset.univ.filter (fun z => z.1 ∈ A)
            let B' : Finset S := Finset.univ.filter (fun z => z.1 ∈ B)
            have hPBip : P.IsBipartiteWith (A' : Set S) (B' : Set S) := by
              simpa [P, A', B'] using
                twoNeighborContraction_isBipartiteWith H A B hBip v₀ x y hxB hyB
            have hPclass := twoNeighborContraction_class_card A B hDisj v₀ y hv₀ hyB
            change A'.card + 1 = A.card ∧ B'.card + 1 = B.card at hPclass
            obtain ⟨hAc, hBc⟩ := hPclass
            have hPCover : A' ∪ B' = Finset.univ := by
              exact twoNeighborContraction_class_cover A B hCover v₀ y
            have hPminor : IsMinor P H :=
              twoNeighborContraction_isMinor H v₀ x y hvx hvy
            have hPminorFree : ¬ HasCliqueMinor P t := by
              intro h
              exact hminorH (hasCliqueMinor_of_minor hPminor h)
            have hsmall : Fintype.card S < N := by
              rw [← hcardH]
              exact Fintype.card_subtype_lt (x := v₀)
                (by simp [S, twoNeighborContractionSet])
            have hP := ih (Fintype.card S) hsmall S P A' B'
              hPBip hPCover hPminorFree rfl
            have hAcR : (A'.card : ℝ) = (A.card : ℝ) - 1 := by
              have h := congrArg (fun k : ℕ => (k : ℝ)) hAc
              norm_num at h
              linarith
            have hBcR : (B'.card : ℝ) = (B.card : ℝ) - 1 := by
              have h := congrArg (fun k : ℕ => (k : ℝ)) hBc
              norm_num at h
              linarith
            change (edgeCount P : ℝ) ≤
              6400 * τ * Real.sqrt ((A'.card : ℝ) * (B'.card : ℝ)) +
              κ * ((A'.card : ℝ) + (B'.card : ℝ)) at hP
            rw [hAcR, hBcR] at hP
            have hLoss := twoNeighborContraction_edgeCount_add_degree_add_common
              H A B hBip v₀ x y hv₀ hxB hyB hxy
            have hLossR : (edgeCount P : ℝ) + (H.degree v₀ : ℝ) +
                (((H.neighborFinset x ∩ H.neighborFinset y).erase v₀).card : ℝ) =
                  (edgeCount H : ℝ) := by
              exact_mod_cast hLoss
            have hαrewrite : 1600 * α * τ =
                1600 * τ * (A.card : ℝ) /
                  Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by
              dsimp [α]
              ring
            have hdegree : (H.degree v₀ : ℝ) ≤
                1600 * τ * (A.card : ℝ) /
                  Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by
              rw [← hαrewrite]
              exact le_of_lt hlow
            have hboundCommon := common_neighbor_lower_of_path_contraction
              (A.card : ℝ) (B.card : ℝ) τ κ (edgeCount H : ℝ)
              (edgeCount P : ℝ) (H.degree v₀ : ℝ)
              (((H.neighborFinset x ∩ H.neighborFinset y).erase v₀).card : ℝ)
              ha hb hτpos.le hκ hcounter hP hLossR hdegree
            rw [hαrewrite]
            exact hboundCommon
          let n : ℕ := Nat.ceil (τ / α + (t : ℝ) - 2)
          have hτge' : (t : ℝ) ≤ τ := hτge
          have hsample := sample_size_ceiling_bounds t (by omega) τ α
            hτge' hαge
          change t - 1 ≤ n ∧ τ / α ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * τ at hsample
          obtain ⟨hnlowNat, hnlow, hnup⟩ := hsample
          have hn2 : 2 ≤ n := by omega
          have hβ : (B.card : ℝ) /
              Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) = 1 / α := by
            apply (eq_div_iff (ne_of_gt hαpos)).mpr
            have hprod := aspect_ratio_mul_reciprocal
              (A.card : ℝ) (B.card : ℝ) (by linarith) (by linarith)
            nlinarith
          have hκR : κ = (t : ℝ) - 2 := by
            dsimp [κ]
            exact Nat.cast_sub (by omega : 2 ≤ t)
          have hdegreeN : τ / α + κ < (H.degree v₀ : ℝ) := by
            have hdeg := hdelete v₀ hv₀
            have hβscaled : 3200 * τ * (B.card : ℝ) /
                Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) =
                  3200 * (τ / α) := by
              calc
                _ = 3200 * τ * ((B.card : ℝ) /
                    Real.sqrt ((A.card : ℝ) * (B.card : ℝ))) := by ring
                _ = 3200 * τ * (1 / α) := by rw [hβ]
                _ = 3200 * (τ / α) := by ring
            rw [hβscaled] at hdeg
            have hratio : 0 ≤ τ / α := (div_pos hτpos hαpos).le
            nlinarith [hdeg]
          have hnDegree : n ≤ H.degree v₀ := by
            apply Nat.ceil_le.mpr
            change τ / α + (t : ℝ) - 2 ≤ (H.degree v₀ : ℝ)
            linarith [hκR, hdegreeN]
          have hnNeighbor : n ≤ (H.neighborFinset v₀).card := by
            simpa only [H.card_neighborFinset_eq_degree] using hnDegree
          obtain ⟨X, hX, hXcard⟩ := Finset.exists_subset_card_eq hnNeighbor
          have hX2 : 2 ≤ X.card := by omega
          let A₀ := sampledLeftVertices H A X v₀
          have hAX : Disjoint A₀ X :=
            sampledLeftVertices_disjoint_neighbors H A B X hBip v₀ hv₀ hX
          have hchoices : ∀ w ∈ A₀, ∃ x ∈ X, H.Adj w x :=
            sampledLeftVertices_has_choice H A X v₀
          have hvA₀ : v₀ ∉ A₀ := by
            simp [A₀, sampledLeftVertices]
          have hvX : v₀ ∉ X := by
            intro hvX
            have hadj : H.Adj v₀ v₀ :=
              (H.mem_neighborFinset v₀ v₀).mp (hX hvX)
            exact H.irrefl hadj
          let s : ℕ := Nat.ceil (1600 * α * τ)
          have hs : 1600 * α * τ ≤ (s : ℝ) := Nat.le_ceil _
          have hcommon : ∀ x y : ↥(X : Set W), x ≠ y →
              s ≤ (starCommonNeighbors H A₀ X x y).card := by
            intro x y hxy
            have hxy' : x.1 ≠ y.1 := fun heq => hxy (Subtype.ext heq)
            have hp := hpair x.1 y.1 (hX x.property) (hX y.property) hxy'
            have hceil : s ≤
                ((H.neighborFinset x.1 ∩ H.neighborFinset y.1).erase v₀).card :=
              Nat.ceil_le.mpr (le_of_lt hp)
            exact hceil.trans
              (common_neighbors_le_sampled_star_common H A B X hBip v₀ hv₀ hX x y)
          have hneighbor : ∀ x ∈ X, H.Adj v₀ x := by
            intro x hx
            exact (H.mem_neighborFinset v₀ x).mp (hX hx)
          by_cases hsmallExp :
              ((X.card.choose 2 : ℕ) : ℝ) *
                Real.exp (-(2 * (s : ℝ) / (X.card : ℝ))) < 1
          · have htX : t ≤ X.card + 1 := by omega
            have hKt := hasCliqueMinor_of_star_pair_expect_lt_one
              H A₀ X hAX v₀ hvA₀ hvX hneighbor s t hX2 htX
                hchoices hcommon hsmallExp
            exact hminorH hKt
          · have hchoose : ((n.choose 2 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
              rw [Nat.cast_choose_two]
              have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
              nlinarith
            have hnot : (1 : ℝ) ≤ ((n.choose 2 : ℕ) : ℝ) *
                Real.exp (-(2 * (s : ℝ) / (n : ℝ))) := by
              simpa only [hXcard] using le_of_not_gt hsmallExp
            have hLarge : (1 : ℝ) ≤ (n : ℝ) ^ 2 *
                Real.exp (-(2 * (s : ℝ) / (n : ℝ))) := by
              nlinarith [mul_nonneg (sub_nonneg.mpr hchoose)
                (Real.exp_pos (-(2 * (s : ℝ) / (n : ℝ)))).le]
            have hτsq' : τ ^ 2 = (t : ℝ) ^ 2 * Real.log (t : ℝ) := hτsq
            obtain ⟨hn9, hpower⟩ := near_complete_power_of_sample_failure
              t n ht (by omega) τ α (s : ℝ) hτpos hαge
              hτsq' hnlow hnup hs hLarge
            obtain ⟨J, hJminor, hmissing⟩ :=
              exists_star_contraction_minor_with_few_missing_edges
                H A₀ X hAX s hX2 hchoices hcommon
            have hXsize : Fintype.card ↥(X : Set W) = n := by
              have hcardX : Fintype.card ↥(X : Set W) = X.card := by
                apply Fintype.card_of_subtype
                intro z
                simp
              rw [hcardX, hXcard]
            have hmissing' : (edgeCount Jᶜ : ℝ) ≤
                ((n.choose 2 : ℕ) : ℝ) *
                  Real.exp (-(2 * (s : ℝ) / (n : ℝ))) := by
              simpa only [hXcard] using hmissing
            have hpowerActual := near_complete_power_of_missing_count_bound
              t n (n / (9 * t)) (edgeCount Jᶜ) hn2 (s : ℝ)
              hmissing' hpower
            have hKtJ : HasCliqueMinor J t := by
              apply hasCliqueMinor_of_near_complete_power_bound J t ht
              · simpa only [hXsize] using hn9
              · simpa only [hXsize] using hpowerActual
            exact hminorH (hasCliqueMinor_of_minor hJminor hKtJ)
      by_cases horder : R.card ≤ L.card
      · exact ordered L R hH hcoverH horder
      · have horder' : L.card ≤ R.card := Nat.le_of_not_ge horder
        have hcoverSwap : R ∪ L = Finset.univ := by
          simpa [Finset.union_comm] using hcoverH
        have h := ordered R L hH.symm hcoverSwap horder'
        simpa only [mul_comm (R.card : ℝ) (L.card : ℝ),
          add_comm (R.card : ℝ) (L.card : ℝ)] using h
  exact main (Fintype.card V) V G A B hG hcover hminor rfl

end HadwigerLean