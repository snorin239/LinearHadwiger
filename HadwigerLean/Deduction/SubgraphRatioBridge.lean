import HadwigerLean.Deduction.Theorem4Scale
import HadwigerLean.Graph.SubgraphImageIso
import HadwigerLean.Deduction.ExternalInputs
import HadwigerLean.Deduction.SubgraphRatioNumerics
import Mathlib.Tactic

/-! Ratio-set estimates for the final Theorem 4 comparison. -/

namespace HadwigerLean.Deduction

universe u

/-- A specific admissible subgraph ratio is bounded by the finite maximum
in the exact paper statement. -/
theorem theorem4_candidate_le_max
    {V : Type u} [Fintype V] (G : SimpleGraph V) (C t q : ℕ)
    (H : G.Subgraph)
    (hwindow : (t : ℝ) / Real.sqrt (Real.log (t : ℝ)) ≤ (q : ℝ))
    (hq : q ≤ t)
    (hminor : ¬ HadwigerLean.HasCliqueMinor H.coe q)
    (horder : (Nat.card H.verts : ℝ) ≤
      (C : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ (4 : ℝ)) :
    (HadwigerLean.chromatic H.coe : ℝ) / (q : ℝ) ≤
      theorem4MaxRatio G C t := by
  classical
  have hmem : (HadwigerLean.chromatic H.coe : ℝ) / (q : ℝ) ∈
      theorem4RatioSet G C t := by
    change _ ∈ ({0} ∪ {r : ℝ | ∃ (a : ℕ) (J : G.Subgraph),
      (t : ℝ) / Real.sqrt (Real.log (t : ℝ)) ≤ (a : ℝ) ∧
      a ≤ t ∧ ¬ HadwigerLean.HasCliqueMinor J.coe a ∧
      (Fintype.card J.verts : ℝ) ≤
        (C : ℝ) * (a : ℝ) * (Real.log (a : ℝ)) ^ (4 : ℝ) ∧
      r = (HadwigerLean.chromatic J.coe : ℝ) / (a : ℝ)})
    have horderF : (Fintype.card H.verts : ℝ) ≤
        (C : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ (4 : ℝ) := by
      simpa only [Nat.card_eq_fintype_card] using horder
    exact Or.inr ⟨q, H, hwindow, hq, hminor, horderF, rfl⟩
  exact le_csSup (theorem4RatioSet_bddAbove G C t) hmem

/-- The lower endpoint of the paper's scale window is no greater than `t`
for `t ≥ 3`. -/
theorem dp_window_le_self (t : ℕ) (ht : 3 ≤ t) :
    (t : ℝ) / Real.sqrt (Real.log (t : ℝ)) ≤ (t : ℝ) := by
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hlog : 1 ≤ Real.log (t : ℝ) := by
    have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_three]
    exact hlog3.trans (Real.log_le_log (by norm_num)
      (by exact_mod_cast ht))
  have hroot : 1 ≤ Real.sqrt (Real.log (t : ℝ)) :=
    (Real.one_le_sqrt).2 hlog
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hroot)).2
  nlinarith

/-- Any candidate with order above `t` is affordable at the denominator
`t`, using the coefficient `3^9`. The graph hypothesis records that the
ambient graph is `K_t`-minor-free. -/
theorem theorem4_large_order_candidate_le_max
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (D t q : ℕ) (ht : 3 ≤ t) (htq : t < q)
    (hq : q ≤ 42 * t) (H : G.Subgraph)
    (hminor : ¬ HadwigerLean.HasCliqueMinor H.coe t)
    (horder : (Nat.card H.verts : ℝ) ≤
      (D : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ (4 : ℝ)) :
    (HadwigerLean.chromatic H.coe : ℝ) / (q : ℝ) ≤
      theorem4MaxRatio G (3 ^ 9 * D) t := by
  have hbud : (q : ℝ) * (Real.log (q : ℝ)) ^ (4 : ℝ) ≤
      (3 ^ 9 : ℕ) * (t : ℝ) * (Real.log (t : ℝ)) ^ (4 : ℝ) := by
    convert fortytwo_order_log_budget t q ht hq using 1 <;>
      norm_num [Real.rpow_natCast]
  have hneworder : (Nat.card H.verts : ℝ) ≤
      ((3 ^ 9 * D : ℕ) : ℝ) * (t : ℝ) *
        (Real.log (t : ℝ)) ^ (4 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hbud (by positivity : 0 ≤ (D : ℝ))
    calc
      (Nat.card H.verts : ℝ) ≤
          (D : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ (4 : ℝ) := horder
      _ = (D : ℝ) * ((q : ℝ) * (Real.log (q : ℝ)) ^ (4 : ℝ)) := by ring
      _ ≤ (D : ℝ) * ((3 ^ 9 : ℕ) * (t : ℝ) *
          (Real.log (t : ℝ)) ^ (4 : ℝ)) := hh
      _ = ((3 ^ 9 * D : ℕ) : ℝ) * (t : ℝ) *
          (Real.log (t : ℝ)) ^ (4 : ℝ) := by push_cast; ring
  have hratio := theorem4_candidate_le_max G (3 ^ 9 * D) t t H
    (dp_window_le_self t ht) le_rfl hminor hneworder
  have hratio' : (HadwigerLean.chromatic H.coe : ℝ) / (q : ℝ) ≤
      (HadwigerLean.chromatic H.coe : ℝ) / (t : ℝ) := by
    apply div_le_div_of_nonneg_left (by positivity)
      (by exact_mod_cast (by omega : 0 < t))
    exact_mod_cast htq.le
  exact hratio'.trans hratio


/-- Every candidate in the enlarged scale window of an induced subgraph
contributes at most the exact paper maximum of the original host graph.
The two branches correspond to `q ≤ t` and `q > t`. -/
theorem induce_large_window_candidate_le_theorem4_max
    {V : Type u} [Fintype V] (G : SimpleGraph V) (U : Finset V)
    (D t T q : ℕ) (ht : 3 ≤ t) (htT : t ≤ T) (hTlt : T < 3 * t)
    (hwindow : (T : ℝ) / Real.sqrt (Real.log (T : ℝ)) ≤ (q : ℝ))
    (hq : q ≤ 14 * T)
    (hGminor : ¬ HadwigerLean.HasCliqueMinor G t)
    (H : (G.induce (U : Set V)).Subgraph)
    (hHminor : ¬ HadwigerLean.HasCliqueMinor H.coe q)
    (horder : (Nat.card H.verts : ℝ) ≤
      (D : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ (4 : ℝ)) :
    (HadwigerLean.chromatic H.coe : ℝ) / (q : ℝ) ≤
      theorem4MaxRatio G (3 ^ 9 * D) t := by
  classical
  let f : G.induce (U : Set V) ↪g G := SimpleGraph.Embedding.induce _
  let J : G.Subgraph := H.map f.toHom
  let e : H.coe ≃g J.coe := subgraphMapIso f H
  have hcard : Nat.card J.verts = Nat.card H.verts := by
    have hc : Fintype.card H.verts = Fintype.card J.verts :=
      Fintype.card_congr e.toEquiv
    simpa only [Nat.card_eq_fintype_card] using hc.symm
  have hχ : HadwigerLean.chromatic H.coe =
      HadwigerLean.chromatic J.coe := by
    unfold HadwigerLean.chromatic
    exact congrArg ENat.toNat (SimpleGraph.chromaticNumber_congr e)
  have hJorder : (Nat.card J.verts : ℝ) ≤
      (D : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ (4 : ℝ) := by
    rw [hcard]
    exact horder
  have hJminorq : ¬ HadwigerLean.HasCliqueMinor J.coe q := by
    intro h
    exact hHminor (HadwigerLean.hasCliqueMinor_map e.symm.toHom
      e.symm.injective h)
  have hJminort : ¬ HadwigerLean.HasCliqueMinor J.coe t := by
    intro h
    exact hGminor (HadwigerLean.hasCliqueMinor_map J.hom
      (by intro x y hxy; exact Subtype.ext hxy) h)
  have hresult : (HadwigerLean.chromatic J.coe : ℝ) / (q : ℝ) ≤
      theorem4MaxRatio G (3 ^ 9 * D) t := by
    by_cases hqt : q ≤ t
    · have hwin : (t : ℝ) / Real.sqrt (Real.log (t : ℝ)) ≤
          (q : ℝ) :=
        (dp_window_mono (by exact_mod_cast ht)
          (by exact_mod_cast htT)).trans hwindow
      have hC : (D : ℝ) ≤ ((3 ^ 9 * D : ℕ) : ℝ) := by
        exact_mod_cast (show D ≤ 3 ^ 9 * D by omega)
      have hfactor : 0 ≤ (q : ℝ) *
          (Real.log (q : ℝ)) ^ (4 : ℝ) := by
        positivity
      have hbig : (Nat.card J.verts : ℝ) ≤
          ((3 ^ 9 * D : ℕ) : ℝ) * (q : ℝ) *
            (Real.log (q : ℝ)) ^ (4 : ℝ) := by
        have hh := mul_le_mul_of_nonneg_right hC hfactor
        calc
          (Nat.card J.verts : ℝ) ≤
              (D : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ (4 : ℝ) := hJorder
          _ = (D : ℝ) * ((q : ℝ) * (Real.log (q : ℝ)) ^ (4 : ℝ)) := by ring
          _ ≤ ((3 ^ 9 * D : ℕ) : ℝ) *
                ((q : ℝ) * (Real.log (q : ℝ)) ^ (4 : ℝ)) := hh
          _ = ((3 ^ 9 * D : ℕ) : ℝ) * (q : ℝ) *
                (Real.log (q : ℝ)) ^ (4 : ℝ) := by ring
      exact theorem4_candidate_le_max G (3 ^ 9 * D) t q J
        hwin hqt hJminorq hbig
    · have htq : t < q := by omega
      have hq42 : q ≤ 42 * t := by omega
      exact theorem4_large_order_candidate_le_max G D t q ht htq
        hq42 J hJminort hJorder
  simpa only [hχ] using hresult

/-- The exact host maximum is nonnegative because its candidate set
contains zero. -/
theorem theorem4MaxRatio_nonneg
    {V : Type u} [Fintype V] (G : SimpleGraph V) (C t : ℕ) :
    0 ≤ theorem4MaxRatio G C t := by
  unfold theorem4MaxRatio
  apply le_csSup (theorem4RatioSet_bddAbove G C t)
  simp [theorem4RatioSet]

/-- The enlarged-scale maximum of any induced subgraph is bounded by the
exact ratio maximum from paper Theorem 4. -/
theorem theorem4ScaleMaxRatio_induce_le_theorem4MaxRatio
    {V : Type u} [Fintype V] (G : SimpleGraph V) (U : Finset V)
    (D t T : ℕ) (ht : 3 ≤ t) (htT : t ≤ T) (hTlt : T < 3 * t)
    (hGminor : ¬ HadwigerLean.HasCliqueMinor G t) :
    theorem4ScaleMaxRatio (G.induce (U : Set V)) D T ≤
      theorem4MaxRatio G (3 ^ 9 * D) t := by
  unfold theorem4ScaleMaxRatio
  apply csSup_le (theorem4ScaleRatioSet_nonempty
    (G.induce (U : Set V)) D T)
  intro r hr
  change r ∈ ({0} ∪ {s : ℝ | ∃ (q : ℕ)
    (H : (G.induce (U : Set V)).Subgraph),
    (T : ℝ) / Real.sqrt (Real.log (T : ℝ)) ≤ (q : ℝ) ∧
    q ≤ 14 * T ∧
    ¬ HadwigerLean.HasCliqueMinor H.coe q ∧
    (Nat.card H.verts : ℝ) ≤
      (D : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ (4 : ℝ) ∧
    s = (HadwigerLean.chromatic H.coe : ℝ) / (q : ℝ)}) at hr
  rcases hr with hr | ⟨q, H, hwindow, hq, hHminor, horder, rfl⟩
  · have hr0 : r = 0 := by simpa using hr
    simpa only [hr0] using theorem4MaxRatio_nonneg G (3 ^ 9 * D) t
  · exact induce_large_window_candidate_le_theorem4_max G U D t T q
      ht htT hTlt hwindow hq hGminor H hHminor horder
end HadwigerLean.Deduction








