import HadwigerLean.Graph.CliqueDensity.Reduction
import HadwigerLean.Graph.UniversalVertexMinor
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# The first clique-density base case

Positive edge density forces an edge and hence a two-vertex clique minor.
The higher finite base cases use the neighborhood reduction in Appendix E.
-/

namespace HadwigerLean

universe u

variable {V : Type u} [Fintype V]

/-- Any edge gives a `K₂` minor with singleton branch sets. -/
theorem hasCliqueMinor_two_of_adj (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b) : HasCliqueMinor G 2 := by
  classical
  let f : Fin 2 → V := fun i => if i = 0 then a else b
  have hne : a ≠ b := hab.ne
  have hinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f, hne, hne.symm] at hij ⊢
  have hadj : ∀ ⦃i j : Fin 2⦄, i ≠ j → G.Adj (f i) (f j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f, hab, hab.symm] at hij ⊢
  refine ⟨{
    branch := fun i => {f i}
    connected := by intro i; simp
    disjoint := by
      intro i j hij
      simpa using hinj.ne hij
    adjacent := by
      intro i j hij
      exact ⟨f i, by simp, f j, by simp, hadj (by simpa using hij)⟩
  }⟩

/-- The `r=2` case of the clique-density theorem needs only positivity. -/
theorem hasCliqueMinor_two_of_edgeDensity_pos (G : SimpleGraph V)
    (hdense : 0 < edgeDensity G) : HasCliqueMinor G 2 := by
  classical
  have hepos : 0 < edgeCount G := by
    by_contra he
    have hzero : edgeCount G = 0 := by omega
    simp [edgeDensity, hzero] at hdense
  have hfinpos : 0 < G.edgeFinset.card := by
    rw [← edgeCount_eq_card_edgeFinset]
    exact hepos
  obtain ⟨e, he⟩ := Finset.card_pos.mp hfinpos
  induction e using Sym2.ind with
  | _ a b =>
    have hab : G.Adj a b := by simpa [SimpleGraph.mem_edgeFinset] using he
    exact hasCliqueMinor_two_of_adj G hab


/-- The first exponential-density case: a graph with at least one edge per
vertex has a triangle minor. -/
theorem hasCliqueMinor_three_of_edges_ge_card (G : SimpleGraph V)
    (hnonempty : 0 < Fintype.card V)
    (hdense : Fintype.card V ≤ edgeCount G) :
    HasCliqueMinor G 3 := by
  classical
  obtain ⟨W, instW, H, instEq, instAdj, v, hminor, _hexact,
    hnoiso, _hdeg, hneighbor⟩ :=
    exists_dense_neighborhood_minor G 1 (by omega) hnonempty
      (by simpa using hdense)
  letI : Fintype W := instW
  letI : DecidableEq W := instEq
  letI : DecidableRel H.Adj := instAdj
  let J := H.induce (H.neighborSet v)
  have hpos : 0 < Fintype.card (H.neighborSet v) := by
    simpa only [← H.card_neighborSet_eq_degree] using hnoiso v
  obtain ⟨w⟩ := Fintype.card_pos_iff.mp hpos
  have hwpos : 0 < J.degree w := by
    have h : 1 ≤ J.degree w := hneighbor w
    omega
  have hnpos : 0 < Fintype.card (J.neighborSet w) := by
    simpa only [← J.card_neighborSet_eq_degree] using hwpos
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp hnpos
  have htwo : HasCliqueMinor J 2 := hasCliqueMinor_two_of_adj J x.property
  have hthree : HasCliqueMinor H 3 :=
    hasCliqueMinor_succ_of_neighbor_minor H v htwo
  exact hasCliqueMinor_of_minor hminor hthree
/-- The exponential-density clique-minor bound used for the finite range of
the quantitative theorem. The induction itself is valid for every `r ≥ 3`. -/
theorem hasCliqueMinor_of_exponential_edges (r : ℕ) :
    ∀ {X : Type u} [Fintype X] (G : SimpleGraph X),
      3 ≤ r → 0 < Fintype.card X →
      2 ^ (r - 3) * Fintype.card X ≤ edgeCount G →
      HasCliqueMinor G r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro X instX G hr hpositive hdense
    letI : Fintype X := instX
    by_cases hbase : r = 3
    · subst r
      have hd : Fintype.card X ≤ edgeCount G := by simpa using hdense
      exact hasCliqueMinor_three_of_edges_ge_card G hpositive hd
    · have hr4 : 4 ≤ r := by omega
      let k := 2 ^ ((r - 1) - 3)
      have hkpos : 0 < k := by dsimp [k]; positivity
      have hpow : 2 ^ (r - 3) = 2 * k := by
        dsimp [k]
        have hsub : r - 3 = ((r - 1) - 3) + 1 := by omega
        rw [hsub, pow_succ]
        omega
      have hdense2 : (2 * k) * Fintype.card X ≤ edgeCount G := by
        simpa only [hpow] using hdense
      obtain ⟨W, instW, H, instEq, instAdj, v, hminor, _hexact,
        hnoiso, _hdeg, hneighbor⟩ :=
        exists_dense_neighborhood_minor G (2 * k) (by omega)
          hpositive hdense2
      letI : Fintype W := instW
      letI : DecidableEq W := instEq
      letI : DecidableRel H.Adj := instAdj
      let J := H.induce (H.neighborSet v)
      have hJpositive : 0 < Fintype.card (H.neighborSet v) := by
        simpa only [← H.card_neighborSet_eq_degree] using hnoiso v
      have hJmin : ∀ w : H.neighborSet v, 2 * k ≤ J.degree w := by
        intro w
        exact hneighbor w
      have hJdense : k * Fintype.card (H.neighborSet v) ≤ edgeCount J :=
        edgeCount_ge_card_mul_of_min_degree_twice J k hJmin
      have hJminor : HasCliqueMinor J (r - 1) := by
        exact ih (r - 1) (by omega) J (by omega) hJpositive hJdense
      have hHminor : HasCliqueMinor H ((r - 1) + 1) :=
        hasCliqueMinor_succ_of_neighbor_minor H v hJminor
      have hrstep : (r - 1) + 1 = r := by omega
      rw [hrstep] at hHminor
      exact hasCliqueMinor_of_minor hminor hHminor
/-- Appendix E's finite-range comparison, using certified logarithm bounds
for `log 2` and `log 3`. -/
theorem small_order_power_le_density_threshold (r : ℕ)
    (hr3 : 3 ≤ r) (hr12 : r ≤ 12) :
    (2 ^ (r - 3) : ℝ) ≤ 30 * (r : ℝ) * Real.sqrt (Real.log (r : ℝ)) := by
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    have h := Real.log_three_gt_d9
    norm_num at h ⊢
    linarith
  by_cases hr11 : r ≤ 11
  · have hnat : 2 ^ (r - 3) ≤ 30 * r := by
      interval_cases r <;> norm_num at *
    have hlog : (1 : ℝ) ≤ Real.log (r : ℝ) := by
      exact hlog3.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hr3))
    have hsqrt : (1 : ℝ) ≤ Real.sqrt (Real.log (r : ℝ)) := by
      simpa using Real.sqrt_le_sqrt hlog
    have hcast : (2 ^ (r - 3) : ℝ) ≤ 30 * (r : ℝ) := by exact_mod_cast hnat
    calc
      (2 ^ (r - 3) : ℝ) ≤ 30 * (r : ℝ) := hcast
      _ = 30 * (r : ℝ) * 1 := by ring
      _ ≤ 30 * (r : ℝ) * Real.sqrt (Real.log (r : ℝ)) :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)
  · have hr : r = 12 := by omega
    subst r
    have hlog12 : (9 / 4 : ℝ) ≤ Real.log 12 := by
      have h2 := Real.log_two_gt_d9
      have h3 := Real.log_three_gt_d9
      have heq : Real.log (12 : ℝ) = Real.log 3 + 2 * Real.log 2 := by
        rw [show (12 : ℝ) = 3 * 4 by norm_num, Real.log_mul (by norm_num) (by norm_num),
          Real.log_four_eq]
      rw [heq]
      norm_num at h2 h3 ⊢
      linarith
    have hsqrt : (3 / 2 : ℝ) ≤ Real.sqrt (Real.log 12) := by
      have h := Real.sqrt_le_sqrt hlog12
      norm_num at h ⊢
      exact h
    norm_num
    nlinarith
/-- The coefficient-30 clique-minor theorem for the finite range
`3 ≤ r ≤ 12`. -/
theorem hasCliqueMinor_of_edgeDensity_ge_small
    (G : SimpleGraph V) (r : ℕ) (hr3 : 3 ≤ r) (hr12 : r ≤ 12)
    (hdense : 30 * (r : ℝ) * Real.sqrt (Real.log (r : ℝ)) ≤
      edgeDensity G) :
    HasCliqueMinor G r := by
  have hpow : (2 ^ (r - 3) : ℝ) ≤ edgeDensity G :=
    (small_order_power_le_density_threshold r hr3 hr12).trans hdense
  have hpositive : 0 < Fintype.card V := by
    by_contra hzero
    have hz : Fintype.card V = 0 := by omega
    have hdz : edgeDensity G = 0 := by simp [edgeDensity, hz]
    rw [hdz] at hpow
    have hp : (0 : ℝ) < 2 ^ (r - 3) := by positivity
    exact (not_le_of_gt hp) hpow
  have hpowNat : ((2 ^ (r - 3) : ℕ) : ℝ) ≤ edgeDensity G := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hpow
  have hcount : 2 ^ (r - 3) * Fintype.card V ≤ edgeCount G :=
    edgeCount_ge_card_mul_of_edgeDensity_ge G _ hpowNat
  exact hasCliqueMinor_of_exponential_edges r G hr3 hpositive hcount

/-- The coefficient-30 theorem also holds at `r=2`. -/
theorem hasCliqueMinor_two_of_edgeDensity_ge_threshold
    (G : SimpleGraph V)
    (hdense : 30 * (2 : ℝ) * Real.sqrt (Real.log (2 : ℝ)) ≤
      edgeDensity G) :
    HasCliqueMinor G 2 := by
  have hlog : 0 < Real.log (2 : ℝ) := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hsqrt : 0 < Real.sqrt (Real.log (2 : ℝ)) := Real.sqrt_pos.2 hlog
  have hpos : 0 < edgeDensity G := by nlinarith
  exact hasCliqueMinor_two_of_edgeDensity_pos G hpos

/-- Appendix E's numerical finite-range case, including the edge case
`r=2`. -/
theorem hasCliqueMinor_of_edgeDensity_ge_twelve
    (G : SimpleGraph V) (r : ℕ) (hr2 : 2 ≤ r) (hr12 : r ≤ 12)
    (hdense : 30 * (r : ℝ) * Real.sqrt (Real.log (r : ℝ)) ≤
      edgeDensity G) :
    HasCliqueMinor G r := by
  by_cases hr : r = 2
  · subst r
    exact hasCliqueMinor_two_of_edgeDensity_ge_threshold G hdense
  · exact hasCliqueMinor_of_edgeDensity_ge_small G r (by omega) hr12 hdense
end HadwigerLean
