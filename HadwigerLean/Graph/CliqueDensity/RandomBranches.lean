import HadwigerLean.Graph.CliqueDensity.SmallOrders
import HadwigerLean.Graph.CliqueDensity.Diameter
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Tactic

/-!
# Parameters for the large-order clique-minor construction

The parameters follow Appendix E: `s = ⌈4√(log r)⌉` and
`d = ⌊30r√(log r)⌋`.
-/

set_option maxHeartbeats 1000000

namespace HadwigerLean

/-- The elementary logarithm estimate needed for the branch-set budget. -/
theorem log_twelve_gt_nine_fourths :
    (9 / 4 : ℝ) < Real.log 12 := by
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_three_gt_d9
  have heq : Real.log (12 : ℝ) = Real.log 3 + 2 * Real.log 2 := by
    rw [show (12 : ℝ) = 3 * 4 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_four_eq]
  rw [heq]
  norm_num at h2 h3 ⊢
  linarith

/-- The total budget for `r` branch sets of size at most `s+8`.
This is the integer form of (E.4). -/
theorem clique_branch_budget (r : ℕ) (hr : 13 ≤ r) :
    3 * r * (Nat.ceil (4 * Real.sqrt (Real.log (r : ℝ))) + 8) ≤
      Nat.floor (30 * (r : ℝ) * Real.sqrt (Real.log (r : ℝ))) := by
  let L : ℝ := Real.log (r : ℝ)
  let x : ℝ := Real.sqrt L
  let s : ℕ := Nat.ceil (4 * x)
  let d : ℕ := Nat.floor (30 * (r : ℝ) * x)
  change 3 * r * (s + 8) ≤ d
  have hrreal : (12 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 12 ≤ r)
  have hlog : (9 / 4 : ℝ) < L :=
    lt_of_lt_of_le log_twelve_gt_nine_fourths
      (Real.log_le_log (by norm_num) hrreal)
  have hLnonneg : 0 ≤ L := by linarith
  have hxnonneg : 0 ≤ x := Real.sqrt_nonneg _
  have hxsq : x ^ 2 = L := Real.sq_sqrt hLnonneg
  have hx : (3 / 2 : ℝ) < x := by nlinarith
  have hs : (s : ℝ) < 4 * x + 1 := by
    exact Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * x)
  have hsbound : (s : ℝ) + 8 < 10 * x := by linarith
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hprod : (3 : ℝ) * (r : ℝ) * ((s : ℝ) + 8) <
      30 * (r : ℝ) * x := by
    have h := mul_lt_mul_of_pos_left hsbound (by positivity : 0 < (3 : ℝ) * r)
    nlinarith
  have hcast : ((3 * r * (s + 8) : ℕ) : ℝ) ≤ 30 * (r : ℝ) * x := by
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    exact hprod.le
  exact Nat.le_floor hcast

/-- In case (I) of (E.3), deleting fewer than `d/3` vertices
leaves minimum degree greater than two fifths of the remaining order. -/
theorem residual_ratio_case_one (d m b : ℕ)
    (hm : m ≤ 2 * d) (hb : 3 * b < d) :
    2 * (m - b) < 5 * (d - b) := by
  omega

/-- The analogous two-fifths ratio in case (II) of (E.3). -/
theorem residual_ratio_case_two (d δ m b : ℕ)
    (hm : m ≤ d) (hδ : 2 * d < 3 * δ) (hb : 3 * b < d) :
    2 * (m - b) < 5 * (δ - b) := by
  omega
universe u

variable {V : Type u} [Fintype V]

/-- An inclusion-exclusion form of the common-neighborhood bound. -/
theorem degree_sum_le_order_add_common_neighbor_card
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V) :
    G.degree x + G.degree y ≤ Fintype.card V +
      (G.neighborFinset x ∩ G.neighborFinset y).card := by
  classical
  have hsum := Finset.card_union_add_card_inter
    (G.neighborFinset x) (G.neighborFinset y)
  have hbound : (G.neighborFinset x ∪ G.neighborFinset y).card ≤
      Fintype.card V :=
    Finset.card_le_card (Finset.subset_univ _)
  rw [← G.card_neighborFinset_eq_degree,
    ← G.card_neighborFinset_eq_degree]
  omega

/-- If every degree is large enough that any two vertices retain a common
neighbor after fewer than `k` deletions, then the graph is `k`-connected. -/
theorem vertexConnected_of_degree_bound
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (horder : k < Fintype.card V)
    (hdegree : ∀ v : V, Fintype.card V + k ≤ 2 * G.degree v) :
    VertexConnected G k := by
  classical
  refine ⟨horder, ?_⟩
  intro U hU
  have hcard : Fintype.card ↥((U : Set V)ᶜ) + U.card = Fintype.card V := by
    have hc : Fintype.card ↥((U : Set V)ᶜ) = (Uᶜ : Finset V).card := by
      apply Fintype.card_of_subtype
      intro x
      simp
    rw [hc]
    exact Finset.card_compl_add_card U
  have hpositive : 0 < Fintype.card ↥((U : Set V)ᶜ) := by omega
  letI : Nonempty ↥((U : Set V)ᶜ) := Fintype.card_pos_iff.mp hpositive
  refine (SimpleGraph.connected_iff _).mpr ⟨?_, inferInstance⟩
  intro x y
  have hcommon : k ≤
      (G.neighborFinset x.1 ∩ G.neighborFinset y.1).card := by
    have hx := hdegree x.1
    have hy := hdegree y.1
    have hsum := degree_sum_le_order_add_common_neighbor_card G x.1 y.1
    omega
  have hnotSub : ¬
      G.neighborFinset x.1 ∩ G.neighborFinset y.1 ⊆ U := by
    intro hsub
    have hc := Finset.card_le_card hsub
    omega
  obtain ⟨z, hz, hzU⟩ := Finset.not_subset.mp hnotSub
  have hxz : G.Adj x.1 z := (G.mem_neighborFinset x.1 z).mp (Finset.mem_inter.mp hz).1
  have hyz : G.Adj y.1 z := (G.mem_neighborFinset y.1 z).mp (Finset.mem_inter.mp hz).2
  have hxz' : (G.induce (U : Set V)ᶜ).Adj x ⟨z, hzU⟩ := hxz
  have hyz' : (G.induce (U : Set V)ᶜ).Adj y ⟨z, hzU⟩ := hyz
  exact hxz'.reachable.trans hyz'.symm.reachable
/-- A disconnected finite graph has a nonempty side of a cut containing at
most half its vertices. The cut has no crossing edge. -/
theorem exists_small_noncross_side_of_not_connected
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hpositive : 0 < Fintype.card V) (hnot : ¬ G.Connected) :
    ∃ C : Finset V, C.Nonempty ∧
      (∃ y : V, y ∉ C) ∧
      2 * C.card ≤ Fintype.card V ∧
      (∀ ⦃a b : V⦄, a ∈ C → b ∉ C → ¬ G.Adj a b) := by
  classical
  have hnotpre : ¬ G.Preconnected := by
    intro hp
    exact hnot ((SimpleGraph.connected_iff G).mpr
      ⟨hp, Fintype.card_pos_iff.mp hpositive⟩)
  change ¬ (∀ a b : V, G.Reachable a b) at hnotpre
  push_neg at hnotpre
  obtain ⟨x, y, hxy⟩ := hnotpre
  let A : Finset V := Finset.univ.filter (fun z => G.Reachable x z)
  let B : Finset V := Aᶜ
  have hxA : x ∈ A := by simp [A]
  have hyB : y ∈ B := by simp [A, B, hxy]
  have hcard : A.card + B.card = Fintype.card V := by
    have h := Finset.card_compl_add_card A
    dsimp [B]
    omega
  have hnocross : ∀ ⦃a b : V⦄, a ∈ A → b ∈ B → ¬ G.Adj a b := by
    intro a b ha hb hab
    have hxa : G.Reachable x a := (Finset.mem_filter.mp ha).2
    have hxb : G.Reachable x b := hxa.trans hab.reachable
    have hbA : b ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxb⟩
    exact (Finset.mem_compl.mp hb) hbA
  by_cases hAB : A.card ≤ B.card
  · refine ⟨A, ⟨x, hxA⟩, ⟨y, ?_⟩, by omega, ?_⟩
    · exact Finset.mem_compl.mp hyB
    · intro a b ha hb hab
      exact hnocross ha (Finset.mem_compl.mpr hb) hab
  · refine ⟨B, ⟨y, hyB⟩, ⟨x, ?_⟩, by omega, ?_⟩
    · simpa [B] using hxA
    · intro a b ha hb hab
      have hbA : b ∈ A := by simpa [B] using hb
      exact hnocross hbA ha hab.symm
/-- A side of an edge cut retains every degree when taken as an induced
subgraph. -/
theorem degree_induce_of_noncross
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V)
    (hnocross : ∀ ⦃a b : V⦄, a ∈ C → b ∉ C → ¬ G.Adj a b)
    (w : (C : Set V)) :
    (G.induce (C : Set V)).degree w = G.degree w := by
  classical
  let e : (G.induce (C : Set V)).neighborSet w ≃ G.neighborSet w.1 := {
    toFun := fun z => ⟨z.1.1, z.property⟩
    invFun := fun z => ⟨⟨z.1, by
      by_contra hz
      exact (hnocross w.property hz) z.property⟩, z.property⟩
    left_inv := by intro z; apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := by intro z; apply Subtype.ext; rfl
  }
  rw [← (G.induce (C : Set V)).card_neighborSet_eq_degree,
    ← G.card_neighborSet_eq_degree]
  exact Fintype.card_congr e
/-- The connected core dichotomy (E.3). From an order-`2d` graph of
minimum degree `d`, it extracts a `k`-connected induced minor, either
unchanged or with order at most `d` and minimum degree above `2d/3`. -/
theorem exists_connected_dense_core
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d k : ℕ) (hk : 0 < k) (hthree : 3 * k ≤ d)
    (hpositive : 0 < Fintype.card V)
    (horderBound : Fintype.card V ≤ 2 * d)
    (hdegree : ∀ v : V, d ≤ G.degree v) :
    ∃ (X : Type u) (_ : Fintype X) (F : SimpleGraph X)
      (_ : DecidableRel F.Adj),
      IsMinor F G ∧ VertexConnected F k ∧
      ((Fintype.card X ≤ 2 * d ∧ ∀ x : X, d ≤ F.degree x) ∨
       (Fintype.card X ≤ d ∧ ∀ x : X, 2 * d < 3 * F.degree x)) := by
  classical
  have horder : k < Fintype.card V := by
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp hpositive
    have hdeglt := G.degree_lt_card_verts v
    have hd := hdegree v
    omega
  by_cases hconnected : VertexConnected G k
  · exact ⟨V, inferInstance, G, inferInstance, IsMinor.refl G,
      hconnected, Or.inl ⟨horderBound, hdegree⟩⟩
  · have hsep : ∃ U : Finset V, U.card < k ∧
        ¬ (G.induce (U : Set V)ᶜ).Connected := by
      by_contra h
      apply hconnected
      refine ⟨horder, ?_⟩
      intro U hU
      by_contra hc
      exact h ⟨U, hU, hc⟩
    obtain ⟨U, hU, hnotJ⟩ := hsep
    let S : Set V := (U : Set V)ᶜ
    let J : SimpleGraph S := G.induce S
    letI : DecidableRel J.Adj := fun x y => (inferInstance : DecidableRel G.Adj) x.1 y.1
    letI : DecidableEq S := Classical.decEq S
    letI : DecidableRel J.Adj := Classical.decRel J.Adj
    have hJcard : Fintype.card S + U.card = Fintype.card V := by
      have hc : Fintype.card S = (Uᶜ : Finset V).card := by
        apply Fintype.card_of_subtype
        intro x
        simp [S]
      rw [hc]
      exact Finset.card_compl_add_card U
    have hJpositive : 0 < Fintype.card S := by omega
    have hnotJ' : ¬ J.Connected := hnotJ
    obtain ⟨C, hCnonempty, _hCproper, hCsmall, hnocross⟩ :=
      exists_small_noncross_side_of_not_connected J hJpositive hnotJ'
    let F : SimpleGraph (C : Set S) := J.induce (C : Set S)
    letI : DecidableEq (C : Set S) := Classical.decEq (C : Set S)
    letI : DecidableRel F.Adj := Classical.decRel F.Adj
    have hForder : Fintype.card (C : Set S) ≤ d := by
      have hc : Fintype.card (C : Set S) = C.card := by
        apply Fintype.card_of_subtype
        intro x
        simp
      rw [hc]
      omega
    have hFdegree : ∀ w : (C : Set S),
        d ≤ F.degree w + U.card := by
      intro w
      have heq : F.degree w = J.degree w :=
        degree_induce_of_noncross J C hnocross w
      have hdelete := degree_le_degree_induce_compl_add_card
        G U w.1.1 w.1.property
      have hd := hdegree w.1.1
      rw [heq]
      exact hd.trans hdelete
    have hForderGt : k < Fintype.card (C : Set S) := by
      obtain ⟨w, hw⟩ := hCnonempty
      let z : (C : Set S) := ⟨w, hw⟩
      have hdeglt := F.degree_lt_card_verts z
      have hd := hFdegree z
      omega
    have hFconn : VertexConnected F k := by
      apply vertexConnected_of_degree_bound F k hForderGt
      intro w
      have hd := hFdegree w
      omega
    have hFstrong : ∀ w : (C : Set S), 2 * d < 3 * F.degree w := by
      intro w
      have hd := hFdegree w
      omega
    have hminorFG : IsMinor F G :=
      IsMinor.trans (induce_isMinor J (C : Set S))
        (induce_isMinor G S)
    exact ⟨(C : Set S), inferInstance, F, inferInstance, hminorFG,
      hFconn, Or.inr ⟨hForder, hFstrong⟩⟩
/-- Apply the connected-core dichotomy to the neighborhood supplied by the
minimal dense-minor reduction. -/
theorem exists_dense_connected_core_from_edges
    (G : SimpleGraph V) (d k : ℕ)
    (hd : 1 ≤ d) (hk : 0 < k) (hthree : 3 * k ≤ d)
    (hnonempty : 0 < Fintype.card V)
    (hdense : d * Fintype.card V ≤ edgeCount G) :
    ∃ (X : Type u) (_ : Fintype X) (F : SimpleGraph X)
      (_ : DecidableRel F.Adj),
      IsMinor F G ∧ VertexConnected F k ∧
      ((Fintype.card X ≤ 2 * d ∧ ∀ x : X, d ≤ F.degree x) ∨
       (Fintype.card X ≤ d ∧ ∀ x : X, 2 * d < 3 * F.degree x)) := by
  classical
  obtain ⟨W, instW, H, instEq, instAdj, v, hminorHG, _hexact,
    hnoiso, hvdegree, hneighbor⟩ :=
    exists_dense_neighborhood_minor G d hd hnonempty hdense
  letI : Fintype W := instW
  letI : DecidableEq W := instEq
  letI : DecidableRel H.Adj := instAdj
  let J := H.induce (H.neighborSet v)
  have hJpositive : 0 < Fintype.card (H.neighborSet v) := by
    simpa only [← H.card_neighborSet_eq_degree] using hnoiso v
  have hJorder : Fintype.card (H.neighborSet v) ≤ 2 * d := by
    simpa only [H.card_neighborSet_eq_degree] using hvdegree
  have hJdegree : ∀ w : H.neighborSet v, d ≤ J.degree w := hneighbor
  obtain ⟨X, instX, F, instAdjF, hminorFJ, hconnected, hcase⟩ :=
    exists_connected_dense_core J d k hk hthree hJpositive hJorder hJdegree
  letI : Fintype X := instX
  letI : DecidableRel F.Adj := instAdjF
  have hminorJG : IsMinor J G :=
    IsMinor.trans (induce_isMinor H (H.neighborSet v)) hminorHG
  exact ⟨X, instX, F, instAdjF, IsMinor.trans hminorFJ hminorJG,
    hconnected, hcase⟩
/-- The old-branch failure probability in (E.7) is below `1/8`.
The fixed-size sampling argument only needs this numerical inequality. -/
theorem clique_branch_old_set_failure_bound (r : ℕ) (hr : 13 ≤ r) :
    (r : ℝ) *
      (4 * Real.exp (-(2 : ℝ) *
        (Nat.ceil (4 * Real.sqrt (Real.log (r : ℝ))) : ℝ) / 5)) ^
          (Nat.ceil (4 * Real.sqrt (Real.log (r : ℝ)))) <
      1 / 8 := by
  let L : ℝ := Real.log (r : ℝ)
  let x : ℝ := Real.sqrt L
  let s : ℕ := Nat.ceil (4 * x)
  let t : ℝ := s
  change (r : ℝ) * (4 * Real.exp (-2 * t / 5)) ^ s < 1 / 8
  have hrreal : (12 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 12 ≤ r)
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hlog : (9 / 4 : ℝ) < L :=
    lt_of_lt_of_le log_twelve_gt_nine_fourths
      (Real.log_le_log (by norm_num) hrreal)
  have hLnonneg : 0 ≤ L := by linarith
  have hxnonneg : 0 ≤ x := Real.sqrt_nonneg _
  have hxsq : x ^ 2 = L := Real.sq_sqrt hLnonneg
  have hx : (3 / 2 : ℝ) < x := by nlinarith
  have hst : 4 * x ≤ t := by
    exact Nat.le_ceil (4 * x)
  have ht : (0 : ℝ) ≤ t := by positivity
  have hlog4 : Real.log (4 : ℝ) < 7 / 5 := by
    rw [Real.log_four_eq]
    have h := Real.log_two_lt_d9
    norm_num at h ⊢
    linarith
  have hlog8 : Real.log (8 : ℝ) < 21 / 10 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    have h := Real.log_two_lt_d9
    norm_num at h ⊢
    linarith
  have hlogterm : t * Real.log 4 ≤ t * (7 / 5 : ℝ) :=
    mul_le_mul_of_nonneg_left hlog4.le ht
  have hfactor : 0 ≤ (t - 4 * x) * (2 * t + 8 * x - 7) :=
    mul_nonneg (by linarith) (by linarith)
  have hxFactor : 0 ≤ (x - 3 / 2) * (108 * x + 50) :=
    mul_nonneg (by linarith) (by linarith)
  have hpoly : L + t * Real.log 4 - 2 * t * t / 5 <
      -Real.log 8 := by
    rw [← hxsq]
    nlinarith [hfactor, hxFactor, hlogterm, hlog8]
  have hbasepos : 0 < 4 * Real.exp (-2 * t / 5) := by positivity
  have hproductpos : 0 < (r : ℝ) * (4 * Real.exp (-2 * t / 5)) ^ s := by
    positivity
  have hlogProduct :
      Real.log ((r : ℝ) * (4 * Real.exp (-2 * t / 5)) ^ s) =
        L + t * Real.log 4 - 2 * t * t / 5 := by
    rw [Real.log_mul hrpos.ne' (pow_ne_zero _ hbasepos.ne'),
      Real.log_pow, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
        (Real.exp_pos _).ne', Real.log_exp]
    dsimp [L, t]
    ring
  have hlogEighth : Real.log (1 / 8 : ℝ) = -Real.log 8 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (by norm_num : (8 : ℝ) ≠ 0)]
    simp
  apply (Real.log_lt_log_iff hproductpos (by norm_num : (0 : ℝ) < 1 / 8)).mp
  rw [hlogProduct, hlogEighth]
  exact hpoly
/-- The set of vertices seen in an ordered sample. Repetitions only
decrease its size. -/
def sampleRange [DecidableEq V] {s : ℕ} (ω : Fin s → V) : Finset V :=
  Finset.univ.image ω

theorem sampleRange_card_le [DecidableEq V] {s : ℕ} (ω : Fin s → V) :
    (sampleRange ω).card ≤ s := by
  simpa [sampleRange] using Finset.card_image_le (s := Finset.univ) (f := ω)

/-- Exactly `|A|^s` ordered samples of length `s` use only vertices in
`A`. -/
theorem card_sample_words_in [DecidableEq V] (A : Finset V) (s : ℕ) :
    Fintype.card {ω : Fin s → V // sampleRange ω ⊆ A} = A.card ^ s := by
  classical
  let e : {ω : Fin s → V // sampleRange ω ⊆ A} ≃ (Fin s → A) := {
    toFun := fun ω i => ⟨ω.1 i, ω.2 (Finset.mem_image.mpr
      ⟨i, Finset.mem_univ _, rfl⟩)⟩
    invFun := fun f => ⟨fun i => (f i).1, by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact (f i).property⟩
    left_inv := by intro ω; apply Subtype.ext; funext i; rfl
    right_inv := by intro f; funext i; apply Subtype.ext; rfl
  }
  rw [Fintype.card_congr e]
  simp

/-- The same count as a finite-set filter, convenient for double counting. -/
theorem card_filter_sample_words_in [DecidableEq V] (A : Finset V) (s : ℕ) :
    (Finset.univ.filter (fun ω : Fin s → V => sampleRange ω ⊆ A)).card =
      A.card ^ s := by
  classical
  have hcard : Fintype.card {ω : Fin s → V // sampleRange ω ⊆ A} =
      (Finset.univ.filter (fun ω : Fin s → V => sampleRange ω ⊆ A)).card := by
    apply Fintype.card_of_subtype
    intro ω
    simp
  rw [← hcard]
  exact card_sample_words_in A s
/-- Number of vertices with no sampled neighbor. -/
def undominatedCount [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {s : ℕ} (ω : Fin s → V) : ℕ :=
  (Finset.univ.filter
    (fun v : V => sampleRange ω ⊆ (G.neighborFinset v)ᶜ)).card

/-- A fixed vertex has no sampled neighbor in exactly
`(m-degree(v))^s` ordered samples. -/
theorem card_sample_words_undominated
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (s : ℕ) :
    (Finset.univ.filter
      (fun ω : Fin s → V =>
        sampleRange ω ⊆ (G.neighborFinset v)ᶜ)).card =
      (Fintype.card V - G.degree v) ^ s := by
  classical
  rw [card_filter_sample_words_in]
  simp only [Finset.card_compl, G.card_neighborFinset_eq_degree]

/-- Double counting the undominated vertices in every ordered sample. -/
theorem sum_undominatedCount
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) :
    (∑ ω : Fin s → V, undominatedCount G ω) =
      ∑ v : V, (Fintype.card V - G.degree v) ^ s := by
  classical
  have hdc :
      (∑ ω : Fin s → V, undominatedCount G ω) =
        ∑ v : V, (Finset.univ.filter
          (fun ω : Fin s → V =>
            sampleRange ω ⊆ (G.neighborFinset v)ᶜ)).card := by
    simpa [undominatedCount, Finset.bipartiteAbove,
      Finset.bipartiteBelow] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (r := fun ω : Fin s → V => fun v : V =>
          sampleRange ω ⊆ (G.neighborFinset v)ᶜ)
        (s := Finset.univ) (t := Finset.univ))
  rw [hdc]
  apply Finset.sum_congr rfl
  intro v _
  exact card_sample_words_undominated G v s
/-- Minimum degree bounds the total number of undominated vertices over all
ordered samples. -/
theorem sum_undominatedCount_le
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s δ : ℕ) (hmin : ∀ v : V, δ ≤ G.degree v) :
    (∑ ω : Fin s → V, undominatedCount G ω) ≤
      Fintype.card V * (Fintype.card V - δ) ^ s := by
  rw [sum_undominatedCount]
  calc
    (∑ v : V, (Fintype.card V - G.degree v) ^ s) ≤
        ∑ _v : V, (Fintype.card V - δ) ^ s := by
      apply Finset.sum_le_sum
      intro v _
      exact Nat.pow_le_pow_left (Nat.sub_le_sub_left (hmin v) _) s
    _ = Fintype.card V * (Fintype.card V - δ) ^ s := by simp
/-- Sampling with replacement gives the standard exponential avoidance bound. -/
theorem sub_pow_le_exp_bound (m δ s : ℕ)
    (hm : 0 < m) (hδ : δ ≤ m) :
    ((m - δ : ℕ) : ℝ) ^ s ≤
      (m : ℝ) ^ s * Real.exp (-(s : ℝ) * (δ : ℝ) / (m : ℝ)) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hexp := Real.add_one_le_exp (-(δ : ℝ) / (m : ℝ))
  have hbase : (m : ℝ) - (δ : ℝ) ≤
      (m : ℝ) * Real.exp (-(δ : ℝ) / (m : ℝ)) := by
    have hmult := mul_le_mul_of_nonneg_left hexp hmpos.le
    have hcancel : (m : ℝ) * ((δ : ℝ) / (m : ℝ)) = δ := by
      field_simp
    have heq : (m : ℝ) * (-(δ : ℝ) / (m : ℝ) + 1) =
        (m : ℝ) - (δ : ℝ) := by
      calc
        (m : ℝ) * (-(δ : ℝ) / (m : ℝ) + 1) =
            (m : ℝ) - (m : ℝ) * ((δ : ℝ) / (m : ℝ)) := by ring
        _ = (m : ℝ) - (δ : ℝ) := by rw [hcancel]
    rw [heq] at hmult
    exact hmult
  calc
    ((m - δ : ℕ) : ℝ) ^ s = ((m : ℝ) - (δ : ℝ)) ^ s := by
      rw [Nat.cast_sub hδ]
    _ ≤ ((m : ℝ) * Real.exp (-(δ : ℝ) / (m : ℝ))) ^ s := by
      exact pow_le_pow_left₀ (sub_nonneg.mpr (by exact_mod_cast hδ)) hbase _
    _ = (m : ℝ) ^ s * Real.exp (-(s : ℝ) * (δ : ℝ) / (m : ℝ)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
/-- Exponential upper bound for the total number of undominated vertices
over the uniform ordered sample space. -/
theorem sum_undominatedCount_le_exp
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s δ : ℕ) (hm : 0 < Fintype.card V)
    (hδ : δ ≤ Fintype.card V)
    (hmin : ∀ v : V, δ ≤ G.degree v) :
    (∑ ω : Fin s → V, (undominatedCount G ω : ℝ)) ≤
      (Fintype.card (Fin s → V) : ℝ) * (Fintype.card V : ℝ) *
        Real.exp (-(s : ℝ) * (δ : ℝ) / (Fintype.card V : ℝ)) := by
  let m := Fintype.card V
  have hsumNat := sum_undominatedCount_le G s δ hmin
  have hsumReal : (∑ ω : Fin s → V, (undominatedCount G ω : ℝ)) ≤
      (m : ℝ) * ((m - δ : ℕ) : ℝ) ^ s := by
    exact_mod_cast hsumNat
  have hpow := sub_pow_le_exp_bound m δ s hm hδ
  calc
    (∑ ω : Fin s → V, (undominatedCount G ω : ℝ)) ≤
        (m : ℝ) * ((m - δ : ℕ) : ℝ) ^ s := hsumReal
    _ ≤ (m : ℝ) *
        ((m : ℝ) ^ s * Real.exp (-(s : ℝ) * (δ : ℝ) / (m : ℝ))) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (Fintype.card (Fin s → V) : ℝ) * (m : ℝ) *
        Real.exp (-(s : ℝ) * (δ : ℝ) / (m : ℝ)) := by
      simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
      ring
/-- Every sampled connected component has a first sampled vertex, and
that vertex has no earlier sampled neighbor. -/
theorem sampled_component_count_le_first_without_neighbor
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {s : ℕ} (ω : Fin s → V) :
    Fintype.card
      (G.induce (sampleRange ω : Set V)).ConnectedComponent ≤
    (Finset.univ.filter (fun j : Fin s =>
      ∀ i : Fin s, i < j → ¬ G.Adj (ω i) (ω j))).card := by
  classical
  let B := sampleRange ω
  let J := G.induce (B : Set V)
  let sampled : Fin s → B := fun j =>
    ⟨ω j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  let comp : Fin s → J.ConnectedComponent :=
    fun j => J.connectedComponentMk (sampled j)
  have hsurj : Function.Surjective comp := by
    intro c
    obtain ⟨z, hz⟩ := c.nonempty_supp
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp z.property
    refine ⟨j, ?_⟩
    have hzj : sampled j = z := Subtype.ext hj
    change J.connectedComponentMk (sampled j) = c
    rw [hzj]
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff c z).mp hz
  let indices (c : J.ConnectedComponent) : Finset (Fin s) :=
    Finset.univ.filter (fun j => comp j = c)
  have hnonempty (c : J.ConnectedComponent) : (indices c).Nonempty := by
    obtain ⟨j, hj⟩ := hsurj c
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  let first (c : J.ConnectedComponent) : Fin s :=
    (indices c).min' (hnonempty c)
  have hfirst (c : J.ConnectedComponent) : comp (first c) = c :=
    (Finset.mem_filter.mp (Finset.min'_mem _ (hnonempty c))).2
  have hfirst_injective : Function.Injective first := by
    intro c d hcd
    calc
      c = comp (first c) := (hfirst c).symm
      _ = comp (first d) := by rw [hcd]
      _ = d := hfirst d
  have hfirst_good (c : J.ConnectedComponent) :
      ∀ i : Fin s, i < first c → ¬ G.Adj (ω i) (ω (first c)) := by
    intro i hi hadj
    have hadjJ : J.Adj (sampled i) (sampled (first c)) := hadj
    have hsame : comp i = comp (first c) :=
      SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadjJ
    have hiIndex : i ∈ indices c := by
      simp only [indices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hsame.trans (hfirst c)
    have hle : first c ≤ i := Finset.min'_le _ _ hiIndex
    omega
  let good : Finset (Fin s) :=
    Finset.univ.filter (fun j : Fin s =>
      ∀ i : Fin s, i < j → ¬ G.Adj (ω i) (ω j))
  let firstGood : J.ConnectedComponent → good :=
    fun c => ⟨first c, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hfirst_good c⟩⟩
  have hinj : Function.Injective firstGood := by
    intro c d hcd
    exact hfirst_injective (congrArg Subtype.val hcd)
  have hcard : Fintype.card J.ConnectedComponent ≤ Fintype.card good :=
    Fintype.card_le_of_injective firstGood hinj
  have hgoodCard : Fintype.card good = good.card := Fintype.card_coe good
  rw [hgoodCard] at hcard
  exact hcard
/-- Independent coordinate restrictions on an ordered sample multiply
their counts. -/
theorem card_constrained_words [DecidableEq V] (s : ℕ)
    (allowed : Fin s → Finset V) :
    Fintype.card
      {ω : Fin s → V // ∀ i : Fin s, ω i ∈ allowed i} =
      ∏ i : Fin s, (allowed i).card := by
  classical
  let e :
      {ω : Fin s → V // ∀ i : Fin s, ω i ∈ allowed i} ≃
        (∀ i : Fin s, allowed i) := {
    toFun := fun ω i => ⟨ω.1 i, ω.2 i⟩
    invFun := fun f => ⟨fun i => (f i).1, fun i => (f i).property⟩
    left_inv := by intro ω; apply Subtype.ext; funext i; rfl
    right_inv := by intro f; funext i; apply Subtype.ext; rfl
  }
  rw [Fintype.card_congr e]
  simp
/-- A product with one fixed coordinate and constant values before and after
that coordinate. -/
theorem prod_fin_before_at_after (s : ℕ) (j : Fin s) (a m : ℕ) :
    (∏ i : Fin s, if i < j then a else if i = j then 1 else m) =
      a ^ (j : ℕ) * m ^ (s - (j : ℕ) - 1) := by
  classical
  rw [Finset.prod_ite, Finset.prod_ite]
  simp only [Finset.prod_const, Finset.filter_filter]
  have hbefore : ({i : Fin s | i < j} : Finset (Fin s)).card = (j : ℕ) := by
    rw [Finset.filter_gt_eq_Iio, Fin.card_Iio]
  have hafter :
      ({i : Fin s | ¬i < j ∧ ¬i = j} : Finset (Fin s)).card =
        s - (j : ℕ) - 1 := by
    have heq :
        ({i : Fin s | ¬i < j ∧ ¬i = j} : Finset (Fin s)) =
          Finset.Ioi j := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_Ioi]
      omega
    rw [heq, Fin.card_Ioi]
    omega
  rw [hbefore, hafter]
  simp
/-- Exact count of samples whose vertex at position `j` is `v` and has
no neighbor among earlier positions. -/
theorem card_fixed_first_event
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {s : ℕ} (j : Fin s) (v : V) :
    Fintype.card
      {ω : Fin s → V // ω j = v ∧
        ∀ i : Fin s, i < j → ¬ G.Adj v (ω i)} =
      (Fintype.card V - G.degree v) ^ (j : ℕ) *
        (Fintype.card V) ^ (s - (j : ℕ) - 1) := by
  classical
  let A : Finset V := (G.neighborFinset v)ᶜ
  let allowed : Fin s → Finset V :=
    fun i => if i < j then A else if i = j then {v} else Finset.univ
  have hiff (ω : Fin s → V) :
      (ω j = v ∧ ∀ i : Fin s, i < j → ¬ G.Adj v (ω i)) ↔
        ∀ i : Fin s, ω i ∈ allowed i := by
    constructor
    · rintro ⟨hj, hbefore⟩ i
      by_cases hij : i < j
      · simp [allowed, hij, A, hbefore i hij]
      · by_cases hieq : i = j
        · subst i
          simpa [allowed] using hj
        · simp [allowed, hij, hieq]
    · intro h
      have hj : ω j = v := by
        have hh := h j
        simpa [allowed] using hh
      refine ⟨hj, ?_⟩
      intro i hij
      have hi := h i
      simpa [allowed, hij, A] using hi
  let e :
      {ω : Fin s → V // ω j = v ∧
        ∀ i : Fin s, i < j → ¬ G.Adj v (ω i)} ≃
      {ω : Fin s → V // ∀ i : Fin s, ω i ∈ allowed i} := {
    toFun := fun ω => ⟨ω.1, (hiff ω.1).mp ω.2⟩
    invFun := fun ω => ⟨ω.1, (hiff ω.1).mpr ω.2⟩
    left_inv := by intro ω; apply Subtype.ext; rfl
    right_inv := by intro ω; apply Subtype.ext; rfl
  }
  rw [Fintype.card_congr e, card_constrained_words]
  have hproduct :
      (∏ i : Fin s, (allowed i).card) =
        ∏ i : Fin s,
          if i < j then A.card else if i = j then 1 else Fintype.card V := by
    apply Finset.prod_congr rfl
    intro i _
    by_cases hij : i < j
    · simp [allowed, hij]
    · by_cases hieq : i = j
      · simp [allowed, hij, hieq]
      · simp [allowed, hij, hieq]
  rw [hproduct, prod_fin_before_at_after]
  simp only [A, Finset.card_compl, G.card_neighborFinset_eq_degree]
/-- Exact number of samples whose `j`th vertex has no neighbor in the
earlier part of the sample. -/
theorem card_first_without_neighbor
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {s : ℕ} (j : Fin s) :
    (Finset.univ.filter (fun ω : Fin s → V =>
      ∀ i : Fin s, i < j → ¬ G.Adj (ω j) (ω i))).card =
      ∑ v : V,
        (Fintype.card V - G.degree v) ^ (j : ℕ) *
          (Fintype.card V) ^ (s - (j : ℕ) - 1) := by
  classical
  have hsubtype :
      (Finset.univ.filter (fun ω : Fin s → V =>
        ∀ i : Fin s, i < j → ¬ G.Adj (ω j) (ω i))).card =
      Fintype.card {ω : Fin s → V //
        ∀ i : Fin s, i < j → ¬ G.Adj (ω j) (ω i)} := by
    symm
    apply Fintype.card_of_subtype
    intro ω
    simp
  rw [hsubtype]
  let e :
      {ω : Fin s → V //
        ∀ i : Fin s, i < j → ¬ G.Adj (ω j) (ω i)} ≃
      Σ v : V, {ω : Fin s → V // ω j = v ∧
        ∀ i : Fin s, i < j → ¬ G.Adj v (ω i)} := {
    toFun := fun ω => ⟨ω.1 j, ⟨ω.1, ⟨rfl, ω.2⟩⟩⟩
    invFun := fun p => ⟨p.2.1, by
      intro i hi
      rw [p.2.2.1]
      exact p.2.2.2 i hi⟩
    left_inv := by intro ω; apply Subtype.ext; rfl
    right_inv := by
      intro p
      rcases p with ⟨v, ⟨f, hf⟩⟩
      cases hf.1
      rfl  }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro v _
  exact card_fixed_first_event G j v
/-- Positions with no sampled neighbor before them. -/
def firstWithoutNeighborCount [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {s : ℕ} (ω : Fin s → V) : ℕ :=
  (Finset.univ.filter (fun j : Fin s =>
    ∀ i : Fin s, i < j → ¬ G.Adj (ω j) (ω i))).card

/-- Double count position/sample pairs with no earlier neighbor. -/
theorem sum_firstWithoutNeighborCount
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) :
    (∑ ω : Fin s → V, firstWithoutNeighborCount G ω) =
      ∑ j : Fin s, ∑ v : V,
        (Fintype.card V - G.degree v) ^ (j : ℕ) *
          (Fintype.card V) ^ (s - (j : ℕ) - 1) := by
  classical
  have hdc :
      (∑ ω : Fin s → V, firstWithoutNeighborCount G ω) =
        ∑ j : Fin s, (Finset.univ.filter
          (fun ω : Fin s → V =>
            ∀ i : Fin s, i < j → ¬ G.Adj (ω j) (ω i))).card := by
    simpa [firstWithoutNeighborCount, Finset.bipartiteAbove,
      Finset.bipartiteBelow] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (r := fun ω : Fin s → V => fun j : Fin s =>
          ∀ i : Fin s, i < j → ¬ G.Adj (ω j) (ω i))
        (s := Finset.univ) (t := Finset.univ))
  rw [hdc]
  apply Finset.sum_congr rfl
  intro j _
  exact card_first_without_neighbor G j

/-- Sampled components are bounded by positions with no earlier neighbor. -/
theorem sampled_component_count_le_firstWithoutNeighborCount
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {s : ℕ} (ω : Fin s → V) :
    Fintype.card (G.induce (sampleRange ω : Set V)).ConnectedComponent ≤
      firstWithoutNeighborCount G ω := by
  have h := sampled_component_count_le_first_without_neighbor G ω
  unfold firstWithoutNeighborCount
  convert h using 1
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact forall_congr' fun i => imp_congr_right fun _ =>
    not_congr (G.adj_comm _ _)
/-- The finite geometric sum underlying the expected component bound (E.6). -/
theorem first_event_geometric_bound (m δ s : ℕ) (hδ : δ ≤ m) :
    δ * (m *
      (∑ j : Fin s, (m - δ) ^ (j : ℕ) *
        m ^ (s - (j : ℕ) - 1))) ≤ m ^ (s + 1) := by
  let q := m - δ
  have hq : q ≤ m := Nat.sub_le m δ
  have hdiff : m - q = δ := by dsimp [q]; omega
  have hgeom :
      (∑ j : Fin s, q ^ (j : ℕ) * m ^ (s - (j : ℕ) - 1)) *
          δ = m ^ s - q ^ s := by
    have h := geom_sum₂_mul_of_ge hq s
    rw [geom_sum₂_comm] at h
    rw [hdiff] at h
    have hfin :
        (∑ j : Fin s, q ^ (j : ℕ) * m ^ (s - (j : ℕ) - 1)) =
          ∑ i ∈ Finset.range s, q ^ i * m ^ (s - 1 - i) := by
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => q ^ i * m ^ (s - i - 1))]
      apply Finset.sum_congr rfl
      intro i hi
      have his : i < s := Finset.mem_range.mp hi
      have hsub : s - i - 1 = s - 1 - i := by omega
      rw [hsub]
    rw [hfin]
    exact h
  dsimp [q] at hgeom ⊢
  have hpow : m ^ s - (m - δ) ^ s ≤ m ^ s := Nat.sub_le _ _
  calc
    δ * (m *
        (∑ j : Fin s, (m - δ) ^ (j : ℕ) *
          m ^ (s - (j : ℕ) - 1))) =
      m * ((∑ j : Fin s, (m - δ) ^ (j : ℕ) *
          m ^ (s - (j : ℕ) - 1)) * δ) := by ring
    _ = m * (m ^ s - (m - δ) ^ s) := by rw [hgeom]
    _ ≤ m * m ^ s := Nat.mul_le_mul_left _ hpow
    _ = m ^ (s + 1) := by rw [pow_succ]; ring

/-- The total number of first-component events in all ordered samples. -/
theorem sum_firstWithoutNeighborCount_le
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s δ : ℕ) (hV : Nonempty V)
    (hmin : ∀ v : V, δ ≤ G.degree v) :
    δ * (∑ ω : Fin s → V, firstWithoutNeighborCount G ω) ≤
      (Fintype.card V) ^ (s + 1) := by
  let m := Fintype.card V
  have hδ : δ ≤ m :=
    (hmin (Classical.choice hV)).trans
      (G.degree_lt_card_verts (Classical.choice hV)).le
  rw [sum_firstWithoutNeighborCount]
  have hterm (j : Fin s) (v : V) :
      (m - G.degree v) ^ (j : ℕ) * m ^ (s - (j : ℕ) - 1) ≤
      (m - δ) ^ (j : ℕ) * m ^ (s - (j : ℕ) - 1) := by
    gcongr
    exact hmin v
  have hsum :
      (∑ j : Fin s, ∑ v : V,
        (m - G.degree v) ^ (j : ℕ) * m ^ (s - (j : ℕ) - 1)) ≤
      m * (∑ j : Fin s,
        (m - δ) ^ (j : ℕ) * m ^ (s - (j : ℕ) - 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    simpa [m] using
      (Finset.sum_le_sum (s := Finset.univ) (fun v hv => hterm j v))
  exact (Nat.mul_le_mul_left δ hsum).trans
    (first_event_geometric_bound m δ s hδ)
/-- The total first-component count has mean strictly below `5/2`
when the minimum degree exceeds two fifths of the order. -/
theorem two_mul_sum_firstWithoutNeighborCount_lt
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s δ : ℕ) (hV : Nonempty V)
    (hmin : ∀ v : V, δ ≤ G.degree v)
    (hratio : 2 * Fintype.card V < 5 * δ) :
    2 * (∑ ω : Fin s → V, firstWithoutNeighborCount G ω) <
      5 * (Fintype.card V) ^ s := by
  let m := Fintype.card V
  let N := m ^ s
  let S := ∑ ω : Fin s → V, firstWithoutNeighborCount G ω
  have hN : 0 < N := pow_pos (Fintype.card_pos_iff.mpr hV) _
  have hmain : δ * S ≤ m * N := by
    simpa [N, S, pow_succ, mul_comm] using
      (sum_firstWithoutNeighborCount_le G s δ hV hmin)
  have hstrict : 2 * m * N < 5 * δ * N := by
    nlinarith [Nat.mul_lt_mul_of_pos_right hratio hN]
  change 2 * S < 5 * N
  by_contra h
  have hle : 5 * N ≤ 2 * S := by omega
  have hmul := Nat.mul_le_mul_left δ hle
  nlinarith

/-- The sampled induced graph has fewer than `5/2` components on average. -/
theorem two_mul_sum_sampled_components_lt
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s δ : ℕ) (hV : Nonempty V)
    (hmin : ∀ v : V, δ ≤ G.degree v)
    (hratio : 2 * Fintype.card V < 5 * δ) :
    2 * (∑ ω : Fin s → V,
      Fintype.card (G.induce (sampleRange ω : Set V)).ConnectedComponent) <
      5 * Fintype.card (Fin s → V) := by
  have hsum :
      (∑ ω : Fin s → V,
        Fintype.card (G.induce (sampleRange ω : Set V)).ConnectedComponent) ≤
      ∑ ω : Fin s → V, firstWithoutNeighborCount G ω := by
    apply Finset.sum_le_sum
    intro ω _
    exact sampled_component_count_le_firstWithoutNeighborCount G ω
  have hcard : Fintype.card (Fin s → V) = (Fintype.card V) ^ s := by
    simp
  rw [hcard]
  exact lt_of_le_of_lt (Nat.mul_le_mul_left 2 hsum)
    (two_mul_sum_firstWithoutNeighborCount_lt G s δ hV hmin hratio)
/-- A three-event union bound with the exact fractions used in Appendix E. -/
theorem exists_outside_three_bad_events
    {Ω : Type*} [Fintype Ω] (bad₁ bad₂ bad₃ : Ω → Prop)
    [DecidablePred bad₁] [DecidablePred bad₂] [DecidablePred bad₃]
    (h₁ : 4 * (Finset.univ.filter bad₁).card ≤ Fintype.card Ω)
    (h₂ : 8 * (Finset.univ.filter bad₂).card < 5 * Fintype.card Ω)
    (h₃ : 8 * (Finset.univ.filter bad₃).card < Fintype.card Ω) :
    ∃ ω : Ω, ¬ bad₁ ω ∧ ¬ bad₂ ω ∧ ¬ bad₃ ω := by
  classical
  let B₁ := Finset.univ.filter bad₁
  let B₂ := Finset.univ.filter bad₂
  let B₃ := Finset.univ.filter bad₃
  by_contra h
  push_neg at h
  have hcover : Finset.univ ⊆ B₁ ∪ (B₂ ∪ B₃) := by
    intro ω _
    have hw := h ω
    simp only [Finset.mem_union, B₁, B₂, B₃, Finset.mem_filter,
      Finset.mem_univ, true_and]
    tauto
  have hc := Finset.card_le_card hcover
  have h12 := Finset.card_union_le B₂ B₃
  have h123 := Finset.card_union_le B₁ (B₂ ∪ B₃)
  simp only [Finset.card_univ] at hc
  dsimp [B₁, B₂, B₃] at *
  omega
/-- Finite Markov counting in the form used for the three failure events. -/
theorem threshold_mul_bad_card_le_sum
    {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (t : ℝ)
    (bad : Ω → Prop) [DecidablePred bad]
    (hnonneg : ∀ ω, 0 ≤ f ω)
    (hbad : ∀ ω, bad ω → t ≤ f ω) :
    t * ((Finset.univ.filter bad).card : ℝ) ≤ ∑ ω, f ω := by
  let B := Finset.univ.filter bad
  calc
    t * (B.card : ℝ) = ∑ _ω ∈ B, t := by simp [mul_comm]
    _ ≤ ∑ ω ∈ B, f ω := by
      apply Finset.sum_le_sum
      intro ω hω
      exact hbad ω (Finset.mem_filter.mp hω).2
    _ ≤ ∑ ω ∈ Finset.univ, f ω := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro ω _ _
        exact hnonneg ω
/-- Fewer than five eighths of ordered samples have four or more
sampled components. -/
theorem eight_mul_bad_component_samples_lt
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s δ : ℕ) (hV : Nonempty V)
    (hmin : ∀ v : V, δ ≤ G.degree v)
    (hratio : 2 * Fintype.card V < 5 * δ) :
    8 * (Finset.univ.filter (fun ω : Fin s → V =>
      4 ≤ Fintype.card
        (G.induce (sampleRange ω : Set V)).ConnectedComponent)).card <
      5 * Fintype.card (Fin s → V) := by
  classical
  let f : (Fin s → V) → ℝ := fun ω =>
    Fintype.card (G.induce (sampleRange ω : Set V)).ConnectedComponent
  have hmarkov := threshold_mul_bad_card_le_sum f 4
    (fun ω => 4 ≤ Fintype.card
      (G.induce (sampleRange ω : Set V)).ConnectedComponent)
    (fun ω => by positivity)
    (fun ω hω => by change (4 : ℝ) ≤ (Fintype.card _ : ℝ); exact_mod_cast hω)
  have hmarkovNat :
      4 * (Finset.univ.filter (fun ω : Fin s → V =>
        4 ≤ Fintype.card
          (G.induce (sampleRange ω : Set V)).ConnectedComponent)).card ≤
      ∑ ω : Fin s → V,
        Fintype.card (G.induce (sampleRange ω : Set V)).ConnectedComponent := by
    have hcast :
        (↑(4 * (Finset.univ.filter (fun ω : Fin s → V =>
          4 ≤ Fintype.card
            (G.induce (sampleRange ω : Set V)).ConnectedComponent)).card) : ℝ) ≤
        (↑(∑ ω : Fin s → V,
          Fintype.card (G.induce (sampleRange ω : Set V)).ConnectedComponent) : ℝ) := by
      simpa [f] using hmarkov
    exact_mod_cast hcast
  have hmean := two_mul_sum_sampled_components_lt G s δ hV hmin hratio
  omega
/-- Union bound for samples contained in one of a finite family of sets. -/
theorem card_sample_words_in_some_le_sum_pow
    [DecidableEq V] {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (A : ι → Finset V) (s : ℕ) :
    (Finset.univ.filter (fun ω : Fin s → V =>
      ∃ j ∈ J, sampleRange ω ⊆ A j)).card ≤
      ∑ j ∈ J, (A j).card ^ s := by
  classical
  let E : ι → Finset (Fin s → V) := fun j =>
    Finset.univ.filter (fun ω => sampleRange ω ⊆ A j)
  have heq :
      Finset.univ.filter (fun ω : Fin s → V =>
        ∃ j ∈ J, sampleRange ω ⊆ A j) = J.biUnion E := by
    ext ω
    simp [E, Finset.mem_biUnion]
  rw [heq]
  calc
    (J.biUnion E).card ≤ ∑ j ∈ J, (E j).card := Finset.card_biUnion_le
    _ = ∑ j ∈ J, (A j).card ^ s := by
      apply Finset.sum_congr rfl
      intro j _
      exact card_filter_sample_words_in (A j) s
/-- The old-branch avoidance event is rare once each forbidden set is
small compared with the current vertex set. -/
theorem eight_mul_bad_old_samples_lt
    [DecidableEq V] {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (A : ι → Finset V) (s : ℕ) (α : ℝ)
    (hm : 0 < Fintype.card V) (hα : 0 ≤ α)
    (hA : ∀ j ∈ J, ((A j).card : ℝ) ≤ (Fintype.card V : ℝ) * α)
    (hnum : 8 * (J.card : ℝ) * α ^ s < 1) :
    8 * (Finset.univ.filter (fun ω : Fin s → V =>
      ∃ j ∈ J, sampleRange ω ⊆ A j)).card <
      Fintype.card (Fin s → V) := by
  let m := Fintype.card V
  have hmreal : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hbad := card_sample_words_in_some_le_sum_pow J A s
  have hbadReal :
      ((Finset.univ.filter (fun ω : Fin s → V =>
        ∃ j ∈ J, sampleRange ω ⊆ A j)).card : ℝ) ≤
        ∑ j ∈ J, ((A j).card : ℝ) ^ s := by
    exact_mod_cast hbad
  have hsum :
      (∑ j ∈ J, ((A j).card : ℝ) ^ s) ≤
        (J.card : ℝ) * ((m : ℝ) * α) ^ s := by
    calc
      (∑ j ∈ J, ((A j).card : ℝ) ^ s) ≤
          ∑ _j ∈ J, ((m : ℝ) * α) ^ s := by
        apply Finset.sum_le_sum
        intro j hj
        exact pow_le_pow_left₀ (by positivity) (hA j hj) _
      _ = (J.card : ℝ) * ((m : ℝ) * α) ^ s := by simp
  have hnum' :
      (8 * (J.card : ℝ) * α ^ s) * (m : ℝ) ^ s < (m : ℝ) ^ s := by
    simpa using mul_lt_mul_of_pos_right hnum (pow_pos hmreal s)
  have hcard : (Fintype.card (Fin s → V) : ℝ) = (m : ℝ) ^ s := by
    simp [m]
  have hreal :
      8 * ((Finset.univ.filter (fun ω : Fin s → V =>
        ∃ j ∈ J, sampleRange ω ⊆ A j)).card : ℝ) <
        (Fintype.card (Fin s → V) : ℝ) := by
    rw [hcard]
    calc
      8 * ((Finset.univ.filter (fun ω : Fin s → V =>
        ∃ j ∈ J, sampleRange ω ⊆ A j)).card : ℝ) ≤
          8 * ((J.card : ℝ) * ((m : ℝ) * α) ^ s) := by
        gcongr
        exact hbadReal.trans hsum
      _ = (8 * (J.card : ℝ) * α ^ s) * (m : ℝ) ^ s := by
        rw [mul_pow]
        ring
      _ < (m : ℝ) ^ s := hnum'
  exact_mod_cast hreal
/-- Markov's inequality with a quarter of the sample space as threshold. -/
theorem four_mul_large_value_samples_le
    {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (θ : ℝ)
    (hθ : 0 < θ) (hnonneg : ∀ ω, 0 ≤ f ω)
    (hsum : 4 * (∑ ω, f ω) ≤ (Fintype.card Ω : ℝ) * θ) :
    4 * (Finset.univ.filter (fun ω => θ < f ω)).card ≤ Fintype.card Ω := by
  classical
  have hmarkov := threshold_mul_bad_card_le_sum f θ
    (fun ω => θ < f ω) hnonneg (fun _ h => h.le)
  by_contra h
  have hnat : Fintype.card Ω <
      4 * (Finset.univ.filter (fun ω => θ < f ω)).card := by omega
  have hreal : (Fintype.card Ω : ℝ) <
      4 * ((Finset.univ.filter (fun ω => θ < f ω)).card : ℝ) := by
    exact_mod_cast hnat
  have hmul := mul_lt_mul_of_pos_right hreal hθ
  nlinarith
/-- A usable ordered sample from the three finite counting bounds. -/
theorem exists_good_sample_of_count_bounds
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [DecidableEq ι] (J : Finset ι) (A : ι → Finset V)
    (s δ : ℕ) (θ : ℝ) (hV : Nonempty V)
    (hmin : ∀ v : V, δ ≤ G.degree v)
    (hratio : 2 * Fintype.card V < 5 * δ)
    (hθ : 0 < θ)
    (hdom : 4 * (∑ ω : Fin s → V, (undominatedCount G ω : ℝ)) ≤
      (Fintype.card (Fin s → V) : ℝ) * θ)
    (hold : 8 * (Finset.univ.filter (fun ω : Fin s → V =>
      ∃ j ∈ J, sampleRange ω ⊆ A j)).card <
      Fintype.card (Fin s → V)) :
    ∃ ω : Fin s → V,
      (undominatedCount G ω : ℝ) ≤ θ ∧
      Fintype.card (G.induce (sampleRange ω : Set V)).ConnectedComponent ≤ 3 ∧
      ∀ j ∈ J, ¬ sampleRange ω ⊆ A j := by
  classical
  have h₁ := four_mul_large_value_samples_le
    (fun ω : Fin s → V => (undominatedCount G ω : ℝ)) θ
    hθ (fun _ => by positivity) hdom
  have h₂ := eight_mul_bad_component_samples_lt G s δ hV hmin hratio
  obtain ⟨ω, hgood₁, hgood₂, hgood₃⟩ :=
    exists_outside_three_bad_events
      (fun ω : Fin s → V => θ < (undominatedCount G ω : ℝ))
      (fun ω : Fin s → V =>
        4 ≤ Fintype.card (G.induce (sampleRange ω : Set V)).ConnectedComponent)
      (fun ω : Fin s → V => ∃ j ∈ J, sampleRange ω ⊆ A j)
      h₁ h₂ hold
  refine ⟨ω, le_of_not_gt hgood₁, ?_, ?_⟩
  · omega
  · intro j hj hsub
    exact hgood₃ ⟨j, hj, hsub⟩
/-- Appendix E.7 as a finite count of bad ordered samples. -/
theorem eight_mul_bad_old_samples_lt_kt
    [DecidableEq V] {ι : Type*} [DecidableEq ι]
    (r : ℕ) (hr : 13 ≤ r) (J : Finset ι) (A : ι → Finset V)
    (hJ : J.card ≤ r)
    (hm : 0 < Fintype.card V)
    (hA : ∀ j ∈ J,
      ((A j).card : ℝ) ≤ (Fintype.card V : ℝ) *
        (4 * Real.exp (-(2 : ℝ) *
          (Nat.ceil (4 * Real.sqrt (Real.log (r : ℝ))) : ℝ) / 5))) :
    8 * (Finset.univ.filter (fun ω :
        Fin (Nat.ceil (4 * Real.sqrt (Real.log (r : ℝ)))) → V =>
      ∃ j ∈ J, sampleRange ω ⊆ A j)).card <
      Fintype.card
        (Fin (Nat.ceil (4 * Real.sqrt (Real.log (r : ℝ)))) → V) := by
  let s := Nat.ceil (4 * Real.sqrt (Real.log (r : ℝ)))
  let α := 4 * Real.exp (-(2 : ℝ) * (s : ℝ) / 5)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hnum0 := clique_branch_old_set_failure_bound r hr
  have hnum0' : 8 * (r : ℝ) * α ^ s < 1 := by
    dsimp [α, s] at hnum0 ⊢
    linarith
  have hnum : 8 * (J.card : ℝ) * α ^ s < 1 := by
    have hJreal : (J.card : ℝ) ≤ r := by exact_mod_cast hJ
    have hpow : 0 ≤ α ^ s := pow_nonneg hα _
    nlinarith [mul_le_mul_of_nonneg_right hJreal hpow]
  exact eight_mul_bad_old_samples_lt J A s α hm hα hA hnum
/-- The original vertices belonging to a component of an induced graph. -/
def inducedComponentSet [DecidableEq V] (G : SimpleGraph V)
    (B : Finset V)
    (c : (G.induce (B : Set V)).ConnectedComponent) : Set V :=
  (Subtype.val : B → V) '' c.supp

/-- A component of an induced graph remains connected on its original
vertex set. -/
theorem connected_induce_inducedComponentSet
    [DecidableEq V] (G : SimpleGraph V) (B : Finset V)
    (c : (G.induce (B : Set V)).ConnectedComponent) :
    (G.induce (inducedComponentSet G B c)).Connected := by
  let J := G.induce (B : Set V)
  let φ : c.toSimpleGraph →g G.induce (inducedComponentSet G B c) := {
    toFun := fun z => ⟨z.1.1, ⟨z.1, z.2, rfl⟩⟩
    map_rel' := by intro x y hxy; exact hxy }
  have hsurj : Function.Surjective φ := by
    rintro ⟨v, ⟨u, hu, huv⟩⟩
    subst huv
    exact ⟨⟨u, hu⟩, rfl⟩
  exact c.connected_toSimpleGraph.map φ hsurj

/-- Every sampled vertex lies in its induced connected component. -/
theorem mem_inducedComponentSet_mk
    [DecidableEq V] (G : SimpleGraph V) (B : Finset V)
    (v : B) :
    v.1 ∈ inducedComponentSet G B
      ((G.induce (B : Set V)).connectedComponentMk v) := by
  exact ⟨v, by simp, rfl⟩
/-- Join the components of a finite vertex set by paths from one fixed
component. The quantitative version below bounds the added vertices. -/
theorem exists_connected_superset_by_component_paths
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hdist : ∀ u v : V, G.dist u v ≤ 5)
    (B : Finset V) (hB : B.Nonempty)
    (hcomp : Fintype.card (G.induce (B : Set V)).ConnectedComponent ≤ 3) :
    ∃ Q : Finset V, B ⊆ Q ∧ (G.induce (Q : Set V)).Connected ∧
      Q.card ≤ B.card + 8 := by
  classical
  let J := G.induce (B : Set V)
  obtain ⟨v₀, hv₀⟩ := hB
  let c₀ : J.ConnectedComponent := J.connectedComponentMk ⟨v₀, hv₀⟩
  let a : V := c₀.out.1
  let p (c : J.ConnectedComponent) : G.Walk a c.out.1 :=
    Classical.choose (hconn.exists_path_of_dist a c.out.1)
  let P (c : J.ConnectedComponent) : Finset V := (p c).support.toFinset
  let C (c : J.ConnectedComponent) : Set V := inducedComponentSet G B c
  let D (c : J.ConnectedComponent) : Set V := C c ∪ (P c : Set V)
  let Q : Finset V := B ∪ Finset.univ.biUnion P
  have hQ : B ⊆ Q := Finset.subset_union_left
  have hDconn (c : J.ConnectedComponent) : (G.induce (D c)).Connected := by
    have hC : (G.induce (C c)).Connected :=
      connected_induce_inducedComponentSet G B c
    have hP : (G.induce (P c : Set V)).Connected := by
      have hset : (P c : Set V) = {v | v ∈ (p c).support} := by
        ext v
        simp [P]
      rw [hset]
      exact (p c).connected_induce_support
    have hinter : (C c ∩ (P c : Set V)).Nonempty := by
      refine ⟨c.out.1, ?_, ?_⟩
      · exact ⟨c.out, c.out_eq, rfl⟩
      · simp [P, (p c).end_mem_support]
    exact G.induce_union_connected hC.preconnected hP.preconnected hinter
  have haD (c : J.ConnectedComponent) : a ∈ D c := by
    right
    simp [P, (p c).start_mem_support]
  have hSconn :
      (G.induce (⋃₀ (Set.range D))).Connected := by
    apply G.induce_sUnion_connected_of_pairwise_not_disjoint
    · exact ⟨D c₀, ⟨c₀, rfl⟩⟩
    · rintro S T ⟨c, rfl⟩ ⟨d, rfl⟩
      exact ⟨a, haD c, haD d⟩
    · rintro S ⟨c, rfl⟩
      exact hDconn c
  have hQeq : (Q : Set V) = ⋃₀ (Set.range D) := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hxB | hxP
      · let z : B := ⟨x, hxB⟩
        let c : J.ConnectedComponent := J.connectedComponentMk z
        have hxC : x ∈ C c := by
          refine ⟨z, ?_, rfl⟩
          change z ∈ (J.connectedComponentMk z).supp
          simp
        exact ⟨D c, ⟨c, rfl⟩, Or.inl hxC⟩
      · obtain ⟨c, _, hxc⟩ := Finset.mem_biUnion.mp hxP
        exact ⟨D c, ⟨c, rfl⟩, Or.inr hxc⟩
    · rintro ⟨S, ⟨c, rfl⟩, hx⟩
      rcases hx with hxC | hxP
      · obtain ⟨z, _, rfl⟩ := hxC
        exact Finset.mem_union_left _ z.property
      · exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, hxP⟩)
  have hp (c : J.ConnectedComponent) :
      (p c).IsPath ∧ (p c).length = G.dist a c.out.1 :=
    Classical.choose_spec (hconn.exists_path_of_dist a c.out.1)
  have hPcard (c : J.ConnectedComponent) :
      (P c).card = (p c).length + 1 := by
    dsimp [P]
    rw [List.toFinset_card_of_nodup (hp c).1.support_nodup,
      SimpleGraph.Walk.length_support]
  have haB : a ∈ B := c₀.out.property
  have hPstart (c : J.ConnectedComponent) : a ∈ P c := by
    simp [P, (p c).start_mem_support]
  have hPend (c : J.ConnectedComponent) : c.out.1 ∈ P c := by
    simp [P, (p c).end_mem_support]
  have hdiff₀ : (P c₀ \ B).card = 0 := by
    have hlen : (p c₀).length = 0 := by
      rw [(hp c₀).2]
      simp [a]
    have hinter : 1 ≤ (P c₀ ∩ B).card := by
      have : ({a} : Finset V) ⊆ P c₀ ∩ B := by
        simp [hPstart c₀, haB]
      simpa using Finset.card_le_card this
    have heq := Finset.card_sdiff_add_card_inter (P c₀) B
    rw [hPcard c₀, hlen] at heq
    omega
  have hdiff (c : J.ConnectedComponent) (hc : c ≠ c₀) :
      (P c \ B).card ≤ 4 := by
    have hne : a ≠ c.out.1 := by
      intro heq
      have hout : c₀.out = c.out := Subtype.ext heq
      have hceq : c = c₀ := by
        have h₀ : J.connectedComponentMk c₀.out = c₀ := c₀.out_eq
        have h₁ : J.connectedComponentMk c.out = c := c.out_eq
        rw [hout] at h₀
        exact h₁.symm.trans h₀
      exact hc hceq
    have hinter : 2 ≤ (P c ∩ B).card := by
      have hpair : ({a, c.out.1} : Finset V) ⊆ P c ∩ B := by
        intro x hx
        have hx' : x = a ∨ x = c.out.1 := by simpa using hx
        rcases hx' with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hPstart c, haB⟩
        · exact Finset.mem_inter.mpr ⟨hPend c, c.out.property⟩
      have hpairCard : ({a, c.out.1} : Finset V).card = 2 := by
        simp [hne]
      simpa [hpairCard] using Finset.card_le_card hpair
    have hlen : (p c).length ≤ 5 := by
      rw [(hp c).2]
      exact hdist a c.out.1
    have heq := Finset.card_sdiff_add_card_inter (P c) B
    rw [hPcard c] at heq
    omega
  have hsum : (∑ c : J.ConnectedComponent, (P c \ B).card) ≤ 8 := by
    have hsum' :
        (∑ c ∈ (Finset.univ.erase c₀), (P c \ B).card) ≤
          4 * (Finset.univ.erase c₀).card := by
      calc
        (∑ c ∈ (Finset.univ.erase c₀), (P c \ B).card) ≤
            ∑ _c ∈ (Finset.univ.erase c₀), 4 := by
          apply Finset.sum_le_sum
          intro c hc
          exact hdiff c (Finset.ne_of_mem_erase hc)
        _ = 4 * (Finset.univ.erase c₀).card := by simp [mul_comm]
    have hcardErase : (Finset.univ.erase c₀).card ≤ 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ c₀)]
      simpa [J] using hcomp
    rw [← Finset.sum_erase_add Finset.univ (fun c => (P c \ B).card)
      (Finset.mem_univ c₀), hdiff₀]
    omega
  have hQcard : Q.card ≤ B.card + 8 := by
    let T : Finset V := Finset.univ.biUnion P
    have hsub : T \ B ⊆ Finset.univ.biUnion (fun c => P c \ B) := by
      intro x hx
      obtain ⟨hxT, hxnotB⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨c, hc, hxc⟩ := Finset.mem_biUnion.mp hxT
      exact Finset.mem_biUnion.mpr
        ⟨c, hc, Finset.mem_sdiff.mpr ⟨hxc, hxnotB⟩⟩
    have hbound : (T \ B).card ≤ ∑ c : J.ConnectedComponent, (P c \ B).card :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have heq : Q.card = (T \ B).card + B.card := by
      simpa [Q, T, Finset.union_comm] using
        (Finset.card_sdiff_add_card T B).symm
    omega
  exact ⟨Q, hQ, hQeq ▸ hSconn, hQcard⟩
end HadwigerLean
