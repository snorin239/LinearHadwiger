import HadwigerLean.Graph.DensityBasic
import Mathlib.Data.Finset.Powerset
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite averaging for graph sampling

The sampling argument in Appendix F is a uniform average over vertex subsets
of a fixed size. This module first isolates the finite averaging principle;
the exact subset count will use `Finset.card_filter_powersetCard_subset`.
-/

namespace HadwigerLean.FiniteSampling

variable {ι : Type*} [DecidableEq ι]

/-- Some member of a nonempty finite family is at least its average. The
division-free form is useful when the family cardinality is symbolic. -/
theorem exists_sum_le_card_mul (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) :
    ∃ i ∈ s, (∑ j ∈ s, f j) ≤ (s.card : ℝ) * f i := by
  have hsum :
      (∑ i ∈ s, (∑ j ∈ s, f j)) ≤
        ∑ i ∈ s, (s.card : ℝ) * f i := by
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    exact le_rfl
  exact Finset.exists_le_of_sum_le hs hsum

/-- Some member of a nonempty finite family is at most its average. -/
theorem exists_card_mul_le_sum (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) :
    ∃ i ∈ s, (s.card : ℝ) * f i ≤ ∑ j ∈ s, f j := by
  have hsum :
      (∑ i ∈ s, (s.card : ℝ) * f i) ≤
        ∑ i ∈ s, (∑ j ∈ s, f j) := by
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    exact le_rfl
  exact Finset.exists_le_of_sum_le hs hsum

end HadwigerLean.FiniteSampling
namespace HadwigerLean.FiniteSampling

variable {ι : Type*} [DecidableEq ι]

/-- The exact number of m-sets containing two prescribed distinct members. -/
theorem card_fixed_pair_subsets (u : Finset ι) {a b : ι}
    (ha : a ∈ u) (hb : b ∈ u) (hab : a ≠ b)
    (m : ℕ) (hm : 2 ≤ m) :
    ((u.powersetCard m).filter (fun s => ({a, b} : Finset ι) ⊆ s)).card =
      Nat.choose (u.card - 2) (m - 2) := by
  have hpair : ({a, b} : Finset ι).card = 2 := by simp [hab]
  have hsubset : ({a, b} : Finset ι) ⊆ u := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  simpa [hpair] using
    Finset.card_filter_powersetCard_subset ({a, b} : Finset ι) u m
      hsubset (hpair.symm ▸ hm)

end HadwigerLean.FiniteSampling
namespace HadwigerLean.FiniteSampling

variable {ι : Type*} [DecidableEq ι]

/-- Double counting: each two-element member belongs to the same number
of fixed-size subsets of the ambient set. -/
theorem sum_card_contained_pairs (u : Finset ι)
    (pairs : Finset (Finset ι)) (m : ℕ)
    (hpair : ∀ e ∈ pairs, e ⊆ u ∧ e.card = 2)
    (hm : 2 ≤ m) :
    (∑ s ∈ u.powersetCard m, (pairs.filter fun e => e ⊆ s).card) =
      pairs.card * Nat.choose (u.card - 2) (m - 2) := by
  classical
  have hdc :
      (∑ s ∈ u.powersetCard m, (pairs.filter fun e => e ⊆ s).card) =
        ∑ e ∈ pairs, ((u.powersetCard m).filter fun s => e ⊆ s).card := by
    simpa [Finset.bipartiteAbove, Finset.bipartiteBelow] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (r := fun s e : Finset ι => e ⊆ s)
        (s := u.powersetCard m) (t := pairs))
  rw [hdc]
  calc
    (∑ e ∈ pairs, ((u.powersetCard m).filter fun s => e ⊆ s).card) =
        ∑ _e ∈ pairs, Nat.choose (u.card - 2) (m - 2) := by
      apply Finset.sum_congr rfl
      intro e he
      obtain ⟨heu, hecard⟩ := hpair e he
      simpa [hecard] using
        (Finset.card_filter_powersetCard_subset e u m heu (hecard.symm ▸ hm))
    _ = pairs.card * Nat.choose (u.card - 2) (m - 2) := by simp

end HadwigerLean.FiniteSampling
namespace HadwigerLean.FiniteSampling

variable {ι : Type*} [DecidableEq ι]

/-- A finite sample retains at least the average number of two-element
objects. This is the counting core of Appendix F's sampling inequality. -/
theorem exists_fixed_size_sample (u : Finset ι)
    (pairs : Finset (Finset ι)) (m : ℕ)
    (hpair : ∀ e ∈ pairs, e ⊆ u ∧ e.card = 2)
    (hm2 : 2 ≤ m) (hmu : m ≤ u.card) :
    ∃ s : Finset ι, s ⊆ u ∧ s.card = m ∧
      (pairs.card : ℝ) * (Nat.choose (u.card - 2) (m - 2) : ℝ) ≤
        (Nat.choose u.card m : ℝ) *
          ((pairs.filter fun e => e ⊆ s).card : ℝ) := by
  classical
  let family := u.powersetCard m
  have hnonempty : family.Nonempty := by
    simpa [family] using (Finset.powersetCard_nonempty.mpr hmu)
  obtain ⟨s, hs, havg⟩ :=
    exists_sum_le_card_mul family hnonempty
      (fun s => ((pairs.filter fun e => e ⊆ s).card : ℝ))
  have hsum :
      (∑ s ∈ family, ((pairs.filter fun e => e ⊆ s).card : ℝ)) =
        (pairs.card : ℝ) * (Nat.choose (u.card - 2) (m - 2) : ℝ) := by
    exact_mod_cast sum_card_contained_pairs u pairs m hpair hm2
  have hsmem : s ⊆ u ∧ s.card = m := by
    exact Finset.mem_powersetCard.mp hs
  refine ⟨s, hsmem.1, hsmem.2, ?_⟩
  simpa [family, Finset.card_powersetCard, hsum] using havg

end HadwigerLean.FiniteSampling
namespace HadwigerLean.FiniteSampling

/-- The two-point inclusion probability in a uniform fixed-size sample is
at least p squared whenever its falling factorial has the corresponding
lower bound. -/
theorem choose_ratio_bound (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (p : ℝ)
    (hfall : p ^ 2 * (n : ℝ) * ((n : ℝ) - 1) ≤
      (m : ℝ) * ((m : ℝ) - 1)) :
    p ^ 2 * (Nat.choose n m : ℝ) ≤
      (Nat.choose (n - 2) (m - 2) : ℝ) := by
  have hchoose : Nat.choose n m * Nat.choose m 2 =
      Nat.choose n 2 * Nat.choose (n - 2) (m - 2) :=
    Nat.choose_mul hm
  have hchooseR :
      (Nat.choose n m : ℝ) * ((m : ℝ) * ((m : ℝ) - 1)) =
        ((n : ℝ) * ((n : ℝ) - 1)) *
          (Nat.choose (n - 2) (m - 2) : ℝ) := by
    have h := congrArg (fun x : ℕ => (x : ℝ)) hchoose
    simp only [Nat.cast_mul, Nat.cast_choose_two] at h
    nlinarith
  have hmult := mul_le_mul_of_nonneg_left hfall
    (Nat.cast_nonneg (Nat.choose n m) : (0 : ℝ) ≤ _)
  have hnpos : 0 < (n : ℝ) * ((n : ℝ) - 1) := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith

  nlinarith [hmult, hchooseR]

end HadwigerLean.FiniteSampling
namespace HadwigerLean.FiniteSampling

variable {ι : Type*} [DecidableEq ι]

/-- A fixed-size sample retaining a p-squared fraction of every family of
two-element subsets, under the explicit numerical conditions on its size. -/
theorem exists_sample_of_falling_bound (u : Finset ι)
    (pairs : Finset (Finset ι)) (m : ℕ) (p : ℝ)
    (hpair : ∀ e ∈ pairs, e ⊆ u ∧ e.card = 2)
    (hn : 2 ≤ u.card) (hm : 2 ≤ m) (hmu : m ≤ u.card)
    (hmcard : (m : ℝ) ≤ p * (u.card : ℝ) + 2)
    (hfall : p ^ 2 * (u.card : ℝ) * ((u.card : ℝ) - 1) ≤
      (m : ℝ) * ((m : ℝ) - 1)) :
    ∃ s : Finset ι, s ⊆ u ∧
      (s.card : ℝ) ≤ p * (u.card : ℝ) + 2 ∧
      p ^ 2 * (pairs.card : ℝ) ≤
        ((pairs.filter fun e => e ⊆ s).card : ℝ) := by
  classical
  obtain ⟨s, hsu, hscard, havg⟩ :=
    exists_fixed_size_sample u pairs m hpair hm hmu
  have hratio := choose_ratio_bound u.card m hn hm p hfall
  have hcpos : (0 : ℝ) < (Nat.choose u.card m : ℝ) := by
    exact_mod_cast Nat.choose_pos hmu
  have hscaled := mul_le_mul_of_nonneg_left hratio
    (Nat.cast_nonneg pairs.card : (0 : ℝ) ≤ _)
  refine ⟨s, hsu, ?_, ?_⟩
  · simpa [hscard] using hmcard
  · nlinarith [havg, hscaled]

end HadwigerLean.FiniteSampling
namespace HadwigerLean.FiniteSampling

/-- Numerical choice of sample size from Appendix F. -/
theorem sample_size_bounds (n : ℕ) (hn : 2 ≤ n)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    let m := min n (Nat.ceil (p * (n : ℝ)) + 1)
    2 ≤ m ∧ m ≤ n ∧
      (m : ℝ) ≤ p * (n : ℝ) + 2 ∧
      p ^ 2 * (n : ℝ) * ((n : ℝ) - 1) ≤
        (m : ℝ) * ((m : ℝ) - 1) := by
  let x : ℝ := p * (n : ℝ)
  let c : ℕ := Nat.ceil x
  let m : ℕ := min n (c + 1)
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn)
  have hxpos : 0 < x := mul_pos hp hnpos
  have hcle : x ≤ (c : ℝ) := Nat.le_ceil x
  have hcpos : 1 ≤ c := by
    have hcposR : (0 : ℝ) < c := lt_of_lt_of_le hxpos hcle
    exact_mod_cast hcposR
  have hcupper : (c : ℝ) ≤ x + 1 :=
    (Nat.ceil_lt_add_one hxpos.le).le
  have hm2 : 2 ≤ m := by
    dsimp [m]
    omega
  have hmn : m ≤ n := Nat.min_le_left _ _
  have hmcard : (m : ℝ) ≤ x + 2 := by
    have hmc : m ≤ c + 1 := Nat.min_le_right _ _
    have hmcR : (m : ℝ) ≤ (c : ℝ) + 1 := by exact_mod_cast hmc
    linarith
  have hfall :
      p ^ 2 * (n : ℝ) * ((n : ℝ) - 1) ≤
        (m : ℝ) * ((m : ℝ) - 1) := by
    by_cases hnc : n ≤ c + 1
    · have hmeq : m = n := by simp [m, min_eq_left hnc]
      rw [hmeq]
      have hp0 : 0 ≤ p := hp.le
      have hpsq : p ^ 2 ≤ 1 := by
        have hprod := mul_nonneg hp0 (sub_nonneg.mpr hp1)
        nlinarith
      have hnprod : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) := by
        have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hpsq hnprod]
    · have hmeq : m = c + 1 := by
        simp [m, min_eq_right (Nat.le_of_not_ge hnc)]
      have hmbound : x + 1 ≤ (m : ℝ) := by
        rw [hmeq]
        push_cast
        linarith
      have hx0 : 0 ≤ x := hxpos.le
      have hlowfall :
          p ^ 2 * (n : ℝ) * ((n : ℝ) - 1) ≤ x * (x + 1) := by
        dsimp [x]
        nlinarith [mul_nonneg hp.le hnpos.le]
      have hshift : x ≤ (m : ℝ) - 1 := by linarith
      have hmnonneg : 0 ≤ (m : ℝ) - 1 := by linarith
      have hprod : x * (x + 1) ≤ (m : ℝ) * ((m : ℝ) - 1) := by
        calc
          x * (x + 1) ≤ ((m : ℝ) - 1) * (x + 1) :=
            mul_le_mul_of_nonneg_right hshift (by linarith)
          _ ≤ ((m : ℝ) - 1) * (m : ℝ) :=
            mul_le_mul_of_nonneg_left hmbound hmnonneg
          _ = (m : ℝ) * ((m : ℝ) - 1) := by ac_rfl
      exact hlowfall.trans hprod
  change 2 ≤ m ∧ m ≤ n ∧
    (m : ℝ) ≤ x + 2 ∧
    p ^ 2 * (n : ℝ) * ((n : ℝ) - 1) ≤
      (m : ℝ) * ((m : ℝ) - 1)
  exact ⟨hm2, hmn, hmcard, hfall⟩

end HadwigerLean.FiniteSampling
namespace HadwigerLean.FiniteSampling

variable {ι : Type*} [DecidableEq ι]

/-- Uniform finite sampling: some vertex sample of size at most p n + 2
retains at least a p-squared fraction of a family of two-element sets. -/
theorem exists_sample (u : Finset ι)
    (pairs : Finset (Finset ι))
    (hpair : ∀ e ∈ pairs, e ⊆ u ∧ e.card = 2)
    (hn : 2 ≤ u.card) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ∃ s : Finset ι, s ⊆ u ∧
      (s.card : ℝ) ≤ p * (u.card : ℝ) + 2 ∧
      p ^ 2 * (pairs.card : ℝ) ≤
        ((pairs.filter fun e => e ⊆ s).card : ℝ) := by
  let m : ℕ := min u.card (Nat.ceil (p * (u.card : ℝ)) + 1)
  have hnums :
      2 ≤ m ∧ m ≤ u.card ∧
      (m : ℝ) ≤ p * (u.card : ℝ) + 2 ∧
      p ^ 2 * (u.card : ℝ) * ((u.card : ℝ) - 1) ≤
        (m : ℝ) * ((m : ℝ) - 1) := by
    simpa only [m] using sample_size_bounds u.card hn p hp hp1
  exact exists_sample_of_falling_bound u pairs m p hpair hn
    hnums.1 hnums.2.1 hnums.2.2.1 hnums.2.2.2

end HadwigerLean.FiniteSampling
namespace HadwigerLean.FiniteSampling

variable {ι β : Type*} [DecidableEq ι] [DecidableEq β]

/-- Double counting fixed-size samples for indexed two-element objects.
Different objects may have the same endpoint set. -/
theorem sum_card_contained_objects (u : Finset ι)
    (objects : Finset β) (ends : β → Finset ι) (m : ℕ)
    (hends : ∀ e ∈ objects, ends e ⊆ u ∧ (ends e).card = 2)
    (hm : 2 ≤ m) :
    (∑ s ∈ u.powersetCard m,
      (objects.filter fun e => ends e ⊆ s).card) =
      objects.card * Nat.choose (u.card - 2) (m - 2) := by
  classical
  have hdc :
      (∑ s ∈ u.powersetCard m,
        (objects.filter fun e => ends e ⊆ s).card) =
        ∑ e ∈ objects,
          ((u.powersetCard m).filter fun s => ends e ⊆ s).card := by
    simpa [Finset.bipartiteAbove, Finset.bipartiteBelow] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (r := fun s e => ends e ⊆ s)
        (s := u.powersetCard m) (t := objects))
  rw [hdc]
  calc
    (∑ e ∈ objects,
      ((u.powersetCard m).filter fun s => ends e ⊆ s).card) =
        ∑ _e ∈ objects, Nat.choose (u.card - 2) (m - 2) := by
      apply Finset.sum_congr rfl
      intro e he
      obtain ⟨heu, hecard⟩ := hends e he
      simpa [hecard] using
        (Finset.card_filter_powersetCard_subset (ends e) u m heu
          (hecard.symm ▸ hm))
    _ = objects.card * Nat.choose (u.card - 2) (m - 2) := by simp

/-- Uniform sampling for indexed two-element objects, without requiring
distinct objects to have distinct endpoint sets. -/
theorem exists_sample_objects (u : Finset ι)
    (objects : Finset β) (ends : β → Finset ι)
    (hends : ∀ e ∈ objects, ends e ⊆ u ∧ (ends e).card = 2)
    (hn : 2 ≤ u.card) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ∃ s : Finset ι, s ⊆ u ∧
      (s.card : ℝ) ≤ p * (u.card : ℝ) + 2 ∧
      p ^ 2 * (objects.card : ℝ) ≤
        ((objects.filter fun e => ends e ⊆ s).card : ℝ) := by
  classical
  let m : ℕ := min u.card (Nat.ceil (p * (u.card : ℝ)) + 1)
  have hnums :
      2 ≤ m ∧ m ≤ u.card ∧
      (m : ℝ) ≤ p * (u.card : ℝ) + 2 ∧
      p ^ 2 * (u.card : ℝ) * ((u.card : ℝ) - 1) ≤
        (m : ℝ) * ((m : ℝ) - 1) := by
    simpa only [m] using sample_size_bounds u.card hn p hp hp1
  let family := u.powersetCard m
  have hnonempty : family.Nonempty := by
    simpa [family] using (Finset.powersetCard_nonempty.mpr hnums.2.1)
  obtain ⟨s, hs, havg⟩ :=
    exists_sum_le_card_mul family hnonempty
      (fun s => ((objects.filter fun e => ends e ⊆ s).card : ℝ))
  have hsum :
      (∑ s ∈ family,
        ((objects.filter fun e => ends e ⊆ s).card : ℝ)) =
        (objects.card : ℝ) *
          (Nat.choose (u.card - 2) (m - 2) : ℝ) := by
    exact_mod_cast sum_card_contained_objects u objects ends m hends hnums.1
  have hmem : s ⊆ u ∧ s.card = m := Finset.mem_powersetCard.mp hs
  have havg' :
      (objects.card : ℝ) *
        (Nat.choose (u.card - 2) (m - 2) : ℝ) ≤
        (Nat.choose u.card m : ℝ) *
          ((objects.filter fun e => ends e ⊆ s).card : ℝ) := by
    simpa [family, Finset.card_powersetCard, hsum] using havg
  have hratio :=
    choose_ratio_bound u.card m hn hnums.1 p hnums.2.2.2
  have hcpos : (0 : ℝ) < (Nat.choose u.card m : ℝ) := by
    exact_mod_cast Nat.choose_pos hnums.2.1
  have hscaled := mul_le_mul_of_nonneg_left hratio
    (Nat.cast_nonneg objects.card : (0 : ℝ) ≤ _)
  refine ⟨s, hmem.1, ?_, ?_⟩
  · simpa [hmem.2] using hnums.2.2.1
  · nlinarith [havg', hscaled]

end HadwigerLean.FiniteSampling
namespace HadwigerLean.FiniteSampling

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Counting the edges whose two endpoints lie in a vertex sample agrees
with the edge count of its induced graph. -/
theorem sampled_edges_eq_induced_count (G : SimpleGraph V)
    [DecidableRel G.Adj] (s : Finset V) :
    ((G.edgeFinset.filter fun e => e.toFinset ⊆ s).card) =
      edgeCount (G.induce (s : Set V)) := by
  classical
  have hmap := G.map_edgeFinset_induce (s := (s : Set V))
  have hcard := congrArg Finset.card hmap
  rw [Finset.card_map] at hcard
  have hfilter :
      G.edgeFinset ∩ s.sym2 =
        G.edgeFinset.filter (fun e => e.toFinset ⊆ s) := by
    ext e
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_sym2_iff]
    constructor
    · rintro ⟨he, hs⟩
      refine ⟨he, ?_⟩
      intro v hv
      exact hs v (Sym2.mem_toFinset.mp hv)
    · rintro ⟨he, hs⟩
      refine ⟨he, ?_⟩
      intro v hv
      exact hs (Sym2.mem_toFinset.mpr hv)
  simp only [Finset.toFinset_coe] at hcard
  rw [hfilter] at hcard
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hcard
  simpa only [edgeCount] using hcard.symm

/-- Graph form of the finite sampling estimate (F.4). -/
theorem exists_induced_sample (G : SimpleGraph V)
    (hn : 2 ≤ Fintype.card V) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ∃ s : Finset V,
      (s.card : ℝ) ≤ p * (Fintype.card V : ℝ) + 2 ∧
      p ^ 2 * (edgeCount G : ℝ) ≤
        (edgeCount (G.induce (s : Set V)) : ℝ) := by
  classical
  have hends :
      ∀ e ∈ G.edgeFinset, e.toFinset ⊆ (Finset.univ : Finset V) ∧
        e.toFinset.card = 2 := by
    intro e he
    exact ⟨Finset.subset_univ _, G.card_toFinset_mem_edgeFinset ⟨e, he⟩⟩
  obtain ⟨s, _, hsize, hedge⟩ :=
    exists_sample_objects (Finset.univ : Finset V) G.edgeFinset
      Sym2.toFinset hends (by simpa using hn) p hp hp1
  refine ⟨s, by simpa using hsize, ?_⟩
  rw [edgeCount_eq_card_edgeFinset]
  rw [← sampled_edges_eq_induced_count]
  exact hedge

end HadwigerLean.FiniteSampling
