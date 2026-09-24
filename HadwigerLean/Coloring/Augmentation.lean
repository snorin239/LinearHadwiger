import HadwigerLean.Coloring.ExactLoad
import HadwigerLean.Coloring.FractionalLP
import Mathlib.Tactic.Linarith

/-!
# Pair-dual penalties and bounded-degree augmentation

This module develops the LP side of the paper's augmentation lemma. The
rounding theorem will be supplied by a separate module.
-/

namespace HadwigerLean

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
private theorem nonedgePair_not_subset_singleton (G : SimpleGraph V)
    (p : NonedgePair G) (v : V) : ¬p.1 ⊆ ({v} : Finset V) := by
  intro hsub
  have hcard := Finset.card_le_card hsub
  have hp := p.property.1
  simp [hp] at hcard

/-- Every feasible pair-dual vertex price is at most one. -/
theorem pairDual_vertex_le_one (G : SimpleGraph V)
    {a : V → ℝ} {b : NonedgePair G → ℝ}
    (hab : IsPairDualFeasible G a b) (v : V) : a v ≤ 1 := by
  have h := hab.2.2 (singletonStableSet G v)
  have hzero :
      (∑ p : NonedgePair G,
        if p.1 ⊆ ({v} : Finset V) then b p else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    simp [nonedgePair_not_subset_singleton G p v]
  change (∑ u ∈ ({v} : Finset V), a u) -
    (∑ p : NonedgePair G,
      if p.1 ⊆ ({v} : Finset V) then b p else 0) ≤ 1 at h
  rw [hzero] at h
  simpa using h

/-- Paper equation (penalty): the total dual penalty times its tolerance is
at most the graph order. -/
theorem pairDual_penalty_le_order (G : SimpleGraph V) (δ : ℝ)
    {x : StableSet G → ℝ} {a : V → ℝ}
    {b : NonedgePair G → ℝ}
    (hx : IsPairConstrainedColoring G δ x)
    (hab : IsPairDualFeasible G a b)
    (heq : fractionalCost G x = pairDualValue G δ a b) :
    δ * (∑ p : NonedgePair G, b p) ≤ (Fintype.card V : ℝ) := by
  have ha : (∑ v : V, a v) ≤ (Fintype.card V : ℝ) := by
    calc
      (∑ v : V, a v) ≤ ∑ _v : V, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro v _
        exact pairDual_vertex_le_one G hab v
      _ = (Fintype.card V : ℝ) := by simp
  have hnonneg : 0 ≤ fractionalCost G x := fractionalCost_nonneg G hx.1
  rw [heq, pairDualValue] at hnonneg
  linarith


/-- Total pair-dual penalty incident with a vertex. -/
noncomputable def incidentPenalty (G : SimpleGraph V)
    (b : NonedgePair G → ℝ) (v : V) : ℝ :=
  ∑ p : NonedgePair G, if v ∈ p.1 then b p else 0

theorem incidentPenalty_nonneg (G : SimpleGraph V)
    {b : NonedgePair G → ℝ} (hb : ∀ p, 0 ≤ b p) (v : V) :
    0 ≤ incidentPenalty G b v := by
  unfold incidentPenalty
  apply Finset.sum_nonneg
  intro p _
  split_ifs
  · exact hb p
  · exact le_rfl

/-- Each unordered pair contributes its penalty at exactly two vertices. -/
theorem sum_incidentPenalty (G : SimpleGraph V)
    (b : NonedgePair G → ℝ) :
    (∑ v : V, incidentPenalty G b v) =
      2 * ∑ p : NonedgePair G, b p := by
  classical
  unfold incidentPenalty
  rw [Finset.sum_comm]
  calc
    (∑ p : NonedgePair G, ∑ v : V, if v ∈ p.1 then b p else 0) =
        ∑ p : NonedgePair G, ∑ v ∈ p.1, b p := by
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_filter]
      congr 1
      simp
    _ = ∑ p : NonedgePair G, 2 * b p := by
      apply Finset.sum_congr rfl
      intro p _
      simp [p.property.1]
    _ = 2 * ∑ p : NonedgePair G, b p := by rw [Finset.mul_sum]


/-- Vertices whose incident dual penalty exceeds a threshold. -/
noncomputable def heavyVertices (G : SimpleGraph V)
    (b : NonedgePair G → ℝ) (θ : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => θ < incidentPenalty G b v)

theorem heavyVertices_card_mul_le_sum (G : SimpleGraph V)
    (b : NonedgePair G → ℝ) (θ : ℝ)
    (hb : ∀ p, 0 ≤ b p) :
    ((heavyVertices G b θ).card : ℝ) * θ ≤
      ∑ v : V, incidentPenalty G b v := by
  classical
  let X := heavyVertices G b θ
  calc
    (X.card : ℝ) * θ = ∑ _v ∈ X, θ := by simp
    _ ≤ ∑ v ∈ X, incidentPenalty G b v := by
      apply Finset.sum_le_sum
      intro v hv
      exact le_of_lt (Finset.mem_filter.mp hv).2
    _ ≤ ∑ v : V, incidentPenalty G b v := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ _
      · intro v _ _
        exact incidentPenalty_nonneg G hb v

/-- The dual penalty bound controls the number of high-penalty vertices. -/
theorem heavyVertices_card_le (G : SimpleGraph V)
    (δ γ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
    {x : StableSet G → ℝ} {a : V → ℝ}
    {b : NonedgePair G → ℝ}
    (hx : IsPairConstrainedColoring G δ x)
    (hab : IsPairDualFeasible G a b)
    (heq : fractionalCost G x = pairDualValue G δ a b) :
    ((heavyVertices G b (2 / (δ * γ))).card : ℝ) ≤
      γ * (Fintype.card V : ℝ) := by
  have hb := hab.2.1
  have hpen := pairDual_penalty_le_order G δ hx hab heq
  have hcount := heavyVertices_card_mul_le_sum G b
    (2 / (δ * γ)) hb
  rw [sum_incidentPenalty] at hcount
  have hden : 0 < δ * γ := mul_pos hδ hγ
  have hcount' :
      ((heavyVertices G b (2 / (δ * γ))).card : ℝ) * 2 ≤
        (2 * ∑ p : NonedgePair G, b p) * (δ * γ) := by
    calc
      ((heavyVertices G b (2 / (δ * γ))).card : ℝ) * 2 =
          (((heavyVertices G b (2 / (δ * γ))).card : ℝ) *
            (2 / (δ * γ))) * (δ * γ) := by
          field_simp
      _ ≤ (2 * ∑ p : NonedgePair G, b p) * (δ * γ) :=
        mul_le_mul_of_nonneg_right hcount hden.le
  have hpenγ := mul_le_mul_of_nonneg_right hpen hγ.le
  nlinarith

/-- The nonedges selected by large dual penalties outside the exceptional set. -/
noncomputable def penaltyGraph (G : SimpleGraph V)
    (b : NonedgePair G → ℝ) (X : Finset V) (cutoff : ℝ) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ p : NonedgePair G,
    p.1 = {u, v} ∧ u ∉ X ∧ v ∉ X ∧ cutoff ≤ b p
  symm := ⟨by
    intro u v ⟨hne, p, hp, hu, hv, hb⟩
    refine ⟨hne.symm, p, ?_, hv, hu, hb⟩
    simpa [Finset.pair_comm] using hp⟩
  loopless := ⟨by
    intro u huu
    exact huu.1 rfl⟩

omit [Fintype V] in
theorem penaltyGraph_le_compl (G : SimpleGraph V)
    (b : NonedgePair G → ℝ) (X : Finset V) (cutoff : ℝ) :
    penaltyGraph G b X cutoff ≤ Gᶜ := by
  intro u v huv
  obtain ⟨hne, p, hp, _, _, _⟩ := huv
  have hu : u ∈ p.1 := by rw [hp]; simp
  have hv : v ∈ p.1 := by rw [hp]; simp
  exact (SimpleGraph.compl_adj G u v).2 ⟨hne, p.property.2 hu hv hne⟩

/-- Selected penalty pairs incident with one vertex. -/
noncomputable def selectedIncidentPairs (G : SimpleGraph V)
    (b : NonedgePair G → ℝ) (v : V) (cutoff : ℝ) :
    Finset (NonedgePair G) := by
  classical
  exact Finset.univ.filter (fun p => v ∈ p.1 ∧ cutoff ≤ b p)

theorem selectedIncidentPairs_card_mul_le (G : SimpleGraph V)
    (b : NonedgePair G → ℝ) (v : V) (cutoff : ℝ)
    (hb : ∀ p, 0 ≤ b p) :
    ((selectedIncidentPairs G b v cutoff).card : ℝ) * cutoff ≤
      incidentPenalty G b v := by
  classical
  let P := selectedIncidentPairs G b v cutoff
  let I : Finset (NonedgePair G) :=
    Finset.univ.filter (fun p => v ∈ p.1)
  have hsub : P ⊆ I := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp'.1⟩
  calc
    (P.card : ℝ) * cutoff = ∑ _p ∈ P, cutoff := by simp
    _ ≤ ∑ p ∈ P, b p := by
      apply Finset.sum_le_sum
      intro p hp
      exact (Finset.mem_filter.mp hp).2.2
    _ ≤ ∑ p ∈ I, b p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p _ _
      exact hb p
    _ = incidentPenalty G b v := by
      simp [I, incidentPenalty, Finset.sum_filter]

noncomputable instance penaltyGraph_neighborFintype (G : SimpleGraph V)
    (b : NonedgePair G → ℝ) (X : Finset V) (cutoff : ℝ) (v : V) :
    Fintype ((penaltyGraph G b X cutoff).neighborSet v) := by
  classical
  infer_instance
/-- Neighbors in the penalty graph inject into selected penalty pairs. -/
theorem penaltyGraph_degree_le_selectedPairs_card (G : SimpleGraph V)
    (b : NonedgePair G → ℝ) (X : Finset V) (cutoff : ℝ)
    (v : V) :
    (penaltyGraph G b X cutoff).degree v ≤
      (selectedIncidentPairs G b v cutoff).card := by
  classical
  let F := penaltyGraph G b X cutoff
  let P := selectedIncidentPairs G b v cutoff
  let pick (w : F.neighborFinset v) : NonedgePair G :=
    Classical.choose (((F.mem_neighborFinset v w.1).mp w.2).2)
  have hspec (w : F.neighborFinset v) :
      (pick w).1 = {v, w.1} ∧ v ∉ X ∧ w.1 ∉ X ∧
        cutoff ≤ b (pick w) :=
    Classical.choose_spec (((F.mem_neighborFinset v w.1).mp w.2).2)
  let f : (F.neighborFinset v) → P := fun w =>
    ⟨pick w, by
      change pick w ∈ selectedIncidentPairs G b v cutoff
      simp only [selectedIncidentPairs, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨by rw [(hspec w).1]; simp, (hspec w).2.2.2⟩⟩
  have hf : Function.Injective f := by
    intro w z heq
    have hp : (pick w).1 = (pick z).1 :=
      congrArg (fun p : P => p.1.1) heq
    rw [(hspec w).1, (hspec z).1] at hp
    have hwmem : w.1 ∈ ({v, z.1} : Finset V) := by
      rw [← hp]
      simp
    have hne : w.1 ≠ v :=
      ((F.mem_neighborFinset v w.1).mp w.2).1.symm
    have hwz : w.1 = z.1 := by
      simpa [hne] using hwmem
    exact Subtype.ext hwz
  change (F.neighborFinset v).card ≤ P.card
  exact Finset.card_le_card_of_injective hf

theorem penaltyGraph_degree_mul_le_incidentPenalty (G : SimpleGraph V)
    (b : NonedgePair G → ℝ) (X : Finset V) (cutoff : ℝ)
    (v : V) (hb : ∀ p, 0 ≤ b p) (hcutoff : 0 ≤ cutoff) :
    ((penaltyGraph G b X cutoff).degree v : ℝ) * cutoff ≤
      incidentPenalty G b v := by
  have hcard := penaltyGraph_degree_le_selectedPairs_card G b X cutoff v
  have hcast :
      ((penaltyGraph G b X cutoff).degree v : ℝ) ≤
        ((selectedIncidentPairs G b v cutoff).card : ℝ) := by
    exact_mod_cast hcard
  exact (mul_le_mul_of_nonneg_right hcast hcutoff).trans
    (selectedIncidentPairs_card_mul_le G b v cutoff hb)

theorem penaltyGraph_degree_zero_of_mem (G : SimpleGraph V)
    (b : NonedgePair G → ℝ) (X : Finset V) (cutoff : ℝ)
    (v : V) (hv : v ∈ X) :
    (penaltyGraph G b X cutoff).degree v = 0 := by
  classical
  let F := penaltyGraph G b X cutoff
  apply (F.degree_eq_zero v).2
  intro w hadj
  obtain ⟨_, p, _, hnot, _, _⟩ := hadj
  exact hnot hv

/-- Real-valued maximum-degree estimate before the final ceiling operation. -/
theorem penaltyGraph_degree_le_ratio (G : SimpleGraph V)
    (b : NonedgePair G → ℝ) (θ cutoff : ℝ)
    (hb : ∀ p, 0 ≤ b p) (hθ : 0 ≤ θ) (hcutoff : 0 < cutoff)
    (v : V) :
    ((penaltyGraph G b (heavyVertices G b θ) cutoff).degree v : ℝ) ≤
      θ / cutoff := by
  classical
  let X := heavyVertices G b θ
  by_cases hv : v ∈ X
  · have hzero := penaltyGraph_degree_zero_of_mem G b X cutoff v hv
    have hzero' : ((penaltyGraph G b X cutoff).degree v : ℝ) = 0 := by
      exact_mod_cast hzero
    rw [hzero']
    exact div_nonneg hθ hcutoff.le
  · have hnot : ¬ θ < incidentPenalty G b v := by
      intro hgt
      apply hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hgt⟩
    have hinc : incidentPenalty G b v ≤ θ := le_of_not_gt hnot
    have hdegree :=
      penaltyGraph_degree_mul_le_incidentPenalty G b X cutoff v hb
        hcutoff.le
    apply (le_div_iff₀ hcutoff).2
    exact hdegree.trans hinc

noncomputable instance penaltyGraph_decidableRel (G : SimpleGraph V)
    (b : NonedgePair G → ℝ) (X : Finset V) (cutoff : ℝ) :
    DecidableRel (penaltyGraph G b X cutoff).Adj := by
  classical
  infer_instance
theorem penaltyGraph_maxDegree_le_ceil (G : SimpleGraph V)
    (b : NonedgePair G → ℝ) (θ cutoff : ℝ)
    (hb : ∀ p, 0 ≤ b p) (hθ : 0 ≤ θ) (hcutoff : 0 < cutoff) :
    (penaltyGraph G b (heavyVertices G b θ) cutoff).maxDegree ≤
      ⌈θ / cutoff⌉₊ := by
  classical
  apply SimpleGraph.maxDegree_le_of_forall_degree_le
  intro v
  have hdegree :=
    penaltyGraph_degree_le_ratio G b θ cutoff hb hθ hcutoff v
  have hceil : θ / cutoff ≤ (⌈θ / cutoff⌉₊ : ℝ) :=
    Nat.le_ceil _
  exact_mod_cast hdegree.trans hceil


/-- The pair-dual inequality also holds for the empty independent set. -/
theorem pairDual_sum_le_one_add (G : SimpleGraph V)
    {a : V → ℝ} {b : NonedgePair G → ℝ}
    (hab : IsPairDualFeasible G a b) (s : Finset V)
    (hs : G.IsIndepSet (s : Set V)) :
    (∑ v ∈ s, a v) ≤
      1 + ∑ p : NonedgePair G, if p.1 ⊆ s then b p else 0 := by
  classical
  by_cases hne : s.Nonempty
  · have h := hab.2.2 (⟨s, hne, hs⟩ : StableSet G)
    change (∑ v ∈ s, a v) -
      (∑ p : NonedgePair G, if p.1 ⊆ s then b p else 0) ≤ 1 at h
    linarith
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst s
    have hpen : 0 ≤
        (∑ p : NonedgePair G,
          if p.1 ⊆ (∅ : Finset V) then b p else 0) := by
      apply Finset.sum_nonneg
      intro p _
      split_ifs
      · exact hab.2.1 p
      · exact le_rfl
    simp only [Finset.sum_empty]
    linarith

/-- Nonedge pairs contained in a finite vertex set. -/
noncomputable def containedPairs (G : SimpleGraph V)
    (s : Finset V) : Finset (NonedgePair G) := by
  classical
  exact Finset.univ.filter (fun p => p.1 ⊆ s)

/-- Contained nonedge pairs inject into all two-element subsets. -/
theorem containedPairs_card_le_choose (G : SimpleGraph V)
    (s : Finset V) :
    (containedPairs G s).card ≤ Nat.choose s.card 2 := by
  classical
  have hmap : Set.MapsTo (fun p : NonedgePair G => p.1)
      (containedPairs G s) (Finset.powersetCard 2 s) := by
    intro p hp
    exact Finset.mem_powersetCard.mpr
      ⟨(Finset.mem_filter.mp hp).2, p.property.1⟩
  have hinj : Set.InjOn (fun p : NonedgePair G => p.1)
      (containedPairs G s) := by
    intro p _ q _ hpq
    exact Subtype.ext hpq
  simpa only [Finset.card_powersetCard] using
    Finset.card_le_card_of_injOn (fun p : NonedgePair G => p.1)
      hmap hinj

/-- A pointwise bound on penalties gives a binomial bound on their sum. -/
theorem pairPenalty_sum_le_choose (G : SimpleGraph V)
    (b : NonedgePair G → ℝ) (s : Finset V) (cutoff : ℝ)
    (hcutoff : 0 ≤ cutoff)
    (hb : ∀ p : NonedgePair G, p.1 ⊆ s → b p ≤ cutoff) :
    (∑ p : NonedgePair G, if p.1 ⊆ s then b p else 0) ≤
      (Nat.choose s.card 2 : ℝ) * cutoff := by
  classical
  let P := containedPairs G s
  have hcard : (P.card : ℝ) ≤ (Nat.choose s.card 2 : ℝ) := by
    exact_mod_cast containedPairs_card_le_choose G s
  calc
    (∑ p : NonedgePair G, if p.1 ⊆ s then b p else 0) =
        ∑ p ∈ P, b p := by simp [P, containedPairs, Finset.sum_filter]
    _ ≤ ∑ _p ∈ P, cutoff := by
      apply Finset.sum_le_sum
      intro p hp
      exact hb p (Finset.mem_filter.mp hp).2
    _ = (P.card : ℝ) * cutoff := by simp
    _ ≤ (Nat.choose s.card 2 : ℝ) * cutoff :=
      mul_le_mul_of_nonneg_right hcard hcutoff

omit [Fintype V] in
/-- Every pair of a stable set in the penalty graph has small penalty. -/
theorem pairPenalty_lt_of_penaltyGraph_indep (G : SimpleGraph V)
    (b : NonedgePair G → ℝ) (X s : Finset V) (cutoff : ℝ)
    (hs : (penaltyGraph G b X cutoff).IsIndepSet (s : Set V))
    (houtside : ∀ v ∈ s, v ∉ X)
    (p : NonedgePair G) (hp : p.1 ⊆ s) :
    b p < cutoff := by
  classical
  by_contra hnot
  have hlarge : cutoff ≤ b p := le_of_not_gt hnot
  obtain ⟨u, v, huv, hpEq⟩ := Finset.card_eq_two.mp p.property.1
  have hu : u ∈ s := hp (by rw [hpEq]; simp)
  have hv : v ∈ s := hp (by rw [hpEq]; simp)
  have hadj : (penaltyGraph G b X cutoff).Adj u v :=
    ⟨huv, p, hpEq, houtside u hu, houtside v hv, hlarge⟩
  exact hs hu hv huv hadj

/-- The pair dual gives a feasible fractional dual after discarding the heavy
vertices and adding all large-penalty nonedges. -/
theorem retainedPairDual_feasible (G : SimpleGraph V)
    {a : V → ℝ} {b : NonedgePair G → ℝ}
    (hab : IsPairDualFeasible G a b)
    (X : Finset V) (m : ℕ) (γ : ℝ) (hγ : 0 < γ)
    (hm : independenceNumber G ≤ m) (hm2 : 2 ≤ m) :
    IsFractionalDualFeasible
      (G ⊔ penaltyGraph G b X (γ / (Nat.choose m 2 : ℝ)))
      (fun v => if v ∈ X then 0 else a v / (1 + γ)) := by
  classical
  let C : ℝ := Nat.choose m 2
  have hC : 0 < C := by
    change 0 < (Nat.choose m 2 : ℝ)
    exact_mod_cast Nat.choose_pos hm2
  let F := penaltyGraph G b X (γ / C)
  let H := G ⊔ F
  have hden : 0 < 1 + γ := by linarith
  refine ⟨?_, ?_⟩
  · intro v
    by_cases hv : v ∈ X
    · simp [hv]
    · simp [hv, div_nonneg (hab.1 v) hden.le]
  · intro S
    let s := S.1.filter (fun v => v ∉ X)
    have hsG : G.IsIndepSet (s : Set V) := by
      intro u hu v hv huv hadj
      exact S.property.2 (Finset.mem_filter.mp hu).1
        (Finset.mem_filter.mp hv).1 huv (Or.inl hadj)
    have hsF : F.IsIndepSet (s : Set V) := by
      intro u hu v hv huv hadj
      exact S.property.2 (Finset.mem_filter.mp hu).1
        (Finset.mem_filter.mp hv).1 huv (Or.inr hadj)
    have houtside : ∀ v ∈ s, v ∉ X := by
      intro v hv
      exact (Finset.mem_filter.mp hv).2
    have hscard : s.card ≤ m :=
      (stable_card_le_independenceNumber G hsG).trans hm
    have hchoose : (Nat.choose s.card 2 : ℝ) ≤ C := by
      change (Nat.choose s.card 2 : ℝ) ≤ (Nat.choose m 2 : ℝ)
      exact_mod_cast Nat.choose_le_choose 2 hscard
    have hsmall : ∀ p : NonedgePair G, p.1 ⊆ s → b p ≤ γ / C := by
      intro p hp
      exact le_of_lt (pairPenalty_lt_of_penaltyGraph_indep G b X s
        (γ / C) hsF houtside p hp)
    have hpen := pairPenalty_sum_le_choose G b s (γ / C)
      (div_nonneg hγ.le hC.le) hsmall
    have hpair : (∑ p : NonedgePair G,
        if p.1 ⊆ s then b p else 0) ≤ γ := by
      calc
        _ ≤ (Nat.choose s.card 2 : ℝ) * (γ / C) := hpen
        _ ≤ C * (γ / C) :=
          mul_le_mul_of_nonneg_right hchoose (div_nonneg hγ.le hC.le)
        _ = γ := by field_simp
    have hsum := pairDual_sum_le_one_add G hab s hsG
    have hsum' : (∑ v ∈ s, a v) ≤ 1 + γ := by linarith
    have hweight :
        (∑ v ∈ S.1, if v ∈ X then (0 : ℝ) else a v / (1 + γ)) =
          (∑ v ∈ s, a v) / (1 + γ) := by
      rw [Finset.sum_div]
      simp [s, Finset.sum_filter]
    rw [hweight]
    exact (div_le_iff₀ hden).2 (by simpa using hsum')

/-- Discarding at most one unit of vertex price per heavy vertex gives a
quantitative lower bound on the augmented graph's fractional chromatic number. -/
theorem retainedPairDual_value_bound (G : SimpleGraph V)
    {a : V → ℝ} {b : NonedgePair G → ℝ}
    (hab : IsPairDualFeasible G a b)
    (X : Finset V) (m : ℕ) (γ : ℝ) (hγ : 0 < γ)
    (hm : independenceNumber G ≤ m) (hm2 : 2 ≤ m) :
    (∑ v : V, a v) - (X.card : ℝ) ≤
      (1 + γ) * fractionalChromaticNumber
        (G ⊔ penaltyGraph G b X (γ / (Nat.choose m 2 : ℝ))) := by
  classical
  let H := G ⊔ penaltyGraph G b X (γ / (Nat.choose m 2 : ℝ))
  let w : V → ℝ := fun v => if v ∈ X then 0 else a v / (1 + γ)
  have hw : IsFractionalDualFeasible H w :=
    retainedPairDual_feasible G hab X m γ hγ hm hm2
  have hdual : (∑ v : V, w v) ≤ fractionalChromaticNumber H :=
    fractionalDualValue_le_chromatic H hw
  have hden : 0 < 1 + γ := by linarith
  have hterm (v : V) :
      a v - (if v ∈ X then (1 : ℝ) else 0) ≤
        (1 + γ) * w v := by
    by_cases hv : v ∈ X
    · simp only [hv, ↓reduceIte, w, mul_zero]
      linarith [pairDual_vertex_le_one G hab v]
    · have heq : (1 + γ) * (a v / (1 + γ)) = a v := by
        field_simp
      simp [hv, w, heq]
  have hsum :
      (∑ v : V, (a v - (if v ∈ X then (1 : ℝ) else 0))) ≤
        (∑ v : V, (1 + γ) * w v) := by
    apply Finset.sum_le_sum
    intro v _
    exact hterm v
  have hind :
      (∑ v : V, if v ∈ X then (1 : ℝ) else 0) = (X.card : ℝ) := by
    simp
  calc
    (∑ v : V, a v) - (X.card : ℝ) =
        ∑ v : V, (a v - (if v ∈ X then (1 : ℝ) else 0)) := by
      rw [Finset.sum_sub_distrib, hind]
    _ ≤ ∑ v : V, (1 + γ) * w v := hsum
    _ = (1 + γ) * ∑ v : V, w v := by rw [Finset.mul_sum]
    _ ≤ (1 + γ) * fractionalChromaticNumber H :=
      mul_le_mul_of_nonneg_left hdual hden.le

/-- Weak duality for the concrete pair-constrained coloring predicates. -/
theorem pairDual_weak_duality (G : SimpleGraph V) (δ : ℝ)
    {x : StableSet G → ℝ} {a : V → ℝ}
    {b : NonedgePair G → ℝ}
    (hx : IsPairConstrainedColoring G δ x)
    (hab : IsPairDualFeasible G a b) :
    pairDualValue G δ a b ≤ fractionalCost G x := by
  let y : V ⊕ NonedgePair G → ℝ := Sum.elim a b
  have hpr : (pairProblem G δ).PrimalFeasible x :=
    (pairProblem_primal_iff G δ x).2 hx
  have hdu : (pairProblem G δ).DualFeasible y :=
    (pairProblem_dual_iff G δ y).2 hab
  have h := (pairProblem G δ).weak_duality hpr hdu
  simpa [y, pairProblem_primalValue, pairProblem_dualValue] using h

/-- The augmentation lemma, conditional only on the separate low-pair-load
rounding theorem. All LP, penalty-graph, and quantitative dual steps are
proved here. -/
theorem exists_boundedDegree_augmentation_from_rounding
    (G : SimpleGraph V) (δ γ : ℝ) (m : ℕ)
    (hδ : 0 < δ) (hγ : 0 < γ)
    (hm : independenceNumber G ≤ m) (hm2 : 2 ≤ m)
    (hround : ∀ x : StableSet G → ℝ,
      IsPairConstrainedColoring G δ x →
      (∀ v, vertexLoad G x v = 1) →
      (chromatic G : ℝ) ≤ fractionalCost G x +
        γ * (Fintype.card V : ℝ)) :
    ∃ F : SimpleGraph V,
      F ≤ Gᶜ ∧
      (letI : DecidableRel F.Adj := Classical.decRel F.Adj
       F.maxDegree) ≤
        ⌈(2 / (δ * γ)) /
          (γ / (Nat.choose m 2 : ℝ))⌉₊ ∧
      (chromatic G : ℝ) -
        3 * γ * (Fintype.card V : ℝ) ≤
          fractionalChromaticNumber (G ⊔ F) := by
  classical
  obtain ⟨x₀, a, b, hx₀, hab, heq⟩ :=
    exists_pairConstrained_primal_dual_optima G hδ.le
  obtain ⟨x, hx, hexact, hmin⟩ :=
    exists_pairConstrained_exact_minimizer G hδ.le
  have hcost : fractionalCost G x = fractionalCost G x₀ := by
    apply le_antisymm (hmin x₀ hx₀)
    rw [heq]
    exact pairDual_weak_duality G δ hx hab
  have hround' :
      (chromatic G : ℝ) ≤
        fractionalCost G x₀ + γ * (Fintype.card V : ℝ) := by
    simpa only [hcost] using hround x hx hexact
  let X := heavyVertices G b (2 / (δ * γ))
  let F := penaltyGraph G b X (γ / (Nat.choose m 2 : ℝ))
  refine ⟨F, penaltyGraph_le_compl G b X _, ?_, ?_⟩
  · have hθ : 0 ≤ 2 / (δ * γ) :=
      div_nonneg (by norm_num) (mul_pos hδ hγ).le
    have hC : 0 < (Nat.choose m 2 : ℝ) := by
      exact_mod_cast Nat.choose_pos hm2
    exact penaltyGraph_maxDegree_le_ceil G b
      (2 / (δ * γ)) (γ / (Nat.choose m 2 : ℝ))
      hab.2.1 hθ (div_pos hγ hC)
  · have hX :
        (X.card : ℝ) ≤ γ * (Fintype.card V : ℝ) :=
      heavyVertices_card_le G δ γ hδ hγ hx₀ hab heq
    have hdual :
        (∑ v : V, a v) - (X.card : ℝ) ≤
          (1 + γ) * fractionalChromaticNumber (G ⊔ F) :=
      retainedPairDual_value_bound G hab X m γ hγ hm hm2
    have hbsum : 0 ≤ ∑ p : NonedgePair G, b p := by
      apply Finset.sum_nonneg
      intro p _
      exact hab.2.1 p
    have hτa :
        fractionalCost G x₀ ≤ ∑ v : V, a v := by
      rw [heq]
      unfold pairDualValue
      nlinarith [mul_nonneg hδ.le hbsum]
    have haN :
        (∑ v : V, a v) ≤ (Fintype.card V : ℝ) := by
      calc
        (∑ v : V, a v) ≤ ∑ _v : V, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro v _
          exact pairDual_vertex_le_one G hab v
        _ = (Fintype.card V : ℝ) := by simp
    have hτN :
        fractionalCost G x₀ ≤ (Fintype.card V : ℝ) :=
      hτa.trans haN
    have hbound :
        fractionalCost G x₀ -
          γ * (Fintype.card V : ℝ) ≤
          (1 + γ) * fractionalChromaticNumber (G ⊔ F) := by
      linarith
    have hden : 0 < 1 + γ := by linarith
    have hdiv :
        (fractionalCost G x₀ -
          γ * (Fintype.card V : ℝ)) / (1 + γ) ≤
          fractionalChromaticNumber (G ⊔ F) :=
      (div_le_iff₀ hden).2 (by simpa [mul_comm] using hbound)
    have haux :
        fractionalCost G x₀ -
          2 * γ * (Fintype.card V : ℝ) ≤
          (fractionalCost G x₀ -
            γ * (Fintype.card V : ℝ)) / (1 + γ) := by
      apply (le_div_iff₀ hden).2
      have hγτ := mul_le_mul_of_nonneg_left hτN hγ.le
      have hn0 : 0 ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
      have hγn : 0 ≤ γ * (Fintype.card V : ℝ) :=
        mul_nonneg hγ.le hn0
      have hγγn : 0 ≤ γ * (γ * (Fintype.card V : ℝ)) :=
        mul_nonneg hγ.le hγn
      nlinarith
    have hmid :
        fractionalCost G x₀ -
          2 * γ * (Fintype.card V : ℝ) ≤
          fractionalChromaticNumber (G ⊔ F) :=
      haux.trans hdiv
    linarith

/-- Flexible version of augmentation: any integer degree cap above the real
estimate suffices. This keeps ceiling arithmetic out of later arguments. -/
theorem exists_boundedDegree_augmentation_of_cap
    (G : SimpleGraph V) (δ γ : ℝ) (m d : ℕ)
    (hδ : 0 < δ) (hγ : 0 < γ)
    (hm : independenceNumber G ≤ m) (hm2 : 2 ≤ m)
    (hcap :
      (2 / (δ * γ)) /
        (γ / (Nat.choose m 2 : ℝ)) ≤ (d : ℝ))
    (hround : ∀ x : StableSet G → ℝ,
      IsPairConstrainedColoring G δ x →
      (∀ v, vertexLoad G x v = 1) →
      (chromatic G : ℝ) ≤ fractionalCost G x +
        γ * (Fintype.card V : ℝ)) :
    ∃ F : SimpleGraph V,
      F ≤ Gᶜ ∧
      (letI : DecidableRel F.Adj := Classical.decRel F.Adj
       F.maxDegree) ≤ d ∧
      (chromatic G : ℝ) -
        3 * γ * (Fintype.card V : ℝ) ≤
          fractionalChromaticNumber (G ⊔ F) := by
  obtain ⟨F, hF, hdegree, hchi⟩ :=
    exists_boundedDegree_augmentation_from_rounding
      G δ γ m hδ hγ hm hm2 hround
  refine ⟨F, hF, ?_, hchi⟩
  exact hdegree.trans (Nat.ceil_le.mpr hcap)
end HadwigerLean