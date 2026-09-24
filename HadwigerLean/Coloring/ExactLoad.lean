import HadwigerLean.Coloring.PairLoad
import Mathlib.Tactic.Linarith

/-!
# Exact vertex loads for pair-constrained fractional colorings

The paper normalizes an optimal pair-constrained coloring by moving weight
from a stable set to the set obtained by deleting an overcovered vertex.
This module develops that transformation without changing other vertex loads
or increasing pair loads.
-/

namespace HadwigerLean

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Delete a vertex from a stable set, returning `none` if the result is empty. -/
noncomputable def eraseStable? (G : SimpleGraph V) (v : V)
    (S : StableSet G) : Option (StableSet G) := by
  classical
  by_cases h : (S.1.erase v).Nonempty
  · have hs : G.IsIndepSet ((S.1.erase v : Finset V) : Set V) :=
      (mem_stableFinsets G _).mp
        (stableFinsets_downward G (Finset.erase_subset v S.1)
          (stableSet_mem G S))
    exact some ⟨S.1.erase v, h, hs⟩
  · exact none

private theorem eraseStable?_some (G : SimpleGraph V) (v : V)
    (S T : StableSet G) (h : eraseStable? G v S = some T) :
    T.1 = S.1.erase v := by
  classical
  unfold eraseStable? at h
  split_ifs at h with hne
  · exact congrArg Subtype.val (Option.some.inj h).symm

/-- Transported mass from `S` to its vertex deletion, when nonempty. -/
noncomputable def deletionMass (G : SimpleGraph V) (v : V)
    (x : StableSet G → ℝ) (t : ℝ) (T : StableSet G) : ℝ :=
  ∑ S : StableSet G,
    if v ∈ S.1 ∧ eraseStable? G v S = some T then t * x S else 0

/-- Move a fraction `t` of every weight at a set containing `v` to the
set obtained by deleting `v`; discard the fraction from singleton sets. -/
noncomputable def deleteVertexWeight (G : SimpleGraph V) (v : V)
    (x : StableSet G → ℝ) (t : ℝ) (T : StableSet G) : ℝ :=
  (if v ∈ T.1 then (1 - t) * x T else x T) + deletionMass G v x t T


private theorem sum_deletionMass_filter (G : SimpleGraph V) (v : V)
    (x : StableSet G → ℝ) (t : ℝ) (P : StableSet G → Prop) [DecidablePred P] :
    (∑ T : StableSet G, if P T then deletionMass G v x t T else 0) =
      ∑ S : StableSet G,
        if v ∈ S.1 then
          match eraseStable? G v S with
          | some T => if P T then t * x S else 0
          | none => 0
        else 0 := by
  classical
  calc
    (∑ T : StableSet G, if P T then deletionMass G v x t T else 0) =
        ∑ T : StableSet G, ∑ S : StableSet G,
          if P T ∧ v ∈ S.1 ∧ eraseStable? G v S = some T then t * x S else 0 := by
      apply Finset.sum_congr rfl
      intro T _
      by_cases hP : P T
      · simp [hP, deletionMass]
      · simp [hP]
    _ = ∑ S : StableSet G, ∑ T : StableSet G,
          if P T ∧ v ∈ S.1 ∧ eraseStable? G v S = some T then t * x S else 0 := by
      exact Finset.sum_comm
    _ = ∑ S : StableSet G,
          if v ∈ S.1 then
            match eraseStable? G v S with
            | some T => if P T then t * x S else 0
            | none => 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases hv : v ∈ S.1
      · cases h : eraseStable? G v S with
        | none => simp [hv]
        | some T =>
            simp only [hv, if_true]
            have hterm (U : StableSet G) :
                (if P U ∧ T = U then t * x S else 0) =
                  if U = T then (if P T then t * x S else 0) else 0 := by
              by_cases hUT : U = T
              · subst U
                simp
              · have hTU : T ≠ U := Ne.symm hUT
                simp [hUT, hTU]
            simp only [true_and, Option.some.injEq]
            simp_rw [hterm]
            simp
      · simp [hv]


private theorem sum_deleteVertexWeight_filter (G : SimpleGraph V) (v : V)
    (x : StableSet G → ℝ) (t : ℝ) (P : StableSet G → Prop) [DecidablePred P] :
    (∑ T : StableSet G, if P T then deleteVertexWeight G v x t T else 0) =
      ∑ S : StableSet G,
        ((if P S then (if v ∈ S.1 then (1 - t) * x S else x S) else 0) +
        (if v ∈ S.1 then
          match eraseStable? G v S with
          | some T => if P T then t * x S else 0
          | none => 0
        else 0)) := by
  classical
  calc
    (∑ T : StableSet G, if P T then deleteVertexWeight G v x t T else 0) =
        ∑ T : StableSet G,
          ((if P T then (if v ∈ T.1 then (1 - t) * x T else x T) else 0) +
          (if P T then deletionMass G v x t T else 0)) := by
      apply Finset.sum_congr rfl
      intro T _
      by_cases hP : P T <;> simp [hP, deleteVertexWeight]
    _ = (∑ T : StableSet G,
          if P T then (if v ∈ T.1 then (1 - t) * x T else x T) else 0) +
        (∑ T : StableSet G, if P T then deletionMass G v x t T else 0) := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      rw [sum_deletionMass_filter]
      rw [← Finset.sum_add_distrib]

private theorem eraseStable?_exists (G : SimpleGraph V) (v : V)
    (S : StableSet G) (h : (S.1.erase v).Nonempty) :
    ∃ T : StableSet G, eraseStable? G v S = some T ∧
      T.1 = S.1.erase v := by
  classical
  unfold eraseStable?
  split_ifs
  · exact ⟨_, rfl, rfl⟩



private theorem eraseStable?_not_mem (G : SimpleGraph V) (v : V)
    (S T : StableSet G) (h : eraseStable? G v S = some T) :
    v ∉ T.1 := by
  rw [eraseStable?_some G v S T h]
  simp

theorem deleteVertexWeight_nonneg (G : SimpleGraph V) (v : V)
    (x : StableSet G → ℝ) (t : ℝ)
    (hx : ∀ S, 0 ≤ x S) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (T : StableSet G) :
    0 ≤ deleteVertexWeight G v x t T := by
  have hbase : 0 ≤ (if v ∈ T.1 then (1 - t) * x T else x T) := by
    by_cases hv : v ∈ T.1
    · simp only [hv, if_true]
      exact mul_nonneg (sub_nonneg.mpr ht1) (hx T)
    · simpa [hv] using hx T
  have hmass : 0 ≤ deletionMass G v x t T := by
    unfold deletionMass
    apply Finset.sum_nonneg
    intro S _
    split_ifs
    · exact mul_nonneg ht0 (hx S)
    · exact le_rfl
  exact add_nonneg hbase hmass


theorem vertexLoad_deleteVertexWeight_self (G : SimpleGraph V) (v : V)
    (x : StableSet G → ℝ) (t : ℝ) :
    vertexLoad G (deleteVertexWeight G v x t) v =
      (1 - t) * vertexLoad G x v := by
  classical
  unfold vertexLoad
  rw [sum_deleteVertexWeight_filter G v x t (fun T => v ∈ T.1)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hv : v ∈ S.1
  · cases hT : eraseStable? G v S with
    | none => simp [hv]
    | some T =>
        have hn : v ∉ T.1 := eraseStable?_not_mem G v S T hT
        simp [hv, hn]
  · simp [hv]


theorem vertexLoad_deleteVertexWeight_other (G : SimpleGraph V)
    (v u : V) (huv : u ≠ v) (x : StableSet G → ℝ) (t : ℝ) :
    vertexLoad G (deleteVertexWeight G v x t) u =
      vertexLoad G x u := by
  classical
  unfold vertexLoad
  rw [sum_deleteVertexWeight_filter G v x t (fun T => u ∈ T.1)]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hv : v ∈ S.1
  · by_cases hu : u ∈ S.1
    · have hne : (S.1.erase v).Nonempty :=
        ⟨u, Finset.mem_erase.mpr ⟨huv, hu⟩⟩
      obtain ⟨T, hT, hval⟩ := eraseStable?_exists G v S hne
      have huT : u ∈ T.1 := by
        rw [hval]
        exact Finset.mem_erase.mpr ⟨huv, hu⟩
      simp [hv, hu, hT, huT]
      ring
    · cases hT : eraseStable? G v S with
      | none => simp [hv, hu]
      | some T =>
          have hn : u ∉ T.1 := by
            rw [eraseStable?_some G v S T hT]
            simp [hu]
          simp [hv, hu, hn]
  · simp [hv]


private theorem sum_deleteVertexWeight_filter_le (G : SimpleGraph V) (v : V)
    (x : StableSet G → ℝ) (t : ℝ) (P : StableSet G → Prop)
    [DecidablePred P] (hx : ∀ S, 0 ≤ x S) (ht : 0 ≤ t)
    (hP : ∀ S T, eraseStable? G v S = some T → P T → P S) :
    (∑ T : StableSet G, if P T then deleteVertexWeight G v x t T else 0) ≤
      ∑ S : StableSet G, if P S then x S else 0 := by
  classical
  rw [sum_deleteVertexWeight_filter]
  apply Finset.sum_le_sum
  intro S _
  by_cases hv : v ∈ S.1
  · cases hT : eraseStable? G v S with
    | none =>
        by_cases hPS : P S
        · simp only [hv, hPS, ↓reduceIte]
          nlinarith [mul_nonneg ht (hx S)]
        · simp [hv, hPS]
    | some T =>
        by_cases hPT : P T
        · have hPS : P S := hP S T hT hPT
          simp [hv, hPT, hPS]
          nlinarith
        · by_cases hPS : P S
          · simp [hv, hPT, hPS]
            nlinarith [mul_nonneg ht (hx S)]
          · simp [hv, hPT, hPS]
  · simp [hv]

theorem fractionalCost_deleteVertexWeight_le (G : SimpleGraph V) (v : V)
    (x : StableSet G → ℝ) (t : ℝ)
    (hx : ∀ S, 0 ≤ x S) (ht : 0 ≤ t) :
    fractionalCost G (deleteVertexWeight G v x t) ≤
      fractionalCost G x := by
  classical
  unfold fractionalCost
  simpa using sum_deleteVertexWeight_filter_le G v x t
    (fun _ : StableSet G => True) hx ht
    (by intro S T h htrue; trivial)

theorem pairLoad_deleteVertexWeight_le (G : SimpleGraph V) (v : V)
    (x : StableSet G → ℝ) (t : ℝ) (p : Finset V)
    (hx : ∀ S, 0 ≤ x S) (ht : 0 ≤ t) :
    pairLoad G (deleteVertexWeight G v x t) p ≤ pairLoad G x p := by
  classical
  unfold pairLoad
  apply sum_deleteVertexWeight_filter_le G v x t
    (fun S : StableSet G => p ⊆ S.1) hx ht
  intro S T hT hp
  rw [eraseStable?_some G v S T hT] at hp
  exact hp.trans (Finset.erase_subset v S.1)


theorem isPairConstrainedColoring_deleteVertexWeight
    (G : SimpleGraph V) (v : V) (x : StableSet G → ℝ)
    (δ t : ℝ) (hx : IsPairConstrainedColoring G δ x)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hload : 1 ≤ (1 - t) * vertexLoad G x v) :
    IsPairConstrainedColoring G δ (deleteVertexWeight G v x t) := by
  constructor
  · constructor
    · exact deleteVertexWeight_nonneg G v x t hx.1.1 ht0 ht1
    · intro u
      by_cases huv : u = v
      · subst u
        rw [vertexLoad_deleteVertexWeight_self]
        exact hload
      · rw [vertexLoad_deleteVertexWeight_other G v u huv]
        exact hx.1.2 u
  · intro p
    exact (pairLoad_deleteVertexWeight_le G v x t p hx.1.1 ht0).trans
      (hx.2 p)

theorem exists_pairConstrained_normalize_vertex (G : SimpleGraph V)
    (v : V) (x : StableSet G → ℝ) (δ : ℝ)
    (hx : IsPairConstrainedColoring G δ x) :
    ∃ y : StableSet G → ℝ,
      IsPairConstrainedColoring G δ y ∧
      vertexLoad G y v = 1 ∧
      (∀ u, u ≠ v → vertexLoad G y u = vertexLoad G x u) ∧
      fractionalCost G y ≤ fractionalCost G x := by
  let L := vertexLoad G x v
  have hL : 1 ≤ L := hx.1.2 v
  have hLpos : 0 < L := by linarith
  let t : ℝ := 1 - 1 / L
  have hdiv0 : 0 ≤ 1 / L := div_nonneg (by norm_num) hLpos.le
  have hdiv1 : 1 / L ≤ 1 := by
    apply (div_le_iff₀ hLpos).2
    nlinarith
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hscale : (1 - t) * L = 1 := by
    dsimp [t]
    field_simp
    ring
  let y := deleteVertexWeight G v x t
  refine ⟨y, ?_, ?_, ?_, ?_⟩
  · exact isPairConstrainedColoring_deleteVertexWeight G v x δ t hx
      ht0 ht1 (by simpa [L] using hscale.ge)
  · simpa [y, L] using
      (vertexLoad_deleteVertexWeight_self G v x t).trans hscale
  · intro u huv
    exact vertexLoad_deleteVertexWeight_other G v u huv x t
  · exact fractionalCost_deleteVertexWeight_le G v x t hx.1.1 ht0


/-- Normalize every vertex in a finite set while preserving the LP constraints. -/
theorem exists_pairConstrained_exact_on (G : SimpleGraph V)
    (δ : ℝ) (x : StableSet G → ℝ)
    (hx : IsPairConstrainedColoring G δ x) (s : Finset V) :
    ∃ y : StableSet G → ℝ,
      IsPairConstrainedColoring G δ y ∧
      (∀ v ∈ s, vertexLoad G y v = 1) ∧
      fractionalCost G y ≤ fractionalCost G x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨x, hx, ?_, le_rfl⟩
      simp
  | @insert v s hv ih =>
      obtain ⟨y, hy, hyS, hcost⟩ := ih
      obtain ⟨z, hz, hzv, hzother, hcostz⟩ :=
        exists_pairConstrained_normalize_vertex G v y δ hy
      refine ⟨z, hz, ?_, hcostz.trans hcost⟩
      intro u hu
      rcases Finset.mem_insert.mp hu with huv | hus
      · subst u
        exact hzv
      · have huv : u ≠ v := by
          intro heq
          subst u
          exact hv hus
        rw [hzother u huv]
        exact hyS u hus

/-- Any feasible pair-constrained coloring can be made exact at every vertex
without increasing its cost. -/
theorem exists_pairConstrained_exact (G : SimpleGraph V)
    (δ : ℝ) (x : StableSet G → ℝ)
    (hx : IsPairConstrainedColoring G δ x) :
    ∃ y : StableSet G → ℝ,
      IsPairConstrainedColoring G δ y ∧
      (∀ v, vertexLoad G y v = 1) ∧
      fractionalCost G y ≤ fractionalCost G x := by
  obtain ⟨y, hy, hload, hcost⟩ :=
    exists_pairConstrained_exact_on G δ x hx Finset.univ
  exact ⟨y, hy, (by intro v; exact hload v (Finset.mem_univ v)), hcost⟩

/-- The attained pair-constrained LP optimum can be chosen with all vertex
loads equal to one, as required by the rounding lemma. -/
theorem exists_pairConstrained_exact_minimizer (G : SimpleGraph V)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ x : StableSet G → ℝ,
      IsPairConstrainedColoring G δ x ∧
      (∀ v, vertexLoad G x v = 1) ∧
      (∀ y, IsPairConstrainedColoring G δ y →
        fractionalCost G x ≤ fractionalCost G y) := by
  obtain ⟨x, hx, hmin⟩ := exists_pairConstrained_minimizer G hδ
  obtain ⟨y, hy, hload, hcost⟩ :=
    exists_pairConstrained_exact G δ x hx
  refine ⟨y, hy, hload, ?_⟩
  intro z hz
  exact hcost.trans (hmin z hz)

end HadwigerLean
