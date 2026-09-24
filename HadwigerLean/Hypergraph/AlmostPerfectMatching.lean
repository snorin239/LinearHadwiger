import HadwigerLean.Hypergraph.Indexed
import HadwigerLean.Probability.FiniteBernoulli
import HadwigerLean.Quantitative.BackwardPotential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Card

/-!
Deterministic bookkeeping for the almost-perfect-matching iteration.

Probability will supply a favorable round. Here a round records its surviving
vertices and its accepted disjoint edge copies, and the lemmas track the
vertices that were deleted without being covered.
-/

namespace HadwigerLean

variable {V E : Type*} [DecidableEq V]

/-- The combinatorial data produced by a matching round. -/
structure MatchingRound (H : IndexedHypergraph V E) where
  survivors : Finset V
  survivors_subset : survivors ⊆ H.vertices
  accepted : Finset E
  accepted_matching : H.IsMatching accepted
  survivors_disjoint_accepted : Disjoint survivors (H.covered accepted)

namespace MatchingRound

variable {H : IndexedHypergraph V E} (R : MatchingRound H)

/-- Vertices lost in this round without an accepted matching edge. -/
def waste : Finset V :=
  H.vertices \ (R.survivors ∪ H.covered R.accepted)

/-- The untrimmed hypergraph on surviving vertices. -/
def nextBase : IndexedHypergraph V E := H.induce R.survivors

@[simp] theorem nextBase_vertices : R.nextBase.vertices = R.survivors := by
  simp [nextBase, Finset.inter_eq_right.mpr R.survivors_subset]

theorem accepted_covered_subset : H.covered R.accepted ⊆ H.vertices :=
  H.covered_subset_vertices R.accepted_matching.1

theorem waste_partition_card :
    R.survivors.card + (H.covered R.accepted).card + R.waste.card =
      H.vertices.card := by
  classical
  have hsub : R.survivors ∪ H.covered R.accepted ⊆ H.vertices :=
    Finset.union_subset R.survivors_subset R.accepted_covered_subset
  have hcount := Finset.card_sdiff_add_card_eq_card hsub
  have hdisj := Finset.card_union_of_disjoint R.survivors_disjoint_accepted
  change R.waste.card + (R.survivors ∪ H.covered R.accepted).card =
    H.vertices.card at hcount
  rw [hdisj] at hcount
  omega

section Union
variable [DecidableEq E]

/-- A matching found among survivors extends the accepted matching. -/
theorem matching_union_next {N : Finset E}
    (hN : R.nextBase.IsMatching N) :
    H.IsMatching (R.accepted ∪ N) := by
  classical
  constructor
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact R.accepted_matching.1 he
    · exact (H.induce_edges_subset R.survivors) (hN.1 he)
  · intro e he f hf hne
    rcases Finset.mem_union.mp he with heM | heN
    · rcases Finset.mem_union.mp hf with hfM | hfN
      · exact R.accepted_matching.2 heM hfM hne
      · apply Finset.disjoint_left.mpr
        intro v hve hvf
        have hvcovered : v ∈ H.covered R.accepted :=
          Finset.mem_biUnion.mpr ⟨e, heM, hve⟩
        have hfu : H.edge f ⊆ R.survivors :=
          (Finset.mem_filter.mp (hN.1 hfN)).2
        exact (Finset.disjoint_left.mp R.survivors_disjoint_accepted)
          (hfu hvf) hvcovered
    · rcases Finset.mem_union.mp hf with hfM | hfN
      · apply Finset.disjoint_right.mpr
        intro v hve hvf
        have hvcovered : v ∈ H.covered R.accepted :=
          Finset.mem_biUnion.mpr ⟨f, hfM, hve⟩
        have heu : H.edge e ⊆ R.survivors :=
          (Finset.mem_filter.mp (hN.1 heN)).2
        exact (Finset.disjoint_left.mp R.survivors_disjoint_accepted)
          (heu hvf) hvcovered
      · exact hN.2 heN hfN hne

/-- The vertices left uncovered after adding a later matching split into
survivors still uncovered and waste from this round. -/
theorem uncovered_partition_card {N : Finset E}
    (hN : N ⊆ R.nextBase.edges) :
    (H.covered (R.accepted ∪ N)).card +
      (R.survivors \ H.covered N).card + R.waste.card =
      H.vertices.card := by
  classical
  have hcoveredN : H.covered N ⊆ R.survivors := by
    intro v hv
    obtain ⟨e, heN, hve⟩ := Finset.mem_biUnion.mp hv
    exact (Finset.mem_filter.mp (hN heN)).2 hve
  have hdisj : Disjoint (H.covered R.accepted) (H.covered N) :=
    Finset.disjoint_of_subset_right hcoveredN R.survivors_disjoint_accepted.symm
  have hcoveredUnion :
      H.covered (R.accepted ∪ N) =
        H.covered R.accepted ∪ H.covered N := by
    unfold IndexedHypergraph.covered
    exact Finset.union_biUnion
  have hcountN := Finset.card_sdiff_add_card_eq_card hcoveredN
  have hcountR := R.waste_partition_card
  rw [hcoveredUnion, Finset.card_union_of_disjoint hdisj]
  omega
/-- Trim the induced survivor hypergraph, preserving uniformity and codegree,
while charging every discarded edge to initial degree excess. -/
theorem exists_trimmed_next {r : ℕ} (hunif : H.IsUniform r)
    (D' : ℕ) :
    ∃ K : IndexedHypergraph V E,
      K.vertices = R.survivors ∧
      K.edges ⊆ R.nextBase.edges ∧
      K.IsUniform r ∧
      (∀ v ∈ K.vertices, K.degree v ≤ D') ∧
      (∀ u v, K.codegree u v ≤ H.codegree u v) ∧
      (K.degreeDeficit D' + r * R.nextBase.edges.card ≤
        R.survivors.card * D' +
          r * R.nextBase.degreeExcess D') ∧
      K.edge = H.edge := by
  classical
  obtain ⟨F, hF, hcap, hcount⟩ := R.nextBase.exists_degree_trim D'
  let K := R.nextBase.restrictEdges F hF
  have hKunif : K.IsUniform r := by
    intro e he
    exact (H.induce_uniform hunif R.survivors) e (hF he)
  have hdef := K.degreeDeficit_add_edges hKunif hcap
  have hmul : r * R.nextBase.edges.card ≤
      r * F.card + r * R.nextBase.degreeExcess D' := by
    simpa [Nat.mul_add] using Nat.mul_le_mul_left r hcount
  refine ⟨K, ?_, ?_, hKunif, hcap, ?_, ?_, ?_⟩
  · simp [K]
  · simpa [K] using hF
  · intro u v
    exact (R.nextBase.restrictEdges_codegree_le F hF u v).trans
      (H.induce_codegree_le R.survivors u v)
  · have hvertices : K.vertices = R.survivors := by simp [K]
    have hedges : K.edges = F := rfl
    rw [hvertices, hedges] at hdef
    omega
  · rfl
end Union

end MatchingRound

namespace MatchingRound

section Probability

variable [Fintype V] [Fintype E] [DecidableEq E]

/-- One-round mark rate; inactive ambient labels receive rate zero. -/
noncomputable def rate (H : IndexedHypergraph V E) (a : ℝ) (D : ℕ) :
    E ⊕ V → ℝ
  | Sum.inl e => if e ∈ H.edges then a / (D : ℝ) else 0
  | Sum.inr v =>
      if v ∈ H.vertices then a * (1 - (H.degree v : ℝ) / (D : ℝ)) else 0

omit [Fintype V] [Fintype E] in
theorem rate_nonneg (H : IndexedHypergraph V E)
    {a : ℝ} (ha : 0 ≤ a) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (i : E ⊕ V) : 0 ≤ rate H a D i := by
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  cases i with
  | inl e =>
      by_cases he : e ∈ H.edges
      · simp only [rate, if_pos he]
        exact div_nonneg ha hDr.le
      · simp [rate, he]
  | inr v =>
      by_cases hv : v ∈ H.vertices
      · have hdeg : (H.degree v : ℝ) ≤ (D : ℝ) := by
          exact_mod_cast hcap v hv
        have hratio : (H.degree v : ℝ) / (D : ℝ) ≤ 1 :=
          (div_le_iff₀ hDr).mpr (by simpa using hdeg)
        simp only [rate, if_pos hv]
        exact mul_nonneg ha (sub_nonneg.mpr hratio)
      · simp [rate, hv]

omit [Fintype V] [Fintype E] in
theorem markProbability_bounds (H : IndexedHypergraph V E)
    {a : ℝ} (ha : 0 ≤ a) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (i : E ⊕ V) :
    0 ≤ FiniteBernoulli.expMarkProbability (rate H a D) i ∧
      FiniteBernoulli.expMarkProbability (rate H a D) i ≤ 1 :=
  FiniteBernoulli.expMarkProbability_bounds _ (rate_nonneg H ha hD hcap) i
/-- Edge and private marks whose absence lets a vertex survive. -/
def vertexLabels (H : IndexedHypergraph V E) (v : V) : Finset (E ⊕ V) :=
  ((H.edges.filter (fun e => v ∈ H.edge e)).image Sum.inl) ∪ {Sum.inr v}

/-- Survival of a vertex in a single independent-mark round. -/
def vertexSurvives (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) (v : V) : Prop :=
  ω (Sum.inr v) = false ∧
    ∀ e ∈ H.edges, v ∈ H.edge e → ω (Sum.inl e) = false

omit [Fintype V] [Fintype E] in
theorem vertexSurvives_iff_all_false (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) (v : V) :
    vertexSurvives H ω v ↔ ∀ i ∈ vertexLabels H v, ω i = false := by
  classical
  constructor
  · intro h i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨e, heinc, rfl⟩ := Finset.mem_image.mp hi
      exact h.2 e (Finset.mem_filter.mp heinc).1 (Finset.mem_filter.mp heinc).2
    · have hi' : i = Sum.inr v := Finset.mem_singleton.mp hi
      simpa [hi'] using h.1
  · intro h
    constructor
    · exact h (Sum.inr v) (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _)))
    · intro e he hve
      apply h (Sum.inl e)
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_image.mpr
        ⟨e, Finset.mem_filter.mpr ⟨he, hve⟩, rfl⟩

omit [Fintype V] [Fintype E] in
theorem sum_vertexLabels_rate (H : IndexedHypergraph V E)
    (a : ℝ) {D : ℕ} (hD : 0 < D)
    {v : V} (hv : v ∈ H.vertices) :
    (vertexLabels H v).sum (rate H a D) = a := by
  classical
  have hdisj :
      Disjoint ((H.edges.filter (fun e => v ∈ H.edge e)).image Sum.inl)
        ({Sum.inr v} : Finset (E ⊕ V)) := by
    apply Finset.disjoint_singleton_right.mpr
    intro h
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp h
    cases heq
  unfold vertexLabels
  rw [Finset.sum_union hdisj,
    Finset.sum_image (by intro e he f hf h; exact Sum.inl_injective h),
    Finset.sum_singleton]
  have hedge :
      (H.edges.filter (fun e => v ∈ H.edge e)).sum
        (fun e => rate H a D (Sum.inl e)) =
      (H.degree v : ℝ) * (a / (D : ℝ)) := by
    calc
      (H.edges.filter (fun e => v ∈ H.edge e)).sum
          (fun e => rate H a D (Sum.inl e)) =
        (H.edges.filter (fun e => v ∈ H.edge e)).sum
          (fun _ => a / (D : ℝ)) := by
            apply Finset.sum_congr rfl
            intro e he
            simp [rate, (Finset.mem_filter.mp he).1]
      _ = (H.degree v : ℝ) * (a / (D : ℝ)) := by
            simp [IndexedHypergraph.degree, nsmul_eq_mul]
  rw [hedge]
  simp only [rate, if_pos hv]
  have hDc : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  field_simp
  ring
theorem prob_vertexSurvives (H : IndexedHypergraph V E)
    (a : ℝ) {D : ℕ} (hD : 0 < D)
    {v : V} (hv : v ∈ H.vertices) :
    FiniteBernoulli.prob
        (FiniteBernoulli.expMarkProbability (rate H a D))
        {ω | vertexSurvives H ω v} = Real.exp (-a) := by
  have hset :
      {ω | vertexSurvives H ω v} =
        {ω | ∀ i ∈ vertexLabels H v, ω i = false} := by
    ext ω
    exact vertexSurvives_iff_all_false H ω v
  rw [hset, FiniteBernoulli.prob_all_false_exp,
    sum_vertexLabels_rate H a hD hv]

/-- Real-valued count of surviving active vertices. -/
noncomputable def survivorCount (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) : ℝ :=
  H.vertices.sum (fun v =>
    FiniteBernoulli.eventIndicator {ω | vertexSurvives H ω v} ω)

/-- The actual surviving active vertex set. -/
noncomputable def survivingVertices (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) : Finset V := by
  classical
  exact H.vertices.filter (vertexSurvives H ω)

/-- A marked copy accepted only when no other marked copy meets it. -/
def isolatedMarked (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) (e : E) : Prop :=
  ω (Sum.inl e) = true ∧
    ∀ f ∈ H.edges, f ≠ e → ω (Sum.inl f) = true →
      Disjoint (H.edge e) (H.edge f)

noncomputable def acceptedEdges (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) : Finset E := by
  classical
  exact H.edges.filter (isolatedMarked H ω)

omit [DecidableEq V] [Fintype V] [Fintype E] [DecidableEq E] in
theorem acceptedEdges_matching (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) :
    H.IsMatching (acceptedEdges H ω) := by
  classical
  constructor
  · exact Finset.filter_subset _ _
  · intro e he f hf hne
    have he' : e ∈ H.edges.filter (isolatedMarked H ω) := by
      simpa [acceptedEdges] using he
    have hf' : f ∈ H.edges.filter (isolatedMarked H ω) := by
      simpa [acceptedEdges] using hf
    exact (Finset.mem_filter.mp he').2.2 f
      (Finset.mem_filter.mp hf').1 hne.symm
      (Finset.mem_filter.mp hf').2.1

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem surviving_disjoint_accepted (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) :
    Disjoint (survivingVertices H ω) (H.covered (acceptedEdges H ω)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hvc
  have hv' : v ∈ H.vertices.filter (vertexSurvives H ω) := by
    simpa [survivingVertices] using hv
  have hsurvive := (Finset.mem_filter.mp hv').2
  obtain ⟨e, heacc, hve⟩ := Finset.mem_biUnion.mp hvc
  have he' : e ∈ H.edges.filter (isolatedMarked H ω) := by
    simpa [acceptedEdges] using heacc
  have heH := (Finset.mem_filter.mp he').1
  have hemark := (Finset.mem_filter.mp he').2.1
  have hfalse := hsurvive.2 e heH hve
  simp [hemark] at hfalse

/-- Every marking configuration supplies valid deterministic round data. -/
noncomputable def sampledRound (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) : MatchingRound H where
  survivors := survivingVertices H ω
  survivors_subset := by
    classical
    exact Finset.filter_subset _ _
  accepted := acceptedEdges H ω
  accepted_matching := acceptedEdges_matching H ω
  survivors_disjoint_accepted := surviving_disjoint_accepted H ω
omit [DecidableEq V] [Fintype V] [Fintype E] [DecidableEq E] in
theorem survivorCount_eq_card (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) :
    survivorCount H ω = (survivingVertices H ω).card := by
  classical
  simp only [survivorCount, survivingVertices, FiniteBernoulli.eventIndicator]
  rw [Finset.card_filter]
  norm_cast
/-- Every active vertex survives with the same probability exp(-a). -/
theorem expect_survivorCount (H : IndexedHypergraph V E)
    (a : ℝ) {D : ℕ} (hD : 0 < D) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (survivorCount H) =
        (H.vertices.card : ℝ) * Real.exp (-a) := by
  classical
  unfold survivorCount
  rw [FiniteBernoulli.expect_sum]
  calc
    H.vertices.sum (fun v =>
        FiniteBernoulli.expect
          (FiniteBernoulli.expMarkProbability (rate H a D))
          (fun ω => FiniteBernoulli.eventIndicator
            {ω | vertexSurvives H ω v} ω)) =
      H.vertices.sum (fun _ => Real.exp (-a)) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [FiniteBernoulli.expect_eventIndicator]
        exact prob_vertexSurvives H a hD hv
    _ = (H.vertices.card : ℝ) * Real.exp (-a) := by simp
/-- Vertices with a positive private mark. -/
noncomputable def privateMarkedVertices (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) : Finset V := by
  classical
  exact H.vertices.filter (fun v => ω (Sum.inr v) = true)

/-- Marked copies that meet a second marked copy. -/
noncomputable def collidingFirstEdges (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) : Finset E := by
  classical
  exact H.edges.filter (fun e =>
    ω (Sum.inl e) = true ∧
      ∃ f ∈ H.edges, f ≠ e ∧ ω (Sum.inl f) = true ∧
        ¬Disjoint (H.edge e) (H.edge f))

/-- Active edge copies other than e meeting e. -/
noncomputable def intersectingNeighbors (H : IndexedHypergraph V E)
    (e : E) : Finset E := by
  classical
  exact H.edges.filter (fun f => f ≠ e ∧ ¬Disjoint (H.edge e) (H.edge f))

omit [Fintype V] [Fintype E] in
theorem card_intersectingNeighbors_le (H : IndexedHypergraph V E)
    {r D : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {e : E} (he : e ∈ H.edges) :
    (intersectingNeighbors H e).card ≤ r * D := by
  classical
  let U : Finset E :=
    (H.edge e).biUnion (fun v => H.edges.filter (fun f => v ∈ H.edge f))
  have hsub : intersectingNeighbors H e ⊆ U := by
    intro f hf
    have hf' : f ∈ H.edges.filter
        (fun f => f ≠ e ∧ ¬Disjoint (H.edge e) (H.edge f)) := by
      simpa [intersectingNeighbors] using hf
    obtain ⟨hfH, hfe, hinter⟩ := Finset.mem_filter.mp hf'
    obtain ⟨v, hve, hvf⟩ := Finset.not_disjoint_iff.mp hinter
    exact Finset.mem_biUnion.mpr
      ⟨v, hve, Finset.mem_filter.mpr ⟨hfH, hvf⟩⟩
  calc
    (intersectingNeighbors H e).card ≤ U.card := Finset.card_le_card hsub
    _ ≤ (H.edge e).sum H.degree := by
      simpa [U, IndexedHypergraph.degree] using
        (Finset.card_biUnion_le
          (s := H.edge e)
          (t := fun v => H.edges.filter (fun f => v ∈ H.edge f)))
    _ ≤ (H.edge e).sum (fun _ => D) := by
      apply Finset.sum_le_sum
      intro v hv
      exact hcap v (H.edge_subset e he hv)
    _ = r * D := by simp [hunif e he]
/-- Ordered distinct pairs of active copies that intersect. -/
noncomputable def intersectingPairs (H : IndexedHypergraph V E) : Finset (E × E) := by
  classical
  exact (H.edges.product H.edges).filter (fun p =>
    p.1 ≠ p.2 ∧ ¬Disjoint (H.edge p.1) (H.edge p.2))

omit [Fintype V] [Fintype E] in
theorem card_intersectingPairs_le (H : IndexedHypergraph V E)
    {r D : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D) :
    (intersectingPairs H).card ≤ H.edges.card * (r * D) := by
  classical
  have hfirst : Set.MapsTo Prod.fst
      (intersectingPairs H : Set (E × E)) (H.edges : Set E) := by
    intro p hp
    have hp' : p ∈ (H.edges.product H.edges).filter
        (fun p => p.1 ≠ p.2 ∧ ¬Disjoint (H.edge p.1) (H.edge p.2)) := by
      simpa [intersectingPairs] using hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp').1).1
  have hfiber (e : E) (he : e ∈ H.edges) :
      ((intersectingPairs H).filter (fun p => p.1 = e)).card ≤ r * D := by
    have hmap : Set.MapsTo Prod.snd
        (((intersectingPairs H).filter (fun p => p.1 = e)) : Set (E × E))
        (intersectingNeighbors H e : Set E) := by
      intro p hp
      obtain ⟨hpbase, hpeq⟩ := Finset.mem_filter.mp hp
      have hp' : p ∈ (H.edges.product H.edges).filter
          (fun p => p.1 ≠ p.2 ∧ ¬Disjoint (H.edge p.1) (H.edge p.2)) := by
        simpa [intersectingPairs] using hpbase
      obtain ⟨hprod, hne, hinter⟩ := Finset.mem_filter.mp hp'
      have hsecond := (Finset.mem_product.mp hprod).2
      have hmem : p.2 ∈ H.edges.filter
          (fun f => f ≠ e ∧ ¬Disjoint (H.edge e) (H.edge f)) := by
        apply Finset.mem_filter.mpr
        constructor
        · exact hsecond
        · constructor
          · intro h2
            exact hne (hpeq.trans h2.symm)
          · simpa [hpeq] using hinter
      simpa [intersectingNeighbors] using hmem
    have hinj : Set.InjOn Prod.snd
        (((intersectingPairs H).filter (fun p => p.1 = e)) : Set (E × E)) := by
      intro p hp q hq hsec
      have hpfirst := (Finset.mem_filter.mp hp).2
      have hqfirst := (Finset.mem_filter.mp hq).2
      exact Prod.ext (hpfirst.trans hqfirst.symm) hsec
    exact (Finset.card_le_card_of_injOn Prod.snd hmap hinj).trans
      (card_intersectingNeighbors_le H hunif hcap he)
  calc
    (intersectingPairs H).card =
        H.edges.sum (fun e =>
          ((intersectingPairs H).filter (fun p => p.1 = e)).card) :=
      Finset.card_eq_sum_card_fiberwise hfirst
    _ ≤ H.edges.sum (fun _ => r * D) :=
      Finset.sum_le_sum hfiber
    _ = H.edges.card * (r * D) := by simp
/-- Intersecting ordered pairs whose two copies are marked. -/
noncomputable def markedPairs (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) : Finset (E × E) := by
  classical
  exact (intersectingPairs H).filter (fun p =>
    ω (Sum.inl p.1) = true ∧ ω (Sum.inl p.2) = true)

omit [Fintype V] [Fintype E] in
theorem collidingFirstEdges_eq_image_markedPairs
    (H : IndexedHypergraph V E) (ω : E ⊕ V → Bool) :
    collidingFirstEdges H ω = (markedPairs H ω).image Prod.fst := by
  classical
  ext e
  constructor
  · intro he
    have he' : e ∈ H.edges.filter (fun e =>
        ω (Sum.inl e) = true ∧
          ∃ f ∈ H.edges, f ≠ e ∧ ω (Sum.inl f) = true ∧
            ¬Disjoint (H.edge e) (H.edge f)) := by
      simpa [collidingFirstEdges] using he
    obtain ⟨heH, hemark, f, hfH, hfe, hfmark, hinter⟩ :=
      Finset.mem_filter.mp he'
    apply Finset.mem_image.mpr
    refine ⟨(e, f), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨heH, hfH⟩, hfe.symm, hinter⟩
    · exact ⟨hemark, hfmark⟩
  · intro he
    obtain ⟨p, hp, hpfirst⟩ := Finset.mem_image.mp he
    rcases p with ⟨e', f⟩
    change e' = e at hpfirst
    subst e'
    have hp' : (e, f) ∈ (intersectingPairs H).filter
        (fun p => ω (Sum.inl p.1) = true ∧ ω (Sum.inl p.2) = true) := by
      simpa [markedPairs] using hp
    obtain ⟨hpbase, hemark, hfmark⟩ := Finset.mem_filter.mp hp'
    have hpbase' : (e, f) ∈
        (H.edges.product H.edges).filter
          (fun p => p.1 ≠ p.2 ∧ ¬Disjoint (H.edge p.1) (H.edge p.2)) := by
      simpa [intersectingPairs] using hpbase
    obtain ⟨hprod, hne, hinter⟩ := Finset.mem_filter.mp hpbase'
    obtain ⟨heH, hfH⟩ := Finset.mem_product.mp hprod
    have he' : e ∈ H.edges.filter (fun e =>
        ω (Sum.inl e) = true ∧
          ∃ f ∈ H.edges, f ≠ e ∧ ω (Sum.inl f) = true ∧
            ¬Disjoint (H.edge e) (H.edge f)) :=
      Finset.mem_filter.mpr ⟨heH, hemark, f, hfH, hne.symm, hfmark, hinter⟩
    simpa [collidingFirstEdges] using he'

omit [Fintype V] [Fintype E] in
theorem card_collidingFirstEdges_le_markedPairs
    (H : IndexedHypergraph V E) (ω : E ⊕ V → Bool) :
    (collidingFirstEdges H ω).card ≤ (markedPairs H ω).card := by
  rw [collidingFirstEdges_eq_image_markedPairs]
  exact Finset.card_image_le
/-- Real indicator sum for marked intersecting ordered pairs. -/
noncomputable def markedPairCount (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) : ℝ :=
  (intersectingPairs H).sum (fun p =>
    FiniteBernoulli.eventIndicator
      {ω | ω (Sum.inl p.1) = true ∧ ω (Sum.inl p.2) = true} ω)

omit [Fintype V] [Fintype E] in
theorem markedPairCount_eq_card (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) :
    markedPairCount H ω = ((markedPairs H ω).card : ℝ) := by
  classical
  simp only [markedPairCount, markedPairs, FiniteBernoulli.eventIndicator]
  rw [Finset.card_filter]
  norm_cast

theorem expect_markedPairCount (H : IndexedHypergraph V E)
    (a : ℝ) (D : ℕ) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (markedPairCount H) =
    (intersectingPairs H).sum (fun p =>
      FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inl p.1) *
      FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inl p.2)) := by
  classical
  unfold markedPairCount
  rw [FiniteBernoulli.expect_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [FiniteBernoulli.expect_eventIndicator]
  have hp' : p ∈ (H.edges.product H.edges).filter
      (fun p => p.1 ≠ p.2 ∧ ¬Disjoint (H.edge p.1) (H.edge p.2)) := by
    simpa [intersectingPairs] using hp
  have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp').2.1
  exact FiniteBernoulli.prob_two_true _
    (by intro h; exact hne (Sum.inl_injective h))
omit [Fintype V] [Fintype E] in
theorem markProbability_le_rate (H : IndexedHypergraph V E)
    (a : ℝ) (D : ℕ) (i : E ⊕ V) :
    FiniteBernoulli.expMarkProbability (rate H a D) i ≤
      rate H a D i := by
  unfold FiniteBernoulli.expMarkProbability
  have h := Real.add_one_le_exp (-(rate H a D i))
  linarith

theorem expect_markedPairCount_le (H : IndexedHypergraph V E)
    {a : ℝ} (ha : 0 ≤ a) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (markedPairCount H) ≤
        (intersectingPairs H).card * (a / (D : ℝ)) ^ 2 := by
  classical
  rw [expect_markedPairCount]
  have hDr : 0 ≤ (D : ℝ) := by exact_mod_cast (Nat.zero_le D)
  have hdiv : 0 ≤ a / (D : ℝ) := div_nonneg ha hDr
  calc
    (intersectingPairs H).sum (fun p =>
        FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inl p.1) *
        FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inl p.2)) ≤
      (intersectingPairs H).sum (fun _ => (a / (D : ℝ)) ^ 2) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' : p ∈ (H.edges.product H.edges).filter
            (fun p => p.1 ≠ p.2 ∧ ¬Disjoint (H.edge p.1) (H.edge p.2)) := by
          simpa [intersectingPairs] using hp
        obtain ⟨he, hf⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp').1
        have hpe : 0 ≤
            FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inl p.1) :=
          (markProbability_bounds H ha hD hcap (Sum.inl p.1)).1
        have hpf : 0 ≤
            FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inl p.2) :=
          (markProbability_bounds H ha hD hcap (Sum.inl p.2)).1
        have hbe :
            FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inl p.1) ≤
              a / (D : ℝ) := by
          simpa [rate, he] using markProbability_le_rate H a D (Sum.inl p.1)
        have hbf :
            FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inl p.2) ≤
              a / (D : ℝ) := by
          simpa [rate, hf] using markProbability_le_rate H a D (Sum.inl p.2)
        calc
          FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inl p.1) *
              FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inl p.2) ≤
            (a / (D : ℝ)) *
              FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inl p.2) :=
            mul_le_mul_of_nonneg_right hbe hpf
          _ ≤ (a / (D : ℝ)) * (a / (D : ℝ)) :=
            mul_le_mul_of_nonneg_left hbf hdiv
          _ = (a / (D : ℝ)) ^ 2 := by ring
    _ = (intersectingPairs H).card * (a / (D : ℝ)) ^ 2 := by
      simp [nsmul_eq_mul]
theorem expect_markedPairCount_le_global (H : IndexedHypergraph V E)
    {r D : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (markedPairCount H) ≤
        ((H.edges.card : ℝ) * ((r : ℝ) * (D : ℝ))) *
          (a / (D : ℝ)) ^ 2 := by
  have hpair :
      ((intersectingPairs H).card : ℝ) ≤
        (H.edges.card : ℝ) * ((r : ℝ) * (D : ℝ)) := by
    exact_mod_cast card_intersectingPairs_le H hunif hcap
  calc
    FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (markedPairCount H) ≤
      ((intersectingPairs H).card : ℝ) * (a / (D : ℝ)) ^ 2 :=
      expect_markedPairCount_le H ha hD hcap
    _ ≤ ((H.edges.card : ℝ) * ((r : ℝ) * (D : ℝ))) *
        (a / (D : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hpair (sq_nonneg _)
omit [Fintype V] [Fintype E] in
/-- A wasted vertex has a private mark or lies on a colliding marked edge. -/
theorem waste_subset_private_union_colliding (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) :
    (sampledRound H ω).waste ⊆
      privateMarkedVertices H ω ∪ H.covered (collidingFirstEdges H ω) := by
  classical
  intro v hvw
  have hvH : v ∈ H.vertices := (Finset.mem_sdiff.mp hvw).1
  have hvnot : v ∉ (sampledRound H ω).survivors ∪
      H.covered (sampledRound H ω).accepted :=
    (Finset.mem_sdiff.mp hvw).2
  have hvnotU : v ∉ survivingVertices H ω := by
    intro hv
    exact hvnot (Finset.mem_union.mpr (Or.inl hv))
  have hvnotC : v ∉ H.covered (acceptedEdges H ω) := by
    intro hv
    exact hvnot (Finset.mem_union.mpr (Or.inr hv))
  by_cases hp : ω (Sum.inr v) = true
  · apply Finset.mem_union.mpr
    left
    have hvpriv : v ∈ H.vertices.filter (fun x => ω (Sum.inr x) = true) :=
      Finset.mem_filter.mpr ⟨hvH, hp⟩
    simpa [privateMarkedVertices] using hvpriv
  · apply Finset.mem_union.mpr
    right
    have hprivate : ω (Sum.inr v) = false := by
      cases h : ω (Sum.inr v) <;> simp_all
    have hnotSurvive : ¬ vertexSurvives H ω v := by
      intro hs
      apply hvnotU
      exact Finset.mem_filter.mpr ⟨hvH, hs⟩
    have hmarked :
        ∃ e ∈ H.edges, v ∈ H.edge e ∧ ω (Sum.inl e) = true := by
      by_contra hn
      apply hnotSurvive
      constructor
      · exact hprivate
      · intro e he hve
        cases heω : ω (Sum.inl e)
        · rfl
        · exact False.elim (hn ⟨e, he, hve, heω⟩)
    obtain ⟨e, he, hve, hemark⟩ := hmarked
    have hnotAccepted : e ∉ acceptedEdges H ω := by
      intro heacc
      exact hvnotC (Finset.mem_biUnion.mpr ⟨e, heacc, hve⟩)
    have hnotIsolated :
        ¬ ∀ f ∈ H.edges, f ≠ e → ω (Sum.inl f) = true →
          Disjoint (H.edge e) (H.edge f) := by
      intro hiso
      apply hnotAccepted
      apply Finset.mem_filter.mpr
      exact ⟨he, hemark, hiso⟩
    push Not at hnotIsolated
    obtain ⟨f, hf, hfe, hfmark, hinter⟩ := hnotIsolated
    apply Finset.mem_biUnion.mpr
    refine ⟨e, ?_, hve⟩
    apply Finset.mem_filter.mpr
    exact ⟨he, hemark, f, hf, hfe, hfmark, hinter⟩
omit [Fintype V] [Fintype E] in
theorem waste_card_le_private_add_colliding (H : IndexedHypergraph V E)
    {r : ℕ} (hunif : H.IsUniform r) (ω : E ⊕ V → Bool) :
    (sampledRound H ω).waste.card ≤
      (privateMarkedVertices H ω).card +
        r * (collidingFirstEdges H ω).card := by
  classical
  have hsub := waste_subset_private_union_colliding H ω
  have hfirst : collidingFirstEdges H ω ⊆ H.edges := by
    unfold collidingFirstEdges
    exact Finset.filter_subset _ _
  have hcover :
      (H.covered (collidingFirstEdges H ω)).card ≤
        r * (collidingFirstEdges H ω).card := by
    calc
      (H.covered (collidingFirstEdges H ω)).card ≤
          (collidingFirstEdges H ω).sum (fun e => (H.edge e).card) :=
        Finset.card_biUnion_le
      _ = (collidingFirstEdges H ω).sum (fun _ => r) := by
        apply Finset.sum_congr rfl
        intro e he
        exact hunif e (hfirst he)
      _ = r * (collidingFirstEdges H ω).card := by simp [mul_comm]
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le
    (privateMarkedVertices H ω) (H.covered (collidingFirstEdges H ω))
  omega
omit [Fintype V] [Fintype E] in
theorem waste_card_le_private_add_pairs (H : IndexedHypergraph V E)
    {r : ℕ} (hunif : H.IsUniform r) (ω : E ⊕ V → Bool) :
    (sampledRound H ω).waste.card ≤
      (privateMarkedVertices H ω).card + r * (markedPairs H ω).card := by
  have h₁ := waste_card_le_private_add_colliding H hunif ω
  have h₂ := card_collidingFirstEdges_le_markedPairs H ω
  have hmul := Nat.mul_le_mul_left r h₂
  omega
/-- Expected actual number of surviving vertices in one round. -/
theorem expect_survivingVertices_card (H : IndexedHypergraph V E)
    (a : ℝ) {D : ℕ} (hD : 0 < D) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω => ((survivingVertices H ω).card : ℝ)) =
        (H.vertices.card : ℝ) * Real.exp (-a) := by
  calc
    FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (fun ω => ((survivingVertices H ω).card : ℝ)) =
      FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (survivorCount H) := by
          congr 1
          funext ω
          exact (survivorCount_eq_card H ω).symm
    _ = (H.vertices.card : ℝ) * Real.exp (-a) :=
      expect_survivorCount H a hD

/-- Count private positive marks on active vertices. -/
noncomputable def privateMarkCount (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) : ℝ :=
  H.vertices.sum (fun v => if ω (Sum.inr v) then 1 else 0)

omit [DecidableEq V] [Fintype V] [Fintype E] [DecidableEq E] in
theorem privateMarkCount_eq_card (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) :
    privateMarkCount H ω = ((privateMarkedVertices H ω).card : ℝ) := by
  classical
  simp only [privateMarkCount, privateMarkedVertices]
  rw [Finset.card_filter]
  norm_cast

theorem expect_privateMarkCount (H : IndexedHypergraph V E)
    (a : ℝ) (D : ℕ) :
    FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (privateMarkCount H) =
      H.vertices.sum (fun v =>
        FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inr v)) := by
  classical
  unfold privateMarkCount
  rw [FiniteBernoulli.expect_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact FiniteBernoulli.expect_mark _ (Sum.inr v)

omit [Fintype V] [Fintype E] in
theorem sum_privateRate_eq_deficit (H : IndexedHypergraph V E)
    (a : ℝ) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D) :
    H.vertices.sum (fun v => rate H a D (Sum.inr v)) =
      (a / (D : ℝ)) * (H.degreeDeficit D : ℝ) := by
  classical
  have hDc : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  calc
    H.vertices.sum (fun v => rate H a D (Sum.inr v)) =
        H.vertices.sum (fun v =>
          (a / (D : ℝ)) * ((D - H.degree v : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro v hv
      simp only [rate, if_pos hv, Nat.cast_sub (hcap v hv)]
      field_simp
    _ = (a / (D : ℝ)) *
        H.vertices.sum (fun v => ((D - H.degree v : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
    _ = (a / (D : ℝ)) * (H.degreeDeficit D : ℝ) := by
      simp [IndexedHypergraph.degreeDeficit]

theorem expect_privateMarkCount_le (H : IndexedHypergraph V E)
    (a : ℝ) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D) :
    FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (privateMarkCount H) ≤
      (a / (D : ℝ)) * (H.degreeDeficit D : ℝ) := by
  rw [expect_privateMarkCount]
  calc
    H.vertices.sum (fun v =>
        FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inr v)) ≤
      H.vertices.sum (fun v => rate H a D (Sum.inr v)) :=
      Finset.sum_le_sum (fun v hv => markProbability_le_rate H a D (Sum.inr v))
    _ = (a / (D : ℝ)) * (H.degreeDeficit D : ℝ) :=
      sum_privateRate_eq_deficit H a hD hcap
private theorem expect_mono (p : E ⊕ V → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (X Y : (E ⊕ V → Bool) → ℝ)
    (hXY : ∀ ω, X ω ≤ Y ω) :
    FiniteBernoulli.expect p X ≤ FiniteBernoulli.expect p Y := by
  classical
  unfold FiniteBernoulli.expect
  apply Finset.sum_le_sum
  intro ω hω
  exact mul_le_mul_of_nonneg_left (hXY ω)
    (FiniteBernoulli.weight_nonneg p hp ω)

private theorem expect_add (p : E ⊕ V → ℝ)
    (X Y : (E ⊕ V → Bool) → ℝ) :
    FiniteBernoulli.expect p (fun ω => X ω + Y ω) =
      FiniteBernoulli.expect p X + FiniteBernoulli.expect p Y := by
  classical
  unfold FiniteBernoulli.expect
  simp only [mul_add, Finset.sum_add_distrib]

private theorem expect_mul_const (p : E ⊕ V → ℝ) (c : ℝ)
    (X : (E ⊕ V → Bool) → ℝ) :
    FiniteBernoulli.expect p (fun ω => c * X ω) =
      c * FiniteBernoulli.expect p X := by
  classical
  unfold FiniteBernoulli.expect
  calc
    (∑ ω, FiniteBernoulli.weight p ω * (c * X ω)) =
      ∑ ω, c * (FiniteBernoulli.weight p ω * X ω) := by
        apply Finset.sum_congr rfl
        intro ω hω
        ring
    _ = c * ∑ ω, FiniteBernoulli.weight p ω * X ω := by
      rw [Finset.mul_sum]

private theorem expect_const (p : E ⊕ V → ℝ) (c : ℝ) :
    FiniteBernoulli.expect p (fun _ : E ⊕ V → Bool => c) = c := by
  classical
  unfold FiniteBernoulli.expect
  rw [← Finset.sum_mul]
  simp [FiniteBernoulli.sum_weight]

/-- A finite marking configuration has value no greater than its mean. -/
theorem exists_le_expect (p : E ⊕ V → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (X : (E ⊕ V → Bool) → ℝ) :
    ∃ ω, X ω ≤ FiniteBernoulli.expect p X := by
  classical
  obtain ⟨ω, _, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (E ⊕ V → Bool)) X
      Finset.univ_nonempty
  refine ⟨ω, ?_⟩
  have h := expect_mono p hp (fun _ => X ω) X
    (fun η => hmin η (Finset.mem_univ η))
  simpa only [expect_const] using h
/-- One-round expected waste, before simplifying the edge count by regularity. -/
theorem expect_waste_le (H : IndexedHypergraph V E)
    {r D : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω => (((sampledRound H ω).waste.card : ℝ))) ≤
        (a / (D : ℝ)) * (H.degreeDeficit D : ℝ) +
          (r : ℝ) *
            (((H.edges.card : ℝ) * ((r : ℝ) * (D : ℝ))) *
              (a / (D : ℝ)) ^ 2) := by
  let p := FiniteBernoulli.expMarkProbability (rate H a D)
  have hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1 :=
    markProbability_bounds H ha hD hcap
  have hpoint (ω : E ⊕ V → Bool) :
      (((sampledRound H ω).waste.card : ℝ)) ≤
        privateMarkCount H ω + (r : ℝ) * markedPairCount H ω := by
    rw [privateMarkCount_eq_card, markedPairCount_eq_card]
    exact_mod_cast waste_card_le_private_add_pairs H hunif ω
  calc
    FiniteBernoulli.expect p
        (fun ω => (((sampledRound H ω).waste.card : ℝ))) ≤
      FiniteBernoulli.expect p
        (fun ω => privateMarkCount H ω + (r : ℝ) * markedPairCount H ω) :=
      expect_mono p hp _ _ hpoint
    _ = FiniteBernoulli.expect p (privateMarkCount H) +
        (r : ℝ) * FiniteBernoulli.expect p (markedPairCount H) := by
      rw [expect_add, expect_mul_const]
    _ ≤ (a / (D : ℝ)) * (H.degreeDeficit D : ℝ) +
          (r : ℝ) *
            (((H.edges.card : ℝ) * ((r : ℝ) * (D : ℝ))) *
              (a / (D : ℝ)) ^ 2) := by
      apply add_le_add
      · exact expect_privateMarkCount_le H a hD hcap
      · exact mul_le_mul_of_nonneg_left
          (expect_markedPairCount_le_global H hunif hcap ha hD)
          (by positivity)
/-- The collision term depends only on the number of active vertices. -/
theorem expect_waste_le_simplified (H : IndexedHypergraph V E)
    {r D : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω => (((sampledRound H ω).waste.card : ℝ))) ≤
        (a / (D : ℝ)) * (H.degreeDeficit D : ℝ) +
          (r : ℝ) * a ^ 2 * (H.vertices.card : ℝ) := by
  have hcountNat : r * H.edges.card ≤ H.vertices.card * D := by
    have h := H.degreeDeficit_add_edges hunif hcap
    omega
  have hcount :
      (r : ℝ) * (H.edges.card : ℝ) ≤
        (H.vertices.card : ℝ) * (D : ℝ) := by
    exact_mod_cast hcountNat
  have hr : 0 ≤ (r : ℝ) := by positivity
  have hDr : 0 ≤ (D : ℝ) := by positivity
  have hmult : 0 ≤
      ((r : ℝ) * (D : ℝ)) * (a / (D : ℝ)) ^ 2 :=
    mul_nonneg (mul_nonneg hr hDr) (sq_nonneg _)
  have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  calc
    FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (fun ω => (((sampledRound H ω).waste.card : ℝ))) ≤
      (a / (D : ℝ)) * (H.degreeDeficit D : ℝ) +
        (r : ℝ) *
          (((H.edges.card : ℝ) * ((r : ℝ) * (D : ℝ))) *
            (a / (D : ℝ)) ^ 2) :=
      expect_waste_le H hunif hcap ha hD
    _ = (a / (D : ℝ)) * (H.degreeDeficit D : ℝ) +
        ((r : ℝ) * (H.edges.card : ℝ)) *
          (((r : ℝ) * (D : ℝ)) * (a / (D : ℝ)) ^ 2) := by ring
    _ ≤ (a / (D : ℝ)) * (H.degreeDeficit D : ℝ) +
        ((H.vertices.card : ℝ) * (D : ℝ)) *
          (((r : ℝ) * (D : ℝ)) * (a / (D : ℝ)) ^ 2) := by
      exact add_le_add_right (mul_le_mul_of_nonneg_right hcount hmult) _
    _ = (a / (D : ℝ)) * (H.degreeDeficit D : ℝ) +
          (r : ℝ) * a ^ 2 * (H.vertices.card : ℝ) := by
      field_simp
/-- Labels whose simultaneous absence makes a vertex set survive. -/
def setLabels (H : IndexedHypergraph V E) (U : Finset V) :
    Finset (E ⊕ V) :=
  U.biUnion (vertexLabels H)

def setSurvives (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) (U : Finset V) : Prop :=
  ∀ v ∈ U, vertexSurvives H ω v

omit [Fintype V] [Fintype E] in
theorem setSurvives_iff_all_false (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) (U : Finset V) :
    setSurvives H ω U ↔ ∀ i ∈ setLabels H U, ω i = false := by
  classical
  simp only [setSurvives, setLabels, Finset.mem_biUnion]
  constructor
  · intro hs i hi
    obtain ⟨v, hv, hiv⟩ := hi
    exact (vertexSurvives_iff_all_false H ω v).mp (hs v hv) i hiv
  · intro hs v hv
    apply (vertexSurvives_iff_all_false H ω v).mpr
    intro i hi
    exact hs i ⟨v, hv, hi⟩

theorem prob_setSurvives (H : IndexedHypergraph V E)
    (a : ℝ) (D : ℕ) (U : Finset V) :
    FiniteBernoulli.prob
      (FiniteBernoulli.expMarkProbability (rate H a D))
      {ω | setSurvives H ω U} =
        Real.exp (-(setLabels H U).sum (rate H a D)) := by
  have hset :
      {ω | setSurvives H ω U} =
        {ω | ∀ i ∈ setLabels H U, ω i = false} := by
    ext ω
    exact setSurvives_iff_all_false H ω U
  rw [hset, FiniteBernoulli.prob_all_false_exp]

private theorem sum_biUnion_le {κ ι : Type*} [DecidableEq ι]
    (s : Finset κ) (t : κ → Finset ι) (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    (s.biUnion t).sum f ≤ s.sum (fun j => (t j).sum f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
      have hinter : 0 ≤ ((t j) ∩ s.biUnion t).sum f :=
        Finset.sum_nonneg (fun i hi => hf i)
      have hunion := Finset.sum_union_inter
        (s₁ := t j) (s₂ := s.biUnion t) (f := f)
      simp only [Finset.biUnion_insert, Finset.sum_insert hj]
      calc
        (t j ∪ s.biUnion t).sum f ≤
            (t j).sum f + (s.biUnion t).sum f := by linarith
        _ ≤ (t j).sum f + s.sum (fun x => (t x).sum f) :=
          add_le_add_right ih _

omit [Fintype V] [Fintype E] in
theorem sum_setLabels_rate_le (H : IndexedHypergraph V E)
    {a : ℝ} (ha : 0 ≤ a) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {U : Finset V} (hU : U ⊆ H.vertices) :
    (setLabels H U).sum (rate H a D) ≤ (U.card : ℝ) * a := by
  classical
  calc
    (setLabels H U).sum (rate H a D) ≤
      U.sum (fun v => (vertexLabels H v).sum (rate H a D)) :=
      sum_biUnion_le U (vertexLabels H) (rate H a D)
        (rate_nonneg H ha hD hcap)
    _ = U.sum (fun _ => a) := by
      apply Finset.sum_congr rfl
      intro v hv
      exact sum_vertexLabels_rate H a hD (hU hv)
    _ = (U.card : ℝ) * a := by simp

/-- Positive association of no-mark events yields an edge-set survival lower bound. -/
theorem prob_setSurvives_ge (H : IndexedHypergraph V E)
    {a : ℝ} (ha : 0 ≤ a) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {U : Finset V} (hU : U ⊆ H.vertices) :
    Real.exp (-((U.card : ℝ) * a)) ≤
      FiniteBernoulli.prob
        (FiniteBernoulli.expMarkProbability (rate H a D))
        {ω | setSurvives H ω U} := by
  rw [prob_setSurvives]
  exact Real.exp_le_exp.mpr
    (neg_le_neg (sum_setLabels_rate_le H ha hD hcap hU))
/-- Count the active edge copies whose vertices all survive. -/
noncomputable def inducedEdgeCount (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) : ℝ :=
  H.edges.sum (fun e =>
    FiniteBernoulli.eventIndicator
      {ω | setSurvives H ω (H.edge e)} ω)

omit [Fintype V] [Fintype E] in
omit [DecidableEq V] [DecidableEq E] in
theorem edge_subset_survivors_iff (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) {e : E} (he : e ∈ H.edges) :
    H.edge e ⊆ survivingVertices H ω ↔
      setSurvives H ω (H.edge e) := by
  classical
  constructor
  · intro hs v hv
    exact (Finset.mem_filter.mp (hs hv)).2
  · intro hs v hv
    exact Finset.mem_filter.mpr
      ⟨H.edge_subset e he hv, hs v hv⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem inducedEdgeCount_eq_card (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) :
    inducedEdgeCount H ω =
      (((H.induce (survivingVertices H ω)).edges.card : ℝ)) := by
  classical
  simp only [inducedEdgeCount, FiniteBernoulli.eventIndicator,
    IndexedHypergraph.induce_edges]
  rw [Finset.card_filter]
  norm_cast
  apply Finset.sum_congr rfl
  intro e he
  simp only [Set.mem_setOf_eq, ← edge_subset_survivors_iff H ω he]

theorem expect_inducedEdgeCount_ge (H : IndexedHypergraph V E)
    {r D : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D) :
    (H.edges.card : ℝ) * Real.exp (-((r : ℝ) * a)) ≤
      FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (inducedEdgeCount H) := by
  classical
  unfold inducedEdgeCount
  rw [FiniteBernoulli.expect_sum]
  calc
    (H.edges.card : ℝ) * Real.exp (-((r : ℝ) * a)) =
      H.edges.sum (fun _ => Real.exp (-((r : ℝ) * a))) := by simp
    _ ≤ H.edges.sum (fun e =>
        FiniteBernoulli.expect
          (FiniteBernoulli.expMarkProbability (rate H a D))
          (fun ω => FiniteBernoulli.eventIndicator
            {ω | setSurvives H ω (H.edge e)} ω)) := by
      apply Finset.sum_le_sum
      intro e he
      rw [FiniteBernoulli.expect_eventIndicator]
      have hsub : H.edge e ⊆ H.vertices := H.edge_subset e he
      simpa [hunif e he] using
        (prob_setSurvives_ge H ha hD hcap hsub)
omit [Fintype V] [Fintype E] in
theorem vertexLabels_inter (H : IndexedHypergraph V E)
    {u v : V} (huv : u ≠ v) :
    vertexLabels H u ∩ vertexLabels H v =
      ((H.edges.filter (fun e => u ∈ H.edge e ∧ v ∈ H.edge e)).image
        Sum.inl) := by
  classical
  ext i
  cases i with
  | inl e =>
      simp only [vertexLabels, Finset.mem_inter, Finset.mem_union,
        Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨h₁, h₂⟩
        obtain ⟨e₁, he₁, heq₁⟩ := h₁.resolve_right (by simp)
        obtain ⟨e₂, he₂, heq₂⟩ := h₂.resolve_right (by simp)
        have h₁' : e₁ = e := Sum.inl_injective heq₁
        have h₂' : e₂ = e := Sum.inl_injective heq₂
        subst e₁
        subst e₂
        exact ⟨e, Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp he₁).1,
            (Finset.mem_filter.mp he₁).2, (Finset.mem_filter.mp he₂).2⟩, rfl⟩
      · rintro ⟨e', he', heq⟩
        have heq' : e' = e := Sum.inl_injective heq
        subst e'
        obtain ⟨he, hu, hv⟩ := Finset.mem_filter.mp he'
        constructor
        · left
          exact ⟨e, Finset.mem_filter.mpr ⟨he, hu⟩, rfl⟩
        · left
          exact ⟨e, Finset.mem_filter.mpr ⟨he, hv⟩, rfl⟩
  | inr w =>
      simp only [vertexLabels, Finset.mem_inter, Finset.mem_union,
        Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨h₁, h₂⟩
        have hwu : w = u := by
          rcases h₁ with h | h
          · obtain ⟨e, _, heq⟩ := h
            cases heq
          · exact Sum.inr_injective h
        have hwv : w = v := by
          rcases h₂ with h | h
          · obtain ⟨e, _, heq⟩ := h
            cases heq
          · exact Sum.inr_injective h
        exact False.elim (huv (hwu.symm.trans hwv))
      · rintro ⟨e, _, heq⟩
        cases heq

omit [Fintype V] [Fintype E] in
theorem sum_vertexLabels_inter_rate (H : IndexedHypergraph V E)
    (a : ℝ) (D : ℕ) {u v : V} (huv : u ≠ v) :
    (vertexLabels H u ∩ vertexLabels H v).sum (rate H a D) =
      (H.codegree u v : ℝ) * (a / (D : ℝ)) := by
  classical
  rw [vertexLabels_inter H huv]
  rw [Finset.sum_image (by
    intro e he f hf h
    exact Sum.inl_injective h)]
  calc
    (H.edges.filter (fun e => u ∈ H.edge e ∧ v ∈ H.edge e)).sum
        (fun e => rate H a D (Sum.inl e)) =
      (H.edges.filter (fun e => u ∈ H.edge e ∧ v ∈ H.edge e)).sum
        (fun _ => a / (D : ℝ)) := by
      apply Finset.sum_congr rfl
      intro e he
      simp [rate, (Finset.mem_filter.mp he).1]
    _ = (H.codegree u v : ℝ) * (a / (D : ℝ)) := by
      simp [IndexedHypergraph.codegree, nsmul_eq_mul]
omit [Fintype V] [Fintype E] in
theorem vertexLabels_inter_setLabels (H : IndexedHypergraph V E)
    (v : V) (U : Finset V) :
    vertexLabels H v ∩ setLabels H U =
      U.biUnion (fun u => vertexLabels H v ∩ vertexLabels H u) := by
  classical
  ext i
  simp only [setLabels, Finset.mem_inter, Finset.mem_biUnion]
  constructor
  · rintro ⟨hiv, u, hu, hiu⟩
    exact ⟨u, hu, hiv, hiu⟩
  · rintro ⟨u, hu, hiv, hiu⟩
    exact ⟨hiv, u, hu, hiu⟩

omit [Fintype V] [Fintype E] in
theorem sum_vertexLabels_inter_setLabels_le
    (H : IndexedHypergraph V E)
    {a : ℝ} (ha : 0 ≤ a) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ u ∈ H.vertices, H.degree u ≤ D)
    {B : ℕ} (hcodeg :
      ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, u ≠ v →
        H.codegree u v ≤ B)
    {v : V} (hv : v ∈ H.vertices)
    {U : Finset V} (hU : U ⊆ H.vertices) (hvU : v ∉ U) :
    (vertexLabels H v ∩ setLabels H U).sum (rate H a D) ≤
      (U.card : ℝ) * ((B : ℝ) * (a / (D : ℝ))) := by
  classical
  rw [vertexLabels_inter_setLabels H v U]
  calc
    (U.biUnion (fun u => vertexLabels H v ∩ vertexLabels H u)).sum
        (rate H a D) ≤
      U.sum (fun u =>
        (vertexLabels H v ∩ vertexLabels H u).sum (rate H a D)) :=
      sum_biUnion_le U _ _ (rate_nonneg H ha hD hcap)
    _ ≤ U.sum (fun _ => (B : ℝ) * (a / (D : ℝ))) := by
      apply Finset.sum_le_sum
      intro u hu
      have hne : v ≠ u := by
        intro h
        exact hvU (h ▸ hu)
      rw [sum_vertexLabels_inter_rate H a D hne]
      have hcodegR : (H.codegree v u : ℝ) ≤ (B : ℝ) := by
        exact_mod_cast hcodeg v hv u (hU hu) hne
      exact mul_le_mul_of_nonneg_right hcodegR
        (div_nonneg ha (by positivity))
    _ = (U.card : ℝ) * ((B : ℝ) * (a / (D : ℝ))) := by simp
omit [Fintype V] [Fintype E] in
/-- A bounded codegree limits the repeated labels in a joint survival event. -/
theorem sum_setLabels_rate_lower (H : IndexedHypergraph V E)
    {a : ℝ} (ha : 0 ≤ a) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {B : ℕ} (hcodeg :
      ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, u ≠ v →
        H.codegree u v ≤ B)
    (U : Finset V) (hU : U ⊆ H.vertices) :
    (U.card : ℝ) * a ≤
      (setLabels H U).sum (rate H a D) +
        (U.card : ℝ) ^ 2 * ((B : ℝ) * (a / (D : ℝ))) := by
  classical
  induction U using Finset.induction_on with
  | empty =>
      simp [setLabels]
  | @insert v U hvU ih =>
      have hv : v ∈ H.vertices := hU (Finset.mem_insert_self v U)
      have hU' : U ⊆ H.vertices := by
        intro u hu
        exact hU (Finset.mem_insert_of_mem hu)
      have hih := ih hU'
      have hinter :=
        sum_vertexLabels_inter_setLabels_le H ha hD hcap hcodeg hv hU' hvU
      have hunion := Finset.sum_union_inter
        (s₁ := vertexLabels H v) (s₂ := setLabels H U)
        (f := rate H a D)
      have hset :
          setLabels H (insert v U) =
            vertexLabels H v ∪ setLabels H U := by
        simp [setLabels]
      have hvsum := sum_vertexLabels_rate H a hD hv
      have hnonneg : 0 ≤ (U.card : ℝ) *
          ((B : ℝ) * (a / (D : ℝ))) := by
        positivity
      have hc : 0 ≤ (B : ℝ) * (a / (D : ℝ)) := by positivity
      rw [hset, Finset.card_insert_of_notMem hvU]
      push_cast
      nlinarith
theorem prob_setSurvives_le (H : IndexedHypergraph V E)
    {a : ℝ} (ha : 0 ≤ a) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {B : ℕ} (hcodeg :
      ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, u ≠ v →
        H.codegree u v ≤ B)
    {U : Finset V} (hU : U ⊆ H.vertices) :
    FiniteBernoulli.prob
        (FiniteBernoulli.expMarkProbability (rate H a D))
        {ω | setSurvives H ω U} ≤
      Real.exp
        (-((U.card : ℝ) * a) +
          (U.card : ℝ) ^ 2 * ((B : ℝ) * (a / (D : ℝ)))) := by
  rw [prob_setSurvives]
  apply Real.exp_le_exp.mpr
  have h := sum_setLabels_rate_lower H ha hD hcap hcodeg U hU
  linarith
/-- Degree of a fixed vertex in the induced hypergraph, as an indicator sum. -/
noncomputable def inducedDegreeCount (H : IndexedHypergraph V E)
    (v : V) (ω : E ⊕ V → Bool) : ℝ :=
  (H.edges.filter (fun e => v ∈ H.edge e)).sum (fun e =>
    FiniteBernoulli.eventIndicator
      {ω | setSurvives H ω (H.edge e)} ω)

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem inducedDegreeCount_eq_degree (H : IndexedHypergraph V E)
    (v : V) (ω : E ⊕ V → Bool) :
    inducedDegreeCount H v ω =
      (((H.induce (survivingVertices H ω)).degree v : ℝ)) := by
  classical
  simp only [inducedDegreeCount, FiniteBernoulli.eventIndicator,
    IndexedHypergraph.degree, IndexedHypergraph.induce_edges]
  rw [Finset.filter_comm, Finset.card_filter]
  norm_cast
  apply Finset.sum_congr rfl
  intro e he
  have heH : e ∈ H.edges := (Finset.mem_filter.mp he).1
  simp only [Set.mem_setOf_eq, ← edge_subset_survivors_iff H ω heH]

theorem expect_inducedDegreeCount_le (H : IndexedHypergraph V E)
    {r D B : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hcodeg :
      ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, u ≠ v →
        H.codegree u v ≤ B)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D) (v : V) :
    FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (inducedDegreeCount H v) ≤
      (H.degree v : ℝ) *
        Real.exp (-(r : ℝ) * a +
          (r : ℝ) ^ 2 * ((B : ℝ) * (a / (D : ℝ)))) := by
  classical
  unfold inducedDegreeCount
  rw [FiniteBernoulli.expect_sum]
  calc
    (H.edges.filter (fun e => v ∈ H.edge e)).sum (fun e =>
        FiniteBernoulli.expect
          (FiniteBernoulli.expMarkProbability (rate H a D))
          (fun ω => FiniteBernoulli.eventIndicator
            {ω | setSurvives H ω (H.edge e)} ω)) ≤
      (H.edges.filter (fun e => v ∈ H.edge e)).sum (fun _ =>
        Real.exp (-(r : ℝ) * a +
          (r : ℝ) ^ 2 * ((B : ℝ) * (a / (D : ℝ))))) := by
        apply Finset.sum_le_sum
        intro e he
        rw [FiniteBernoulli.expect_eventIndicator]
        have heH : e ∈ H.edges := (Finset.mem_filter.mp he).1
        simpa [hunif e heH] using
          (prob_setSurvives_le H ha hD hcap hcodeg
            (H.edge_subset e heH))
    _ = (H.degree v : ℝ) *
        Real.exp (-(r : ℝ) * a +
          (r : ℝ) ^ 2 * ((B : ℝ) * (a / (D : ℝ)))) := by
        simp [IndexedHypergraph.degree]
omit [Fintype V] [Fintype E] in
omit [DecidableEq E] in
theorem setSurvives_union (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) (U W : Finset V) :
    setSurvives H ω (U ∪ W) ↔
      setSurvives H ω U ∧ setSurvives H ω W := by
  constructor
  · intro h
    constructor
    · intro v hv
      exact h v (Finset.mem_union_left W hv)
    · intro v hv
      exact h v (Finset.mem_union_right U hv)
  · rintro ⟨hU, hW⟩ v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hU v hv
    · exact hW v hv

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem indicator_setSurvives_mul (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) (U W : Finset V) :
    FiniteBernoulli.eventIndicator
        {ω | setSurvives H ω U} ω *
      FiniteBernoulli.eventIndicator
        {ω | setSurvives H ω W} ω =
      FiniteBernoulli.eventIndicator
        {ω | setSurvives H ω (U ∪ W)} ω := by
  classical
  by_cases hU : setSurvives H ω U
  · by_cases hW : setSurvives H ω W
    · have hUW := (setSurvives_union H ω U W).mpr ⟨hU, hW⟩
      simp [FiniteBernoulli.eventIndicator, hU, hW, hUW]
    · have hUW : ¬ setSurvives H ω (U ∪ W) := by
        intro h
        exact hW ((setSurvives_union H ω U W).mp h).2
      simp [FiniteBernoulli.eventIndicator, hU, hW, hUW]
  · have hUW : ¬ setSurvives H ω (U ∪ W) := by
      intro h
      exact hU ((setSurvives_union H ω U W).mp h).1
    simp [FiniteBernoulli.eventIndicator, hU, hUW]

theorem expect_inducedDegreeCount_sq (H : IndexedHypergraph V E)
    (a : ℝ) (D : ℕ) (v : V) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω => (inducedDegreeCount H v ω) ^ 2) =
        (H.edges.filter (fun e => v ∈ H.edge e)).sum (fun e =>
          (H.edges.filter (fun f => v ∈ H.edge f)).sum (fun f =>
            FiniteBernoulli.prob
              (FiniteBernoulli.expMarkProbability (rate H a D))
              {ω | setSurvives H ω (H.edge e ∪ H.edge f)})) := by
  classical
  let I := H.edges.filter (fun e => v ∈ H.edge e)
  let p := FiniteBernoulli.expMarkProbability (rate H a D)
  have hpoint (ω : E ⊕ V → Bool) :
      (inducedDegreeCount H v ω) ^ 2 =
        I.sum (fun e => I.sum (fun f =>
          FiniteBernoulli.eventIndicator
            {ω | setSurvives H ω (H.edge e ∪ H.edge f)} ω)) := by
    simp only [inducedDegreeCount, I]
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_congr rfl
    intro f hf
    exact indicator_setSurvives_mul H ω (H.edge e) (H.edge f)
  calc
    FiniteBernoulli.expect p
        (fun ω => (inducedDegreeCount H v ω) ^ 2) =
      FiniteBernoulli.expect p
        (fun ω => I.sum (fun e => I.sum (fun f =>
          FiniteBernoulli.eventIndicator
            {ω | setSurvives H ω (H.edge e ∪ H.edge f)} ω))) := by
      congr 1
      funext ω
      exact hpoint ω
    _ = I.sum (fun e => I.sum (fun f =>
          FiniteBernoulli.expect p
            (FiniteBernoulli.eventIndicator
              {ω | setSurvives H ω (H.edge e ∪ H.edge f)}))) := by
      rw [FiniteBernoulli.expect_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [FiniteBernoulli.expect_sum]
    _ = I.sum (fun e => I.sum (fun f =>
          FiniteBernoulli.prob p
            {ω | setSurvives H ω (H.edge e ∪ H.edge f)})) := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro f hf
      exact FiniteBernoulli.expect_eventIndicator p _
/-- Incident copies at a fixed vertex, retaining multiplicity through labels. -/
def incidentEdges (H : IndexedHypergraph V E) (v : V) : Finset E :=
  H.edges.filter (fun e => v ∈ H.edge e)

/-- Ordered incident-copy pairs sharing a second vertex. -/
noncomputable def doublyIntersectingPairs (H : IndexedHypergraph V E)
    (v : V) : Finset (E × E) := by
  classical
  exact ((incidentEdges H v).product (incidentEdges H v)).filter
    (fun p => ∃ u ∈ H.vertices.erase v,
      u ∈ H.edge p.1 ∧ u ∈ H.edge p.2)

omit [Fintype V] [Fintype E] in
theorem card_doublyIntersectingPairs_le (H : IndexedHypergraph V E)
    {r B D : ℕ} (hunif : H.IsUniform r)
    {v : V} (hv : v ∈ H.vertices)
    (hB : H.maxCodegree ≤ B) (hD : H.degree v ≤ D) :
    (doublyIntersectingPairs H v).card ≤ B * (r * D) := by
  classical
  let C : V → Finset E := fun u =>
    H.edges.filter (fun e => v ∈ H.edge e ∧ u ∈ H.edge e)
  have hsub :
      doublyIntersectingPairs H v ⊆
        (H.vertices.erase v).biUnion (fun u => (C u).product (C u)) := by
    intro p hp
    obtain ⟨hprod, u, hu, hu₁, hu₂⟩ :=
      Finset.mem_filter.mp (show p ∈
        ((incidentEdges H v).product (incidentEdges H v)).filter
          (fun p => ∃ u ∈ H.vertices.erase v,
            u ∈ H.edge p.1 ∧ u ∈ H.edge p.2) from hp)
    obtain ⟨he₁, hv₁⟩ := Finset.mem_filter.mp (Finset.mem_product.mp hprod).1
    obtain ⟨he₂, hv₂⟩ := Finset.mem_filter.mp (Finset.mem_product.mp hprod).2
    exact Finset.mem_biUnion.mpr
      ⟨u, hu, Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨he₁, hv₁, hu₁⟩,
          Finset.mem_filter.mpr ⟨he₂, hv₂, hu₂⟩⟩⟩
  calc
    (doublyIntersectingPairs H v).card ≤
      ((H.vertices.erase v).biUnion
        (fun u => (C u).product (C u))).card :=
      Finset.card_le_card hsub
    _ ≤ (H.vertices.erase v).sum
        (fun u => ((C u).product (C u)).card) :=
      Finset.card_biUnion_le
    _ = (H.vertices.erase v).sum
        (fun u => H.codegree v u * H.codegree v u) := by
      apply Finset.sum_congr rfl
      intro u hu
      simp [C, IndexedHypergraph.codegree, Finset.card_product]
    _ ≤ B * (r * D) :=
      H.sum_codegree_sq_le hunif hv hB hD
omit [Fintype V] [Fintype E] in
omit [DecidableEq E] in
theorem union_card_of_good_incident_pair (H : IndexedHypergraph V E)
    {r : ℕ} (hunif : H.IsUniform r)
    {v : V} {e f : E}
    (he : e ∈ incidentEdges H v) (hf : f ∈ incidentEdges H v)
    (hgood : (e, f) ∉ doublyIntersectingPairs H v) :
    (H.edge e ∪ H.edge f).card + 1 = 2 * r := by
  classical
  obtain ⟨heH, hve⟩ := Finset.mem_filter.mp he
  obtain ⟨hfH, hvf⟩ := Finset.mem_filter.mp hf
  have hnot :
      ¬ ∃ u ∈ H.vertices.erase v,
        u ∈ H.edge e ∧ u ∈ H.edge f := by
    intro h
    exact hgood (Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨he, hf⟩, h⟩)
  have hinter : H.edge e ∩ H.edge f = {v} := by
    ext u
    constructor
    · intro hu
      have hue := (Finset.mem_inter.mp hu).1
      have huf := (Finset.mem_inter.mp hu).2
      have huv : u = v := by
        by_contra hne
        exact hnot ⟨u,
          Finset.mem_erase.mpr ⟨hne, H.edge_subset e heH hue⟩,
          hue, huf⟩
      simp [huv]
    · intro hu
      have huv : u = v := Finset.mem_singleton.mp hu
      subst u
      exact Finset.mem_inter.mpr ⟨hve, hvf⟩
  have hcount := Finset.card_union_add_card_inter (H.edge e) (H.edge f)
  rw [hinter, Finset.card_singleton, hunif e heH, hunif f hfH] at hcount
  omega
theorem prob_incident_pair_le_vertex (H : IndexedHypergraph V E)
    {a : ℝ} (ha : 0 ≤ a) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {v : V} {e f : E} (he : e ∈ incidentEdges H v) :
    FiniteBernoulli.prob
        (FiniteBernoulli.expMarkProbability (rate H a D))
        {ω | setSurvives H ω (H.edge e ∪ H.edge f)} ≤
      Real.exp (-a) := by
  have heH : e ∈ H.edges := (Finset.mem_filter.mp he).1
  have hve : v ∈ H.edge e := (Finset.mem_filter.mp he).2
  have hv : v ∈ H.vertices := H.edge_subset e heH hve
  have hp : ∀ i, 0 ≤
      FiniteBernoulli.expMarkProbability (rate H a D) i ∧
      FiniteBernoulli.expMarkProbability (rate H a D) i ≤ 1 :=
    markProbability_bounds H ha hD hcap
  calc
    FiniteBernoulli.prob
        (FiniteBernoulli.expMarkProbability (rate H a D))
        {ω | setSurvives H ω (H.edge e ∪ H.edge f)} ≤
      FiniteBernoulli.prob
        (FiniteBernoulli.expMarkProbability (rate H a D))
        {ω | vertexSurvives H ω v} := by
          apply FiniteBernoulli.prob_mono _ hp
          intro ω hω
          exact hω v (Finset.mem_union_left _ hve)
    _ = Real.exp (-a) := prob_vertexSurvives H a hD hv

theorem prob_good_incident_pair_le (H : IndexedHypergraph V E)
    {r B D : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hcodeg :
      ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, u ≠ v →
        H.codegree u v ≤ B)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D)
    {v : V} {e f : E}
    (he : e ∈ incidentEdges H v) (hf : f ∈ incidentEdges H v)
    (hgood : (e, f) ∉ doublyIntersectingPairs H v) :
    FiniteBernoulli.prob
        (FiniteBernoulli.expMarkProbability (rate H a D))
        {ω | setSurvives H ω (H.edge e ∪ H.edge f)} ≤
      Real.exp
        (-(((2 * r - 1 : ℕ) : ℝ) * a) +
          (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
            ((B : ℝ) * (a / (D : ℝ)))) := by
  have heH : e ∈ H.edges := (Finset.mem_filter.mp he).1
  have hfH : f ∈ H.edges := (Finset.mem_filter.mp hf).1
  have hcard : (H.edge e ∪ H.edge f).card = 2 * r - 1 := by
    have h := union_card_of_good_incident_pair H hunif he hf hgood
    omega
  have hsub : H.edge e ∪ H.edge f ⊆ H.vertices :=
    Finset.union_subset (H.edge_subset e heH) (H.edge_subset f hfH)
  simpa [hcard] using
    (prob_setSurvives_le H ha hD hcap hcodeg hsub)
theorem expect_inducedDegreeCount_sq_le_raw (H : IndexedHypergraph V E)
    {r B D : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hcodeg :
      ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, u ≠ v →
        H.codegree u v ≤ B)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D) (v : V) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω => (inducedDegreeCount H v ω) ^ 2) ≤
        ((incidentEdges H v).card : ℝ) ^ 2 *
          Real.exp
            (-(((2 * r - 1 : ℕ) : ℝ) * a) +
              (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
                ((B : ℝ) * (a / (D : ℝ)))) +
        ((doublyIntersectingPairs H v).card : ℝ) * Real.exp (-a) := by
  classical
  let I := incidentEdges H v
  let C := Real.exp
    (-(((2 * r - 1 : ℕ) : ℝ) * a) +
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
        ((B : ℝ) * (a / (D : ℝ))))
  let q := Real.exp (-a)
  have hbadsub : doublyIntersectingPairs H v ⊆ I.product I := by
    dsimp only [doublyIntersectingPairs]
    exact Finset.filter_subset _ _
  have hsum :
      (I.product I).sum (fun p =>
        if p ∈ doublyIntersectingPairs H v then q else 0) =
          ((doublyIntersectingPairs H v).card : ℝ) * q := by
    rw [← Finset.sum_filter]
    have heq :
        (I.product I).filter
          (fun p => p ∈ doublyIntersectingPairs H v) =
            doublyIntersectingPairs H v := by
      ext p
      constructor
      · intro hp
        exact (Finset.mem_filter.mp hp).2
      · intro hp
        exact Finset.mem_filter.mpr ⟨hbadsub hp, hp⟩
    rw [heq]
    simp
  rw [expect_inducedDegreeCount_sq]
  change I.sum (fun e => I.sum (fun f =>
    FiniteBernoulli.prob
      (FiniteBernoulli.expMarkProbability (rate H a D))
      {ω | setSurvives H ω (H.edge e ∪ H.edge f)})) ≤
        (I.card : ℝ) ^ 2 * C +
          ((doublyIntersectingPairs H v).card : ℝ) * q
  calc
    I.sum (fun e => I.sum (fun f =>
        FiniteBernoulli.prob
          (FiniteBernoulli.expMarkProbability (rate H a D))
          {ω | setSurvives H ω (H.edge e ∪ H.edge f)})) =
      (I.product I).sum (fun p =>
        FiniteBernoulli.prob
          (FiniteBernoulli.expMarkProbability (rate H a D))
          {ω | setSurvives H ω (H.edge p.1 ∪ H.edge p.2)}) := by
      exact (Finset.sum_product I I (fun p =>
        FiniteBernoulli.prob
          (FiniteBernoulli.expMarkProbability (rate H a D))
          {ω | setSurvives H ω (H.edge p.1 ∪ H.edge p.2)})).symm
    _ ≤ (I.product I).sum (fun p =>
        C + if p ∈ doublyIntersectingPairs H v then q else 0) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨he, hf⟩ := Finset.mem_product.mp hp
      by_cases hbad : p ∈ doublyIntersectingPairs H v
      · have hprob := prob_incident_pair_le_vertex H ha hD hcap (f := p.2) he
        have hC : 0 ≤ C := Real.exp_nonneg _
        simp only [if_pos hbad]
        exact le_trans hprob (by dsimp [C, q] at *; linarith)
      · have hprob :=
          prob_good_incident_pair_le H hunif hcap hcodeg ha hD (e := p.1) (f := p.2) he hf hbad
        simpa only [if_neg hbad, add_zero, C] using hprob
    _ = (I.card : ℝ) ^ 2 * C +
          ((doublyIntersectingPairs H v).card : ℝ) * q := by
      rw [Finset.sum_add_distrib, hsum]
      simp [Finset.card_product, pow_two, C, q]
theorem expect_inducedDegreeCount_sq_le (H : IndexedHypergraph V E)
    {r B D : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hB : H.maxCodegree ≤ B)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D)
    {v : V} (hv : v ∈ H.vertices) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω => (inducedDegreeCount H v ω) ^ 2) ≤
        (D : ℝ) ^ 2 *
          Real.exp
            (-(((2 * r - 1 : ℕ) : ℝ) * a) +
              (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
                ((B : ℝ) * (a / (D : ℝ)))) +
        ((B * (r * D) : ℕ) : ℝ) * Real.exp (-a) := by
  have hcodeg :
      ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, u ≠ v →
        H.codegree u v ≤ B := by
    intro u hu w hw hne
    exact (H.codegree_le_maxCodegree hu hw hne).trans hB
  have hdegreeNat : (incidentEdges H v).card ≤ D := hcap v hv
  have hdegree : ((incidentEdges H v).card : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast hdegreeNat
  have hdegreeSq :
      ((incidentEdges H v).card : ℝ) ^ 2 ≤ (D : ℝ) ^ 2 := by
    have hnonneg : 0 ≤ ((incidentEdges H v).card : ℝ) := by positivity
    nlinarith
  have hbad :
      ((doublyIntersectingPairs H v).card : ℝ) ≤
        ((B * (r * D) : ℕ) : ℝ) := by
    exact_mod_cast card_doublyIntersectingPairs_le H hunif hv hB (hcap v hv)
  calc
    FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (fun ω => (inducedDegreeCount H v ω) ^ 2) ≤
      ((incidentEdges H v).card : ℝ) ^ 2 *
        Real.exp
          (-(((2 * r - 1 : ℕ) : ℝ) * a) +
            (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
              ((B : ℝ) * (a / (D : ℝ)))) +
      ((doublyIntersectingPairs H v).card : ℝ) * Real.exp (-a) :=
      expect_inducedDegreeCount_sq_le_raw H hunif hcap hcodeg ha hD v
    _ ≤ (D : ℝ) ^ 2 *
        Real.exp
          (-(((2 * r - 1 : ℕ) : ℝ) * a) +
            (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
              ((B : ℝ) * (a / (D : ℝ)))) +
      ((B * (r * D) : ℕ) : ℝ) * Real.exp (-a) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hdegreeSq (Real.exp_nonneg _)
      · exact mul_le_mul_of_nonneg_right hbad (Real.exp_nonneg _)
theorem expect_inducedDegreeCount_ge (H : IndexedHypergraph V E)
    {r D : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D) (v : V) :
    (H.degree v : ℝ) * Real.exp (-((r : ℝ) * a)) ≤
      FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (inducedDegreeCount H v) := by
  classical
  unfold inducedDegreeCount
  rw [FiniteBernoulli.expect_sum]
  calc
    (H.degree v : ℝ) * Real.exp (-((r : ℝ) * a)) =
      (incidentEdges H v).sum
        (fun _ => Real.exp (-((r : ℝ) * a))) := by
      simp [incidentEdges, IndexedHypergraph.degree]
    _ ≤ (incidentEdges H v).sum (fun e =>
        FiniteBernoulli.expect
          (FiniteBernoulli.expMarkProbability (rate H a D))
          (fun ω => FiniteBernoulli.eventIndicator
            {ω | setSurvives H ω (H.edge e)} ω)) := by
      apply Finset.sum_le_sum
      intro e he
      rw [FiniteBernoulli.expect_eventIndicator]
      have heH : e ∈ H.edges := (Finset.mem_filter.mp he).1
      simpa [hunif e heH] using
        (prob_setSurvives_ge H ha hD hcap
          (H.edge_subset e heH))
omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem inducedDegreeCount_zero_of_not_vertexSurvives
    (H : IndexedHypergraph V E) (v : V) (ω : E ⊕ V → Bool)
    (hnot : ¬ vertexSurvives H ω v) :
    inducedDegreeCount H v ω = 0 := by
  classical
  unfold inducedDegreeCount
  apply Finset.sum_eq_zero
  intro e he
  have hve : v ∈ H.edge e := (Finset.mem_filter.mp he).2
  have hnotEdge : ¬ setSurvives H ω (H.edge e) := by
    intro hs
    exact hnot (hs v hve)
  simp [FiniteBernoulli.eventIndicator, hnotEdge]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem inducedDegreeCount_mul_vertexIndicator
    (H : IndexedHypergraph V E) (v : V) (ω : E ⊕ V → Bool) :
    inducedDegreeCount H v ω *
      FiniteBernoulli.eventIndicator
        {ω | vertexSurvives H ω v} ω =
      inducedDegreeCount H v ω := by
  classical
  by_cases hv : vertexSurvives H ω v
  · simp [FiniteBernoulli.eventIndicator, hv]
  · have hz := inducedDegreeCount_zero_of_not_vertexSurvives H v ω hv
    simp [FiniteBernoulli.eventIndicator, hv, hz]

omit [DecidableEq V] [Fintype V] [Fintype E] [DecidableEq E] in
theorem vertexIndicator_sq (H : IndexedHypergraph V E)
    (v : V) (ω : E ⊕ V → Bool) :
    (FiniteBernoulli.eventIndicator
      {ω | vertexSurvives H ω v} ω) ^ 2 =
      FiniteBernoulli.eventIndicator
        {ω | vertexSurvives H ω v} ω := by
  classical
  by_cases hv : vertexSurvives H ω v
  · simp [FiniteBernoulli.eventIndicator, hv]
  · simp [FiniteBernoulli.eventIndicator, hv]

theorem expect_centered_inducedDegreeCount_sq
    (H : IndexedHypergraph V E) (a c : ℝ)
    {D : ℕ} (hD : 0 < D) {v : V} (hv : v ∈ H.vertices) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω =>
        (inducedDegreeCount H v ω -
          c * FiniteBernoulli.eventIndicator
            {ω | vertexSurvives H ω v} ω) ^ 2) =
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω => (inducedDegreeCount H v ω) ^ 2) -
      2 * c * FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (inducedDegreeCount H v) +
      c ^ 2 * Real.exp (-a) := by
  let p := FiniteBernoulli.expMarkProbability (rate H a D)
  let I := fun ω => FiniteBernoulli.eventIndicator
    {ω | vertexSurvives H ω v} ω
  let Z := inducedDegreeCount H v
  have hpoint (ω : E ⊕ V → Bool) :
      (Z ω - c * I ω) ^ 2 =
        (Z ω) ^ 2 + (-2 * c) * Z ω + c ^ 2 * I ω := by
    have hZI : Z ω * I ω = Z ω :=
      inducedDegreeCount_mul_vertexIndicator H v ω
    have hI : (I ω) ^ 2 = I ω := vertexIndicator_sq H v ω
    calc
      (Z ω - c * I ω) ^ 2 =
        (Z ω) ^ 2 - 2 * c * (Z ω * I ω) +
          c ^ 2 * (I ω) ^ 2 := by ring
      _ = (Z ω) ^ 2 + (-2 * c) * Z ω + c ^ 2 * I ω := by
        rw [hZI, hI]
        ring
  calc
    FiniteBernoulli.expect p (fun ω => (Z ω - c * I ω) ^ 2) =
      FiniteBernoulli.expect p
        (fun ω => (Z ω) ^ 2 + (-2 * c) * Z ω + c ^ 2 * I ω) := by
      congr 1
      funext ω
      exact hpoint ω
    _ = FiniteBernoulli.expect p (fun ω => (Z ω) ^ 2) +
          (-2 * c) * FiniteBernoulli.expect p Z +
          c ^ 2 * FiniteBernoulli.expect p I := by
      rw [expect_add, expect_add, expect_mul_const, expect_mul_const]
    _ = FiniteBernoulli.expect p (fun ω => (Z ω) ^ 2) -
          2 * c * FiniteBernoulli.expect p Z +
          c ^ 2 * Real.exp (-a) := by
      have hI :
          FiniteBernoulli.expect p I = Real.exp (-a) := by
        exact (FiniteBernoulli.expect_eventIndicator p
          {ω | vertexSurvives H ω v}).trans
            (prob_vertexSurvives H a hD hv)
      rw [hI]
      ring
theorem expect_centered_inducedDegreeCount_sq_le_raw
    (H : IndexedHypergraph V E)
    {r B D : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hB : H.maxCodegree ≤ B)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D)
    {v : V} (hv : v ∈ H.vertices)
    {c : ℝ} (hc : 0 ≤ c) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω =>
        (inducedDegreeCount H v ω -
          c * FiniteBernoulli.eventIndicator
            {ω | vertexSurvives H ω v} ω) ^ 2) ≤
        ((incidentEdges H v).card : ℝ) ^ 2 *
          Real.exp
            (-(((2 * r - 1 : ℕ) : ℝ) * a) +
              (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
                ((B : ℝ) * (a / (D : ℝ)))) +
        ((doublyIntersectingPairs H v).card : ℝ) * Real.exp (-a) -
        2 * c * ((H.degree v : ℝ) * Real.exp (-((r : ℝ) * a))) +
        c ^ 2 * Real.exp (-a) := by
  have hcodeg :
      ∀ u ∈ H.vertices, ∀ w ∈ H.vertices, u ≠ w →
        H.codegree u w ≤ B := by
    intro u hu w hw hne
    exact (H.codegree_le_maxCodegree hu hw hne).trans hB
  have hsecond :=
    expect_inducedDegreeCount_sq_le_raw H hunif hcap hcodeg ha hD v
  have hfirst :=
    expect_inducedDegreeCount_ge H hunif hcap ha hD v
  have hnegative : -2 * c ≤ 0 := by linarith
  have hfirst' :
      (-2 * c) *
        FiniteBernoulli.expect
          (FiniteBernoulli.expMarkProbability (rate H a D))
          (inducedDegreeCount H v) ≤
      (-2 * c) * ((H.degree v : ℝ) *
        Real.exp (-((r : ℝ) * a))) :=
    mul_le_mul_of_nonpos_left hfirst hnegative
  rw [expect_centered_inducedDegreeCount_sq H a c hD hv]
  linarith
/-- Center at the degree predicted by independent vertex survival. -/
theorem expect_centered_inducedDegreeCount_sq_le
    (H : IndexedHypergraph V E)
    {r B D : ℕ} (hr : 1 ≤ r) (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hB : H.maxCodegree ≤ B)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D)
    {v : V} (hv : v ∈ H.vertices) :
    let c := (H.degree v : ℝ) *
      Real.exp (a - (r : ℝ) * a)
    let k := ((2 * r - 1 : ℕ) : ℝ)
    let b := (B : ℝ) * (a / (D : ℝ))
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω =>
        (inducedDegreeCount H v ω -
          c * FiniteBernoulli.eventIndicator
            {ω | vertexSurvives H ω v} ω) ^ 2) ≤
      (H.degree v : ℝ) ^ 2 *
        Real.exp (-(k * a)) * (Real.exp (k ^ 2 * b) - 1) +
      ((doublyIntersectingPairs H v).card : ℝ) * Real.exp (-a) := by
  dsimp
  let d := (H.degree v : ℝ)
  let k := ((2 * r - 1 : ℕ) : ℝ)
  let b := (B : ℝ) * (a / (D : ℝ))
  let s := a - (r : ℝ) * a
  let c := d * Real.exp s
  let q := Real.exp (-a)
  let t := Real.exp (-(r : ℝ) * a)
  let base := Real.exp (-(k * a))
  have hk : k = 2 * (r : ℝ) - 1 := by
    dsimp [k]
    have hle : 1 ≤ 2 * r := by omega
    rw [Nat.cast_sub hle]
    norm_num
  have hexp1 : Real.exp (-a) * Real.exp s = t := by
    calc
      Real.exp (-a) * Real.exp s = Real.exp (-a + s) :=
        (Real.exp_add _ _).symm
      _ = t := by
        congr 1
        dsimp [s, t]
        ring
  have hqc : q * c = d * t := by
    calc
      q * c = d * (Real.exp (-a) * Real.exp s) := by
        dsimp [q, c]
        ring
      _ = d * t := by rw [hexp1]
  have hexp2 : Real.exp s * t = base := by
    calc
      Real.exp s * t =
          Real.exp (s + (-(r : ℝ) * a)) := by
        dsimp [t]
        rw [Real.exp_add]
      _ = base := by
        congr 1
        dsimp [s, base]
        rw [hk]
        ring
  have hqc2 : c ^ 2 * q = d ^ 2 * base := by
    calc
      c ^ 2 * q = c * (q * c) := by ring
      _ = (d * Real.exp s) * (d * t) := by rw [hqc]
      _ = d ^ 2 * (Real.exp s * t) := by ring
      _ = d ^ 2 * base := by rw [hexp2]
  have hexp3 :
      Real.exp (-(k * a) + k ^ 2 * b) =
        base * Real.exp (k ^ 2 * b) := by
    dsimp [base]
    rw [Real.exp_add]
  have hraw :=
    expect_centered_inducedDegreeCount_sq_le_raw H hunif hcap hB ha hD hv
      (c := c) (by positivity)
  calc
    FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (fun ω =>
          (inducedDegreeCount H v ω -
            c * FiniteBernoulli.eventIndicator
              {ω | vertexSurvives H ω v} ω) ^ 2) ≤
      d ^ 2 * Real.exp (-(k * a) + k ^ 2 * b) +
        ((doublyIntersectingPairs H v).card : ℝ) * q -
        2 * c * (d * t) + c ^ 2 * q := by
      simpa only [d, k, b, q, t, c, incidentEdges, IndexedHypergraph.degree, neg_mul]
        using hraw
    _ = d ^ 2 * base * (Real.exp (k ^ 2 * b) - 1) +
          ((doublyIntersectingPairs H v).card : ℝ) * q := by
      rw [hexp3, ← hqc]
      nlinarith [hqc2]
theorem expect_centered_inducedDegreeCount_sq_le_linear
    (H : IndexedHypergraph V E)
    {r B D : ℕ} (hr : 1 ≤ r) (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hB : H.maxCodegree ≤ B)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D)
    {v : V} (hv : v ∈ H.vertices)
    (hsmall :
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
        ((B : ℝ) * (a / (D : ℝ))) ≤ 1) :
    let c := (H.degree v : ℝ) *
      Real.exp (a - (r : ℝ) * a)
    let k := ((2 * r - 1 : ℕ) : ℝ)
    let b := (B : ℝ) * (a / (D : ℝ))
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω =>
        (inducedDegreeCount H v ω -
          c * FiniteBernoulli.eventIndicator
            {ω | vertexSurvives H ω v} ω) ^ 2) ≤
      (H.degree v : ℝ) ^ 2 *
        Real.exp (-(k * a)) * (2 * (k ^ 2 * b)) +
      ((doublyIntersectingPairs H v).card : ℝ) * Real.exp (-a) := by
  dsimp
  let k := ((2 * r - 1 : ℕ) : ℝ)
  let b := (B : ℝ) * (a / (D : ℝ))
  let x := k ^ 2 * b
  have hx : 0 ≤ x := by
    dsimp [x, b]
    positivity
  have hAbs : |x| ≤ 1 := by
    simpa [abs_of_nonneg hx, x, k, b] using hsmall
  have hexpGap : Real.exp x - 1 ≤ 2 * x := by
    calc
      Real.exp x - 1 ≤ |Real.exp x - 1| := le_abs_self _
      _ ≤ 2 * |x| := Real.abs_exp_sub_one_le hAbs
      _ = 2 * x := by rw [abs_of_nonneg hx]
  have hcoeff : 0 ≤
      (H.degree v : ℝ) ^ 2 * Real.exp (-(k * a)) := by
    positivity
  have hraw :=
    expect_centered_inducedDegreeCount_sq_le H hr hunif hcap hB ha hD hv
  calc
    FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (fun ω =>
          (inducedDegreeCount H v ω -
            (H.degree v : ℝ) *
              Real.exp (a - (r : ℝ) * a) *
              FiniteBernoulli.eventIndicator
                {ω | vertexSurvives H ω v} ω) ^ 2) ≤
      (H.degree v : ℝ) ^ 2 * Real.exp (-(k * a)) *
        (Real.exp x - 1) +
      ((doublyIntersectingPairs H v).card : ℝ) * Real.exp (-a) := by
      simpa only [k, b, x] using hraw
    _ ≤ (H.degree v : ℝ) ^ 2 * Real.exp (-(k * a)) *
          (2 * x) +
        ((doublyIntersectingPairs H v).card : ℝ) * Real.exp (-a) := by
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left hexpGap hcoeff) _
theorem expect_centered_inducedDegreeCount_sq_le_global
    (H : IndexedHypergraph V E)
    {r B D : ℕ} (hr : 1 ≤ r) (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hB : H.maxCodegree ≤ B)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D)
    {v : V} (hv : v ∈ H.vertices)
    (hsmall :
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
        ((B : ℝ) * (a / (D : ℝ))) ≤ 1) :
    let c := (H.degree v : ℝ) *
      Real.exp (a - (r : ℝ) * a)
    let k := ((2 * r - 1 : ℕ) : ℝ)
    let b := (B : ℝ) * (a / (D : ℝ))
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω =>
        (inducedDegreeCount H v ω -
          c * FiniteBernoulli.eventIndicator
            {ω | vertexSurvives H ω v} ω) ^ 2) ≤
      (D : ℝ) ^ 2 * (2 * (k ^ 2 * b)) +
        ((B * (r * D) : ℕ) : ℝ) := by
  dsimp
  let k := ((2 * r - 1 : ℕ) : ℝ)
  let b := (B : ℝ) * (a / (D : ℝ))
  have hd : (H.degree v : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast hcap v hv
  have hdSq : (H.degree v : ℝ) ^ 2 ≤ (D : ℝ) ^ 2 := by
    have hnonneg : 0 ≤ (H.degree v : ℝ) := by positivity
    nlinarith
  have hbase : Real.exp (-(k * a)) ≤ 1 := by
    have hk : 0 ≤ k := by positivity
    have hneg : -(k * a) ≤ 0 := neg_nonpos.mpr (mul_nonneg hk ha)
    simpa using (Real.exp_le_exp.mpr hneg :
      Real.exp (-(k * a)) ≤ Real.exp 0)
  have hcoeff :
      (H.degree v : ℝ) ^ 2 * Real.exp (-(k * a)) ≤
        (D : ℝ) ^ 2 := by
    calc
      (H.degree v : ℝ) ^ 2 * Real.exp (-(k * a)) ≤
        (H.degree v : ℝ) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hbase (sq_nonneg _)
      _ = (H.degree v : ℝ) ^ 2 := by ring
      _ ≤ (D : ℝ) ^ 2 := hdSq
  have hmult : 0 ≤ 2 * (k ^ 2 * b) := by
    dsimp [b]
    positivity
  have hbad : ((doublyIntersectingPairs H v).card : ℝ) ≤
      ((B * (r * D) : ℕ) : ℝ) := by
    exact_mod_cast card_doublyIntersectingPairs_le H hunif hv hB (hcap v hv)
  have hq : Real.exp (-a) ≤ 1 := by
    have hneg : -a ≤ 0 := by linarith
    simpa using (Real.exp_le_exp.mpr hneg :
      Real.exp (-a) ≤ Real.exp 0)
  have hbadTerm :
      ((doublyIntersectingPairs H v).card : ℝ) * Real.exp (-a) ≤
        ((B * (r * D) : ℕ) : ℝ) := by
    calc
      ((doublyIntersectingPairs H v).card : ℝ) * Real.exp (-a) ≤
        ((doublyIntersectingPairs H v).card : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hq (by positivity)
      _ = ((doublyIntersectingPairs H v).card : ℝ) := by ring
      _ ≤ ((B * (r * D) : ℕ) : ℝ) := hbad
  have hraw :=
    expect_centered_inducedDegreeCount_sq_le_linear H hr hunif hcap hB
      ha hD hv hsmall
  calc
    FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (fun ω =>
          (inducedDegreeCount H v ω -
            (H.degree v : ℝ) *
              Real.exp (a - (r : ℝ) * a) *
              FiniteBernoulli.eventIndicator
                {ω | vertexSurvives H ω v} ω) ^ 2) ≤
      (H.degree v : ℝ) ^ 2 * Real.exp (-(k * a)) *
          (2 * (k ^ 2 * b)) +
        ((doublyIntersectingPairs H v).card : ℝ) * Real.exp (-a) := by
      simpa only [k, b] using hraw
    _ ≤ (D : ℝ) ^ 2 * (2 * (k ^ 2 * b)) +
        ((B * (r * D) : ℕ) : ℝ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hcoeff hmult) hbadTerm
omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- A unit of integer rounding plus centered deviation pays for a vertex's
positive degree excess after the survivor step. -/
theorem vertex_degreeExcess_le_abs_centered
    (H : IndexedHypergraph V E) (Dnext : ℕ)
    (ω : E ⊕ V → Bool) (v : V) (c : ℝ)
    (hc : c ≤ (Dnext : ℝ) + 1) :
    (((H.induce (survivingVertices H ω)).degree v - Dnext : ℕ) : ℝ) *
      FiniteBernoulli.eventIndicator
        {ω | vertexSurvives H ω v} ω ≤
      |inducedDegreeCount H v ω -
        c * FiniteBernoulli.eventIndicator
          {ω | vertexSurvives H ω v} ω| +
        FiniteBernoulli.eventIndicator
          {ω | vertexSurvives H ω v} ω := by
  classical
  let Z := inducedDegreeCount H v ω
  let I := FiniteBernoulli.eventIndicator
    {ω | vertexSurvives H ω v} ω
  have hZ :
      Z = (((H.induce (survivingVertices H ω)).degree v : ℝ)) :=
    inducedDegreeCount_eq_degree H v ω
  change
    (((H.induce (survivingVertices H ω)).degree v - Dnext : ℕ) : ℝ) * I ≤
      |Z - c * I| + I
  by_cases hs : vertexSurvives H ω v
  · have hI : I = 1 := by simp [I, FiniteBernoulli.eventIndicator, hs]
    rw [hI]
    simp only [mul_one]
    by_cases hdeg :
        (H.induce (survivingVertices H ω)).degree v ≤ Dnext
    · have hzero :
          (H.induce (survivingVertices H ω)).degree v - Dnext = 0 :=
        Nat.sub_eq_zero_of_le hdeg
      rw [hzero]
      norm_num
      exact add_nonneg (abs_nonneg _) (by norm_num)
    · have hle :
          Dnext ≤ (H.induce (survivingVertices H ω)).degree v := by omega
      have hcast :
          (((H.induce (survivingVertices H ω)).degree v - Dnext : ℕ) : ℝ) =
            Z - (Dnext : ℝ) := by
        rw [Nat.cast_sub hle, hZ]
      rw [hcast]
      have habs : Z - c ≤ |Z - c| := le_abs_self _
      linarith
  · have hI : I = 0 := by simp [I, FiniteBernoulli.eventIndicator, hs]
    rw [hI]
    simp
omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem induced_degreeExcess_eq_indicator_sum
    (H : IndexedHypergraph V E) (Dnext : ℕ)
    (ω : E ⊕ V → Bool) :
    (((H.induce (survivingVertices H ω)).degreeExcess Dnext : ℕ) : ℝ) =
      H.vertices.sum (fun v =>
        ((((H.induce (survivingVertices H ω)).degree v - Dnext : ℕ) : ℝ)) *
          FiniteBernoulli.eventIndicator
            {ω | vertexSurvives H ω v} ω) := by
  classical
  let J := H.induce (survivingVertices H ω)
  have hJvertices :
      J.vertices = H.vertices.filter (vertexSurvives H ω) := by
    simp [J, survivingVertices,
      Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]
  calc
    ((J.degreeExcess Dnext : ℕ) : ℝ) =
      J.vertices.sum (fun v => (((J.degree v - Dnext : ℕ) : ℝ))) := by
        simp [IndexedHypergraph.degreeExcess]
    _ = (H.vertices.filter (vertexSurvives H ω)).sum
          (fun v => (((J.degree v - Dnext : ℕ) : ℝ))) := by
      rw [hJvertices]
    _ = H.vertices.sum (fun v =>
          if vertexSurvives H ω v then
            (((J.degree v - Dnext : ℕ) : ℝ)) else 0) := by
      rw [Finset.sum_filter]
    _ = H.vertices.sum (fun v =>
          (((J.degree v - Dnext : ℕ) : ℝ)) *
            FiniteBernoulli.eventIndicator
              {ω | vertexSurvives H ω v} ω) := by
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hs : vertexSurvives H ω v
      · simp [FiniteBernoulli.eventIndicator, hs]
      · simp [FiniteBernoulli.eventIndicator, hs]
theorem expect_vertex_degreeExcess_le (H : IndexedHypergraph V E)
    {r B D Dnext : ℕ} (hr : 1 ≤ r) (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hB : H.maxCodegree ≤ B)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D)
    (hsmall :
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
        ((B : ℝ) * (a / (D : ℝ))) ≤ 1)
    (hthreshold :
      (D : ℝ) * Real.exp (a - (r : ℝ) * a) ≤
        (Dnext : ℝ) + 1)
    {v : V} (hv : v ∈ H.vertices) :
    let _ := (H.degree v : ℝ) *
      Real.exp (a - (r : ℝ) * a)
    let k := ((2 * r - 1 : ℕ) : ℝ)
    let b := (B : ℝ) * (a / (D : ℝ))
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω =>
        (((H.induce (survivingVertices H ω)).degree v - Dnext : ℕ) : ℝ) *
          FiniteBernoulli.eventIndicator
            {ω | vertexSurvives H ω v} ω) ≤
      Real.sqrt
        ((D : ℝ) ^ 2 * (2 * (k ^ 2 * b)) +
          ((B * (r * D) : ℕ) : ℝ)) +
        Real.exp (-a) := by
  dsimp
  let p := FiniteBernoulli.expMarkProbability (rate H a D)
  let c := (H.degree v : ℝ) * Real.exp (a - (r : ℝ) * a)
  let I := fun ω => FiniteBernoulli.eventIndicator
    {ω | vertexSurvives H ω v} ω
  let X := fun ω => inducedDegreeCount H v ω - c * I ω
  let M := (D : ℝ) ^ 2 *
      (2 * (((2 * r - 1 : ℕ) : ℝ) ^ 2 *
        ((B : ℝ) * (a / (D : ℝ))))) +
      ((B * (r * D) : ℕ) : ℝ)
  have hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1 :=
    markProbability_bounds H ha hD hcap
  have hcv : c ≤ (Dnext : ℝ) + 1 := by
    have hd : (H.degree v : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast hcap v hv
    have hfac : 0 ≤ Real.exp (a - (r : ℝ) * a) :=
      (Real.exp_pos _).le
    exact (mul_le_mul_of_nonneg_right hd hfac).trans hthreshold
  have hpoint (ω : E ⊕ V → Bool) :
      (((H.induce (survivingVertices H ω)).degree v - Dnext : ℕ) : ℝ) *
        I ω ≤ |X ω| + I ω :=
    vertex_degreeExcess_le_abs_centered H Dnext ω v c hcv
  have hcs := FiniteBernoulli.expect_abs_le_sqrt_expect_sq p hp X
  have hmoment :
      FiniteBernoulli.expect p (fun ω => (X ω) ^ 2) ≤ M := by
    simpa only [p, X, I, c, M] using
      (expect_centered_inducedDegreeCount_sq_le_global H hr hunif
        hcap hB ha hD hv hsmall)
  have hsqrt :
      Real.sqrt (FiniteBernoulli.expect p (fun ω => (X ω) ^ 2)) ≤
        Real.sqrt M :=
    Real.sqrt_le_sqrt hmoment
  have hI : FiniteBernoulli.expect p I = Real.exp (-a) := by
    exact (FiniteBernoulli.expect_eventIndicator p
      {ω | vertexSurvives H ω v}).trans
        (prob_vertexSurvives H a hD hv)
  calc
    FiniteBernoulli.expect p
        (fun ω =>
          (((H.induce (survivingVertices H ω)).degree v - Dnext : ℕ) : ℝ) *
            I ω) ≤
      FiniteBernoulli.expect p (fun ω => |X ω| + I ω) :=
      expect_mono p hp _ _ hpoint
    _ = FiniteBernoulli.expect p (fun ω => |X ω|) +
        FiniteBernoulli.expect p I := expect_add p _ _
    _ ≤ Real.sqrt M + Real.exp (-a) := by
      rw [hI]
      linarith
/-- Expected total degree excess in the induced survivor hypergraph. -/
theorem expect_induced_degreeExcess_le (H : IndexedHypergraph V E)
    {r B D Dnext : ℕ} (hr : 1 ≤ r) (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hB : H.maxCodegree ≤ B)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D)
    (hsmall :
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
        ((B : ℝ) * (a / (D : ℝ))) ≤ 1)
    (hthreshold :
      (D : ℝ) * Real.exp (a - (r : ℝ) * a) ≤
        (Dnext : ℝ) + 1) :
    let k := ((2 * r - 1 : ℕ) : ℝ)
    let b := (B : ℝ) * (a / (D : ℝ))
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω =>
        (((H.induce (survivingVertices H ω)).degreeExcess Dnext : ℕ) : ℝ)) ≤
      (H.vertices.card : ℝ) *
        (Real.sqrt
          ((D : ℝ) ^ 2 * (2 * (k ^ 2 * b)) +
            ((B * (r * D) : ℕ) : ℝ)) +
          Real.exp (-a)) := by
  dsimp
  let p := FiniteBernoulli.expMarkProbability (rate H a D)
  let M := (D : ℝ) ^ 2 *
      (2 * (((2 * r - 1 : ℕ) : ℝ) ^ 2 *
        ((B : ℝ) * (a / (D : ℝ))))) +
      ((B * (r * D) : ℕ) : ℝ)
  have hpoint (v : V) (hv : v ∈ H.vertices) :
      FiniteBernoulli.expect p
        (fun ω =>
          (((H.induce (survivingVertices H ω)).degree v - Dnext : ℕ) : ℝ) *
            FiniteBernoulli.eventIndicator
              {ω | vertexSurvives H ω v} ω) ≤
        Real.sqrt M + Real.exp (-a) := by
    simpa only [p, M] using
      (expect_vertex_degreeExcess_le H hr hunif hcap hB ha hD
        hsmall hthreshold hv)
  calc
    FiniteBernoulli.expect p
        (fun ω =>
          (((H.induce (survivingVertices H ω)).degreeExcess Dnext : ℕ) : ℝ)) =
      FiniteBernoulli.expect p
        (fun ω => H.vertices.sum (fun v =>
          (((H.induce (survivingVertices H ω)).degree v - Dnext : ℕ) : ℝ) *
            FiniteBernoulli.eventIndicator
              {ω | vertexSurvives H ω v} ω)) := by
      congr 1
      funext ω
      exact induced_degreeExcess_eq_indicator_sum H Dnext ω
    _ = H.vertices.sum (fun v =>
        FiniteBernoulli.expect p
          (fun ω =>
            (((H.induce (survivingVertices H ω)).degree v - Dnext : ℕ) : ℝ) *
              FiniteBernoulli.eventIndicator
                {ω | vertexSurvives H ω v} ω)) :=
      FiniteBernoulli.expect_sum p H.vertices _
    _ ≤ H.vertices.sum (fun _ => Real.sqrt M + Real.exp (-a)) :=
      Finset.sum_le_sum hpoint
    _ = (H.vertices.card : ℝ) *
          (Real.sqrt M + Real.exp (-a)) := by
      simp
      ring
/-- Choose the deterministic trim after each realized marking configuration. -/
noncomputable def trimmedNext (H : IndexedHypergraph V E)
    {r : ℕ} (hunif : H.IsUniform r)
    (Dnext : ℕ) (ω : E ⊕ V → Bool) : IndexedHypergraph V E :=
  Classical.choose ((sampledRound H ω).exists_trimmed_next hunif Dnext)

omit [Fintype V] [Fintype E] in
theorem trimmedNext_spec (H : IndexedHypergraph V E)
    {r : ℕ} (hunif : H.IsUniform r)
    (Dnext : ℕ) (ω : E ⊕ V → Bool) :
    let K := trimmedNext H hunif Dnext ω
    K.vertices = survivingVertices H ω ∧
    K.edges ⊆ (sampledRound H ω).nextBase.edges ∧
    K.IsUniform r ∧
    (∀ v ∈ K.vertices, K.degree v ≤ Dnext) ∧
    (∀ u v, K.codegree u v ≤ H.codegree u v) ∧
    (K.degreeDeficit Dnext +
      r * (sampledRound H ω).nextBase.edges.card ≤
      (survivingVertices H ω).card * Dnext +
        r * (sampledRound H ω).nextBase.degreeExcess Dnext) ∧
      K.edge = H.edge := by
  dsimp [trimmedNext]
  exact Classical.choose_spec
    ((sampledRound H ω).exists_trimmed_next hunif Dnext)

omit [Fintype V] [Fintype E] in
theorem trimmedNext_deficit_le (H : IndexedHypergraph V E)
    {r : ℕ} (hunif : H.IsUniform r)
    (Dnext : ℕ) (ω : E ⊕ V → Bool) :
    (((trimmedNext H hunif Dnext ω).degreeDeficit Dnext : ℕ) : ℝ) +
      (r : ℝ) * (inducedEdgeCount H ω) ≤
      ((survivingVertices H ω).card : ℝ) * (Dnext : ℝ) +
        (r : ℝ) *
          (((H.induce (survivingVertices H ω)).degreeExcess Dnext : ℕ) : ℝ) := by
  have hNat := (trimmedNext_spec H hunif Dnext ω).2.2.2.2.2.1
  have hNat' :
      (trimmedNext H hunif Dnext ω).degreeDeficit Dnext +
        r * (H.induce (survivingVertices H ω)).edges.card ≤
      (survivingVertices H ω).card * Dnext +
        r * (H.induce (survivingVertices H ω)).degreeExcess Dnext := by
    simpa [MatchingRound.nextBase, sampledRound] using hNat
  have hReal : (((trimmedNext H hunif Dnext ω).degreeDeficit Dnext : ℕ) : ℝ) +
      (r : ℝ) *
        (((H.induce (survivingVertices H ω)).edges.card : ℕ) : ℝ) ≤
      ((survivingVertices H ω).card : ℝ) * (Dnext : ℝ) +
        (r : ℝ) *
          (((H.induce (survivingVertices H ω)).degreeExcess Dnext : ℕ) : ℝ) := by
    exact_mod_cast hNat'
  simpa only [inducedEdgeCount_eq_card H ω] using hReal
/-- One-round expected degree-deficit recurrence after choosing the trim. -/
theorem expect_trimmedNext_degreeDeficit_le
    (H : IndexedHypergraph V E)
    {r B D Dnext : ℕ} (hr : 1 ≤ r) (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hB : H.maxCodegree ≤ B)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D)
    (hsmall :
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
        ((B : ℝ) * (a / (D : ℝ))) ≤ 1)
    (hthreshold :
      (D : ℝ) * Real.exp (a - (r : ℝ) * a) ≤
        (Dnext : ℝ) + 1)
    (hscale :
      (Dnext : ℝ) * Real.exp (-a) ≤
        (D : ℝ) * Real.exp (-((r : ℝ) * a))) :
    let k := ((2 * r - 1 : ℕ) : ℝ)
    let b := (B : ℝ) * (a / (D : ℝ))
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω =>
        (((trimmedNext H hunif Dnext ω).degreeDeficit Dnext : ℕ) : ℝ)) ≤
      Real.exp (-((r : ℝ) * a)) * (H.degreeDeficit D : ℝ) +
        (r : ℝ) * (H.vertices.card : ℝ) *
          (Real.sqrt
            ((D : ℝ) ^ 2 * (2 * (k ^ 2 * b)) +
              ((B * (r * D) : ℕ) : ℝ)) +
            Real.exp (-a)) := by
  dsimp
  let p := FiniteBernoulli.expMarkProbability (rate H a D)
  let S := (H.degreeDeficit D : ℝ)
  let n := (H.vertices.card : ℝ)
  let m := (H.edges.card : ℝ)
  let q := Real.exp (-a)
  let er := Real.exp (-((r : ℝ) * a))
  let K := Real.sqrt
    ((D : ℝ) ^ 2 *
      (2 * (((2 * r - 1 : ℕ) : ℝ) ^ 2 *
        ((B : ℝ) * (a / (D : ℝ))))) +
      ((B * (r * D) : ℕ) : ℝ)) + q
  let X : (E ⊕ V → Bool) → ℝ := fun ω =>
    (((trimmedNext H hunif Dnext ω).degreeDeficit Dnext : ℕ) : ℝ)
  let M : (E ⊕ V → Bool) → ℝ := inducedEdgeCount H
  let N : (E ⊕ V → Bool) → ℝ := fun ω => ((survivingVertices H ω).card : ℝ)
  let F : (E ⊕ V → Bool) → ℝ := fun ω =>
    (((H.induce (survivingVertices H ω)).degreeExcess Dnext : ℕ) : ℝ)
  have hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1 :=
    markProbability_bounds H ha hD hcap
  have hpoint (ω : E ⊕ V → Bool) :
      X ω + (r : ℝ) * M ω ≤
        (Dnext : ℝ) * N ω + (r : ℝ) * F ω := by
    dsimp [X, M, N, F]
    simpa [mul_comm] using trimmedNext_deficit_le H hunif Dnext ω
  have hmono := expect_mono p hp
    (fun ω => X ω + (r : ℝ) * M ω)
    (fun ω => (Dnext : ℝ) * N ω + (r : ℝ) * F ω) hpoint
  have hlinear :
      FiniteBernoulli.expect p X +
        (r : ℝ) * FiniteBernoulli.expect p M ≤
      (Dnext : ℝ) * FiniteBernoulli.expect p N +
        (r : ℝ) * FiniteBernoulli.expect p F := by
    simpa only [expect_add, expect_mul_const] using hmono
  have hn : FiniteBernoulli.expect p N = n * q := by
    simpa only [p, N, n, q] using expect_survivingVertices_card H a hD
  have hm : m * er ≤ FiniteBernoulli.expect p M := by
    simpa only [p, M, m, er] using
      expect_inducedEdgeCount_ge H hunif hcap ha hD
  have hF : FiniteBernoulli.expect p F ≤ n * K := by
    simpa only [p, F, n, q, K] using
      expect_induced_degreeExcess_le H hr hunif hcap hB ha hD
        hsmall hthreshold
  have hscaleN :
      (Dnext : ℝ) * (n * q) ≤ (n * (D : ℝ)) * er := by
    calc
      (Dnext : ℝ) * (n * q) = n * ((Dnext : ℝ) * q) := by ring
      _ ≤ n * ((D : ℝ) * er) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = (n * (D : ℝ)) * er := by ring
  have hrnonneg : 0 ≤ (r : ℝ) := by positivity
  have hm' : (r : ℝ) * (m * er) ≤
      (r : ℝ) * FiniteBernoulli.expect p M :=
    mul_le_mul_of_nonneg_left hm hrnonneg
  have hF' : (r : ℝ) * FiniteBernoulli.expect p F ≤
      (r : ℝ) * (n * K) :=
    mul_le_mul_of_nonneg_left hF hrnonneg
  have hcount : S + (r : ℝ) * m = n * (D : ℝ) := by
    dsimp [S, m, n]
    exact_mod_cast H.degreeDeficit_add_edges hunif hcap
  have hcountEr :
      (S + (r : ℝ) * m) * er = (n * (D : ℝ)) * er :=
    congrArg (fun x : ℝ => x * er) hcount
  dsimp [X, p, S, n, er, K] at *
  nlinarith [hlinear, hn, hm', hF', hscaleN, hcountEr]
/-- The trimmed deficit, normalized by the next degree cap, has a
one-round additive error. -/
theorem expect_trimmedNext_normalizedDeficit_le
    (H : IndexedHypergraph V E)
    {r B D Dnext : ℕ} (hr : 1 ≤ r) (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hB : H.maxCodegree ≤ B)
    {a δ : ℝ} (ha : 0 ≤ a) (hD : 0 < D) (hDnext : 0 < Dnext)
    (hsmall :
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
        ((B : ℝ) * (a / (D : ℝ))) ≤ 1)
    (hthreshold :
      (D : ℝ) * Real.exp (a - (r : ℝ) * a) ≤
        (Dnext : ℝ) + 1)
    (hscale :
      (Dnext : ℝ) * Real.exp (-a) ≤
        (D : ℝ) * Real.exp (-((r : ℝ) * a)))
    (hlower :
      (D : ℝ) * Real.exp (-((r : ℝ) * a)) ≤ Dnext)
    (herror :
      (r : ℝ) *
        (Real.sqrt
          ((D : ℝ) ^ 2 *
              (2 * ((((2 * r - 1 : ℕ) : ℝ) ^ 2) *
                ((B : ℝ) * (a / (D : ℝ))))) +
            ((B * (r * D) : ℕ) : ℝ)) +
          Real.exp (-a)) ≤ δ * (Dnext : ℝ)) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω =>
        (((trimmedNext H hunif Dnext ω).degreeDeficit Dnext : ℕ) : ℝ) /
          (Dnext : ℝ)) ≤
      (H.degreeDeficit D : ℝ) / (D : ℝ) +
        δ * (H.vertices.card : ℝ) := by
  let p := FiniteBernoulli.expMarkProbability (rate H a D)
  let S := (H.degreeDeficit D : ℝ)
  let n := (H.vertices.card : ℝ)
  let er := Real.exp (-((r : ℝ) * a))
  let K := Real.sqrt
    ((D : ℝ) ^ 2 *
      (2 * ((((2 * r - 1 : ℕ) : ℝ) ^ 2) *
        ((B : ℝ) * (a / (D : ℝ))))) +
      ((B * (r * D) : ℕ) : ℝ)) + Real.exp (-a)
  let X : (E ⊕ V → Bool) → ℝ := fun ω =>
    (((trimmedNext H hunif Dnext ω).degreeDeficit Dnext : ℕ) : ℝ)
  have hraw : FiniteBernoulli.expect p X ≤ er * S + (r : ℝ) * n * K := by
    simpa only [p, X, S, n, er, K] using
      (expect_trimmedNext_degreeDeficit_le H hr hunif hcap hB ha hD
        hsmall hthreshold hscale)
  have hlinear :
      FiniteBernoulli.expect p (fun ω => X ω / (Dnext : ℝ)) =
        FiniteBernoulli.expect p X / (Dnext : ℝ) := by
    calc
      FiniteBernoulli.expect p (fun ω => X ω / (Dnext : ℝ)) =
        FiniteBernoulli.expect p
          (fun ω => ((Dnext : ℝ)⁻¹) * X ω) := by
            congr 1
            funext ω
            ring
      _ = ((Dnext : ℝ)⁻¹) * FiniteBernoulli.expect p X :=
        expect_mul_const p _ X
      _ = FiniteBernoulli.expect p X / (Dnext : ℝ) := by ring
  have hDn : (0 : ℝ) < D := by exact_mod_cast hD
  have hDnextn : (0 : ℝ) < Dnext := by exact_mod_cast hDnext
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hscaleS : er * S ≤ (S / (D : ℝ)) * (Dnext : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hlower (div_nonneg hS hDn.le)
    have hident : (D : ℝ) * er * (S / (D : ℝ)) = er * S := by
      field_simp
    nlinarith
  have herrorN : (r : ℝ) * n * K ≤ δ * n * (Dnext : ℝ) := by
    have h := mul_le_mul_of_nonneg_left herror hn
    nlinarith
  have hbound :
      FiniteBernoulli.expect p X ≤
        ((S / (D : ℝ)) + δ * n) * (Dnext : ℝ) := by
    nlinarith [hraw, hscaleS, herrorN]
  have hdiv := (div_le_iff₀ hDnextn).mpr hbound
  simpa only [p, X, S, n, hlinear] using hdiv
/-- Select one marking configuration that controls the backward potential:
surviving vertices, normalized deficit, and unmatched waste together. -/
theorem exists_round_potential_le
    (H : IndexedHypergraph V E)
    {r B D Dnext : ℕ} (hr : 1 ≤ r) (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hB : H.maxCodegree ≤ B)
    {a δ A C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hD : 0 < D) (hDnext : 0 < Dnext)
    (hsmall :
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
        ((B : ℝ) * (a / (D : ℝ))) ≤ 1)
    (hthreshold :
      (D : ℝ) * Real.exp (a - (r : ℝ) * a) ≤
        (Dnext : ℝ) + 1)
    (hscale :
      (Dnext : ℝ) * Real.exp (-a) ≤
        (D : ℝ) * Real.exp (-((r : ℝ) * a)))
    (hlower :
      (D : ℝ) * Real.exp (-((r : ℝ) * a)) ≤ Dnext)
    (herror :
      (r : ℝ) *
        (Real.sqrt
          ((D : ℝ) ^ 2 *
              (2 * ((((2 * r - 1 : ℕ) : ℝ) ^ 2) *
                ((B : ℝ) * (a / (D : ℝ))))) +
            ((B * (r * D) : ℕ) : ℝ)) +
          Real.exp (-a)) ≤ δ * (Dnext : ℝ)) :
    ∃ ω : E ⊕ V → Bool,
      A * ((survivingVertices H ω).card : ℝ) +
        C *
          ((((trimmedNext H hunif Dnext ω).degreeDeficit Dnext : ℕ) : ℝ) /
            (Dnext : ℝ)) +
        ((sampledRound H ω).waste.card : ℝ) ≤
      (A * Real.exp (-a) + C * δ + (r : ℝ) * a ^ 2) *
          (H.vertices.card : ℝ) +
        (C + a) * ((H.degreeDeficit D : ℕ) : ℝ) / (D : ℝ) := by
  let p := FiniteBernoulli.expMarkProbability (rate H a D)
  let N : (E ⊕ V → Bool) → ℝ := fun ω =>
    ((survivingVertices H ω).card : ℝ)
  let Z : (E ⊕ V → Bool) → ℝ := fun ω =>
    (((trimmedNext H hunif Dnext ω).degreeDeficit Dnext : ℕ) : ℝ) /
      (Dnext : ℝ)
  let W : (E ⊕ V → Bool) → ℝ := fun ω =>
    ((sampledRound H ω).waste.card : ℝ)
  let X : (E ⊕ V → Bool) → ℝ := fun ω =>
    A * N ω + C * Z ω + W ω
  have hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1 :=
    markProbability_bounds H ha hD hcap
  obtain ⟨ω, hω⟩ := exists_le_expect p hp X
  have hlin : FiniteBernoulli.expect p X =
      A * FiniteBernoulli.expect p N +
        C * FiniteBernoulli.expect p Z +
          FiniteBernoulli.expect p W := by
    dsimp [X]
    rw [expect_add, expect_add, expect_mul_const, expect_mul_const]
  have hN : FiniteBernoulli.expect p N =
      (H.vertices.card : ℝ) * Real.exp (-a) := by
    simpa only [p, N] using expect_survivingVertices_card H a hD
  have hZ : FiniteBernoulli.expect p Z ≤
      (H.degreeDeficit D : ℝ) / (D : ℝ) +
        δ * (H.vertices.card : ℝ) := by
    simpa only [p, Z] using
      (expect_trimmedNext_normalizedDeficit_le H hr hunif hcap hB
        ha hD hDnext hsmall hthreshold hscale hlower herror)
  have hW : FiniteBernoulli.expect p W ≤
      a * ((H.degreeDeficit D : ℕ) : ℝ) / (D : ℝ) +
        (r : ℝ) * a ^ 2 * (H.vertices.card : ℝ) := by
    have h := expect_waste_le_simplified H hunif hcap ha hD
    convert h using 1; ring
  refine ⟨ω, ?_⟩
  have hCZ := mul_le_mul_of_nonneg_left hZ hC
  dsimp [X, N, Z, W] at hω
  calc
    A * ((survivingVertices H ω).card : ℝ) +
          C *
            ((((trimmedNext H hunif Dnext ω).degreeDeficit Dnext : ℕ) : ℝ) /
              (Dnext : ℝ)) +
          ((sampledRound H ω).waste.card : ℝ) ≤
        FiniteBernoulli.expect p X := hω
    _ = A * FiniteBernoulli.expect p N +
          C * FiniteBernoulli.expect p Z +
            FiniteBernoulli.expect p W := hlin
    _ ≤ (A * Real.exp (-a) + C * δ + (r : ℝ) * a ^ 2) *
          (H.vertices.card : ℝ) +
        (C + a) * ((H.degreeDeficit D : ℕ) : ℝ) / (D : ℝ) := by
      rw [hN]
      calc
        A * ((H.vertices.card : ℝ) * Real.exp (-a)) +
            C * FiniteBernoulli.expect p Z +
              FiniteBernoulli.expect p W ≤
          A * ((H.vertices.card : ℝ) * Real.exp (-a)) +
            C * ((H.degreeDeficit D : ℝ) / (D : ℝ) +
              δ * (H.vertices.card : ℝ)) +
            (a * (H.degreeDeficit D : ℝ) / (D : ℝ) +
              (r : ℝ) * a ^ 2 * (H.vertices.card : ℝ)) := by
                linarith [hCZ, hW]
        _ = _ := by ring
/-- A residual hypergraph together with all accepted edge copies and the
number of vertices deleted without coverage in earlier rounds. -/
structure MatchingState (H₀ : IndexedHypergraph V E)
    (r B : ℕ) (D : ℕ → ℕ) (i : ℕ) where
  residual : IndexedHypergraph V E
  accepted : Finset E
  wasted : ℕ
  vertices_subset : residual.vertices ⊆ H₀.vertices
  edges_subset : residual.edges ⊆ H₀.edges
  edge_eq : residual.edge = H₀.edge
  uniform : residual.IsUniform r
  degree_cap : ∀ v ∈ residual.vertices, residual.degree v ≤ D i
  codegree_cap : residual.maxCodegree ≤ B
  accepted_matching : H₀.IsMatching accepted
  residual_disjoint_accepted : Disjoint residual.vertices (H₀.covered accepted)
  partition_card :
    (H₀.covered accepted).card + residual.vertices.card + wasted = H₀.vertices.card

/-- The initial residual state before any marking. -/
def initialMatchingState (H₀ : IndexedHypergraph V E)
    {r B : ℕ} (D : ℕ → ℕ)
    (hunif : H₀.IsUniform r)
    (hcap : ∀ v ∈ H₀.vertices, H₀.degree v ≤ D 0)
    (hB : H₀.maxCodegree ≤ B) :
    MatchingState H₀ r B D 0 where
  residual := H₀
  accepted := ∅
  wasted := 0
  vertices_subset := Finset.Subset.rfl
  edges_subset := Finset.Subset.rfl
  edge_eq := rfl
  uniform := hunif
  degree_cap := hcap
  codegree_cap := hB
  accepted_matching := by
    constructor
    · simp
    · simp
  residual_disjoint_accepted := by simp [IndexedHypergraph.covered]
  partition_card := by simp [IndexedHypergraph.covered]

/-- The quantity controlled by the backward potential at round `i`. -/
noncomputable def MatchingState.potential
    {H₀ : IndexedHypergraph V E} {r B : ℕ} {D : ℕ → ℕ} {i : ℕ}
    (s : MatchingState H₀ r B D i)
    (q δ a β : ℝ) (T : ℕ) : ℝ :=
  Theorem2.lossPotentialA q δ a β T i * (s.residual.vertices.card : ℝ) +
    Theorem2.lossPotentialB a T i *
      ((s.residual.degreeDeficit (D i) : ℝ) / (D i : ℝ)) +
    (s.wasted : ℝ)
omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- The residual and initial hypergraphs interpret every edge-copy label identically. -/
theorem MatchingState.covered_eq
    {H₀ : IndexedHypergraph V E} {r B : ℕ} {D : ℕ → ℕ} {i : ℕ}
    (s : MatchingState H₀ r B D i) (F : Finset E) :
    s.residual.covered F = H₀.covered F := by
  simp only [IndexedHypergraph.covered, s.edge_eq]

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- A residual matching remains a matching in the original hypergraph. -/
theorem MatchingState.lift_matching
    {H₀ : IndexedHypergraph V E} {r B : ℕ} {D : ℕ → ℕ} {i : ℕ}
    (s : MatchingState H₀ r B D i) {F : Finset E}
    (hF : s.residual.IsMatching F) : H₀.IsMatching F := by
  constructor
  · exact hF.1.trans s.edges_subset
  · intro e he f hf hne
    simpa only [← s.edge_eq] using hF.2 he hf hne

omit [Fintype V] [Fintype E] in
private theorem matching_union_of_disjoint_covered
    (H : IndexedHypergraph V E) {M F : Finset E}
    (hM : H.IsMatching M) (hF : H.IsMatching F)
    (hdisj : Disjoint (H.covered M) (H.covered F)) :
    H.IsMatching (M ∪ F) := by
  classical
  constructor
  · exact Finset.union_subset hM.1 hF.1
  · intro e he f hf hne
    rcases Finset.mem_union.mp he with heM | heF
    · rcases Finset.mem_union.mp hf with hfM | hfF
      · exact hM.2 heM hfM hne
      · apply Finset.disjoint_left.mpr
        intro v hve hvf
        exact (Finset.disjoint_left.mp hdisj)
          (Finset.mem_biUnion.mpr ⟨e, heM, hve⟩)
          (Finset.mem_biUnion.mpr ⟨f, hfF, hvf⟩)
    · rcases Finset.mem_union.mp hf with hfM | hfF
      · apply Finset.disjoint_left.mpr
        intro v hve hvf
        exact (Finset.disjoint_left.mp hdisj)
          (Finset.mem_biUnion.mpr ⟨f, hfM, hvf⟩)
          (Finset.mem_biUnion.mpr ⟨e, heF, hve⟩)
      · exact hF.2 heF hfF hne

omit [Fintype V] [Fintype E] in
/-- Extend the accumulated matching by a matching in the current residual. -/
theorem MatchingState.matching_union
    {H₀ : IndexedHypergraph V E} {r B : ℕ} {D : ℕ → ℕ} {i : ℕ}
    (s : MatchingState H₀ r B D i) {F : Finset E}
    (hF : s.residual.IsMatching F) :
    H₀.IsMatching (s.accepted ∪ F) := by
  have hcoveredF : H₀.covered F ⊆ s.residual.vertices := by
    rw [← s.covered_eq F]
    exact s.residual.covered_subset_vertices hF.1
  exact matching_union_of_disjoint_covered H₀ s.accepted_matching
    (s.lift_matching hF)
    (Finset.disjoint_of_subset_right hcoveredF
      s.residual_disjoint_accepted.symm)

omit [Fintype V] [Fintype E] in
private theorem covered_union (H : IndexedHypergraph V E) (M F : Finset E) :
    H.covered (M ∪ F) = H.covered M ∪ H.covered F := by
  exact Finset.union_biUnion
/-- Update the residual state after any marking and deterministic trim. The
combinatorial invariants hold for every outcome. -/
noncomputable def MatchingState.next
    {H₀ : IndexedHypergraph V E} {r B : ℕ} {D : ℕ → ℕ} {i : ℕ}
    (s : MatchingState H₀ r B D i) (ω : E ⊕ V → Bool) :
    MatchingState H₀ r B D (i + 1) := by
  classical
  let H := s.residual
  let R := sampledRound H ω
  let K := trimmedNext H s.uniform (D (i + 1)) ω
  have hspec := trimmedNext_spec H s.uniform (D (i + 1)) ω
  have hverts : K.vertices ⊆ H.vertices := by
    rw [hspec.1]
    exact R.survivors_subset
  have hedges : K.edges ⊆ H.edges := by
    have hbase := H.induce_edges_subset (survivingVertices H ω)
    exact hspec.2.1.trans (by simp [MatchingRound.nextBase, sampledRound] at hbase ⊢)
  have hcoverA : H₀.covered R.accepted ⊆ H.vertices := by
    rw [← s.covered_eq R.accepted]
    exact R.accepted_covered_subset
  have hcoverDisj : Disjoint (H₀.covered s.accepted) (H₀.covered R.accepted) :=
    Finset.disjoint_of_subset_right hcoverA s.residual_disjoint_accepted.symm
  have hcoveredUnion : H₀.covered (s.accepted ∪ R.accepted) =
      H₀.covered s.accepted ∪ H₀.covered R.accepted :=
    covered_union H₀ s.accepted R.accepted
  refine {
    residual := K
    accepted := s.accepted ∪ R.accepted
    wasted := s.wasted + R.waste.card
    vertices_subset := hverts.trans s.vertices_subset
    edges_subset := hedges.trans s.edges_subset
    edge_eq := hspec.2.2.2.2.2.2.trans s.edge_eq
    uniform := hspec.2.2.1
    degree_cap := hspec.2.2.2.1
    codegree_cap := ?_
    accepted_matching := s.matching_union R.accepted_matching
    residual_disjoint_accepted := ?_
    partition_card := ?_
  }
  · unfold IndexedHypergraph.maxCodegree
    apply Finset.sup_le
    intro u hu
    apply Finset.sup_le
    intro v hv
    have hv' := Finset.mem_erase.mp hv
    have hne : u ≠ v := hv'.1.symm
    have hcodeg := hspec.2.2.2.2.1 u v
    exact (hcodeg.trans
      (H.codegree_le_maxCodegree (hverts hu) (hverts hv'.2) hne)).trans
        s.codegree_cap
  · apply Finset.disjoint_left.mpr
    intro v hv hvcov
    have hvR : v ∈ R.survivors := by
      change v ∈ survivingVertices H ω
      rw [← hspec.1]
      exact hv
    rw [hcoveredUnion] at hvcov
    rcases Finset.mem_union.mp hvcov with hvM | hvA
    · exact (Finset.disjoint_left.mp s.residual_disjoint_accepted)
        (R.survivors_subset hvR) hvM
    · have hvA' : v ∈ H.covered R.accepted := by
        change v ∈ s.residual.covered R.accepted
        rw [s.covered_eq R.accepted]
        exact hvA
      exact (Finset.disjoint_left.mp R.survivors_disjoint_accepted)
        hvR hvA'
  · have hround := R.waste_partition_card
    have hcardUnion :
        (H₀.covered (s.accepted ∪ R.accepted)).card =
          (H₀.covered s.accepted).card + (H₀.covered R.accepted).card := by
      rw [hcoveredUnion, Finset.card_union_of_disjoint hcoverDisj]
    have hcardA : (H₀.covered R.accepted).card =
        (H.covered R.accepted).card := by
      simpa only [H] using congrArg Finset.card (s.covered_eq R.accepted).symm
    have hcardK : K.vertices.card = R.survivors.card := by
      rw [hspec.1]
      rfl
    have hstart : (H₀.covered s.accepted).card + H.vertices.card +
        s.wasted = H₀.vertices.card := s.partition_card
    have hround' : K.vertices.card + (H₀.covered R.accepted).card +
        R.waste.card = H.vertices.card := by
      rw [hcardK, hcardA]
      exact hround
    rw [hcardUnion]
    omega
omit [Fintype V] [Fintype E] in
@[simp] theorem MatchingState.next_residual
    {H₀ : IndexedHypergraph V E} {r B : ℕ} {D : ℕ → ℕ} {i : ℕ}
    (s : MatchingState H₀ r B D i) (ω : E ⊕ V → Bool) :
    (s.next ω).residual =
      trimmedNext s.residual s.uniform (D (i + 1)) ω := rfl

omit [Fintype V] [Fintype E] in
@[simp] theorem MatchingState.next_accepted
    {H₀ : IndexedHypergraph V E} {r B : ℕ} {D : ℕ → ℕ} {i : ℕ}
    (s : MatchingState H₀ r B D i) (ω : E ⊕ V → Bool) :
    (s.next ω).accepted = s.accepted ∪ (sampledRound s.residual ω).accepted := rfl

omit [Fintype V] [Fintype E] in
@[simp] theorem MatchingState.next_wasted
    {H₀ : IndexedHypergraph V E} {r B : ℕ} {D : ℕ → ℕ} {i : ℕ}
    (s : MatchingState H₀ r B D i) (ω : E ⊕ V → Bool) :
    (s.next ω).wasted = s.wasted + (sampledRound s.residual ω).waste.card := rfl
/-- Choose one round so that the backward potential does not increase. -/
theorem MatchingState.exists_next_potential_le
    {H₀ : IndexedHypergraph V E} {r B : ℕ} {D : ℕ → ℕ} {i : ℕ}
    (s : MatchingState H₀ r B D i)
    (T : ℕ) (hi : i < T)
    {a δ : ℝ} (ha : 0 ≤ a) (_hδ : 0 ≤ δ)
    (hr : 1 ≤ r) (hD : 0 < D i) (hDnext : 0 < D (i + 1))
    (hsmall :
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
        ((B : ℝ) * (a / (D i : ℝ))) ≤ 1)
    (hthreshold :
      (D i : ℝ) * Real.exp (a - (r : ℝ) * a) ≤
        (D (i + 1) : ℝ) + 1)
    (hscale :
      (D (i + 1) : ℝ) * Real.exp (-a) ≤
        (D i : ℝ) * Real.exp (-((r : ℝ) * a)))
    (hlower :
      (D i : ℝ) * Real.exp (-((r : ℝ) * a)) ≤ D (i + 1))
    (herror :
      (r : ℝ) *
        (Real.sqrt
          ((D i : ℝ) ^ 2 *
              (2 * ((((2 * r - 1 : ℕ) : ℝ) ^ 2) *
                ((B : ℝ) * (a / (D i : ℝ))))) +
            ((B * (r * D i) : ℕ) : ℝ)) +
          Real.exp (-a)) ≤ δ * (D (i + 1) : ℝ)) :
    ∃ ω : E ⊕ V → Bool,
      (s.next ω).potential (Real.exp (-a)) δ a ((r : ℝ) * a ^ 2) T ≤
        s.potential (Real.exp (-a)) δ a ((r : ℝ) * a ^ 2) T := by
  let q := Real.exp (-a)
  let β := (r : ℝ) * a ^ 2
  let A := Theorem2.lossPotentialA q δ a β T (i + 1)
  let C := Theorem2.lossPotentialB a T (i + 1)
  have hC : 0 ≤ C := Theorem2.lossPotentialB_nonneg a ha T (i + 1)
  obtain ⟨ω, hselect⟩ :=
    exists_round_potential_le s.residual hr s.uniform s.degree_cap
      s.codegree_cap ha hC hD hDnext hsmall hthreshold hscale
      hlower herror (A := A)
  have hnext :
      (s.next ω).potential q δ a β T =
        A * ((survivingVertices s.residual ω).card : ℝ) +
          C *
            ((((trimmedNext s.residual s.uniform (D (i + 1)) ω).degreeDeficit
                (D (i + 1)) : ℕ) : ℝ) / (D (i + 1) : ℝ)) +
          ((sampledRound s.residual ω).waste.card : ℝ) +
          (s.wasted : ℝ) := by
    simp only [MatchingState.potential, MatchingState.next_residual,
      MatchingState.next_wasted, Nat.cast_add]
    rw [(trimmedNext_spec s.residual s.uniform (D (i + 1)) ω).1]
    dsimp [A, C]
    ring
  have hcurrent :
      s.potential q δ a β T =
        (A * q + C * δ + β) * (s.residual.vertices.card : ℝ) +
          (C + a) * ((s.residual.degreeDeficit (D i) : ℕ) : ℝ) /
            (D i : ℝ) +
          (s.wasted : ℝ) := by
    unfold MatchingState.potential
    rw [Theorem2.lossPotentialA_step q δ a β hi,
      Theorem2.lossPotentialB_step a hi]
    dsimp [A, C]
    ring
  refine ⟨ω, ?_⟩
  rw [hnext, hcurrent]
  dsimp [q, β] at hselect ⊢
  linarith [hselect]
/-- A coarse bound for the square-root error under degree-ratio and
half-life estimates. -/
theorem one_round_error_le_eight
    {r B D Dnext : ℕ} (hr : 2 ≤ r) (hB : 1 ≤ B)
    (hD : 0 < D)
    {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hratio : (B : ℝ) / (D : ℝ) ≤ b)
    (hhalf : (D : ℝ) ≤ 2 * (Dnext : ℝ)) :
    (r : ℝ) *
      (Real.sqrt
        ((D : ℝ) ^ 2 *
            (2 * ((((2 * r - 1 : ℕ) : ℝ) ^ 2) *
              ((B : ℝ) * (a / (D : ℝ))))) +
          ((B * (r * D) : ℕ) : ℝ)) +
        Real.exp (-a)) ≤
      8 * (r : ℝ) ^ 2 * Real.sqrt b * (Dnext : ℝ) := by
  let R : ℝ := r
  let d : ℝ := D
  let C : ℝ := B
  let k : ℝ := (2 * r - 1 : ℕ)
  let M : ℝ := d ^ 2 * (2 * (k ^ 2 * (C * (a / d)))) +
    ((B * (r * D) : ℕ) : ℝ)
  have hR : 1 ≤ R := by dsimp [R]; exact_mod_cast (by omega : 1 ≤ r)
  have hR0 : 0 ≤ R := by linarith
  have hd : 0 < d := by dsimp [d]; exact_mod_cast hD
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hBd : C ≤ d * b := by
    dsimp [C, d]
    nlinarith [(div_le_iff₀ hd).mp hratio]
  have hk0 : 0 ≤ k := by dsimp [k]; positivity
  have hk : k ≤ 2 * R := by
    dsimp [k, R]
    have hnat : 2 * r - 1 ≤ 2 * r := Nat.sub_le _ _
    exact_mod_cast hnat
  have hkSq : k ^ 2 ≤ 4 * R ^ 2 := by nlinarith
  have hka : k ^ 2 * a ≤ k ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg k) (sub_nonneg.mpr ha1)]
  have hR2 : R ≤ R ^ 2 := by nlinarith
  have hcoeff : 2 * k ^ 2 * a + R ≤ 9 * R ^ 2 := by
    nlinarith [hkSq, hka, hR2]
  have hMident : M = d * C * (2 * k ^ 2 * a + R) := by
    dsimp [M, d, C, R]
    have hne : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
    simp only [Nat.cast_mul]
    field_simp
  have hMbound : M ≤ (3 * R * d * Real.sqrt b) ^ 2 := by
    calc
      M = d * C * (2 * k ^ 2 * a + R) := hMident
      _ ≤ d * C * (9 * R ^ 2) :=
        mul_le_mul_of_nonneg_left hcoeff (mul_nonneg hd.le hC)
      _ ≤ (d * (d * b)) * (9 * R ^ 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hBd hd.le) (by positivity)
      _ = (3 * R * d * Real.sqrt b) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hb]
        ring
  have hroot : Real.sqrt M ≤ 3 * R * d * Real.sqrt b :=
    Real.sqrt_le_iff.mpr ⟨by positivity, hMbound⟩
  have hbSq : b ^ 2 ≤ b := by
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hb1)]
  have hbroot : b ≤ Real.sqrt b := (Real.le_sqrt hb hb).mpr hbSq
  have hdb : 1 ≤ d * b := by
    have hBC : (1 : ℝ) ≤ C := by dsimp [C]; exact_mod_cast hB
    linarith
  have hdroot : 1 ≤ d * Real.sqrt b := by
    nlinarith [mul_le_mul_of_nonneg_left hbroot hd.le]
  have hq : Real.exp (-a) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hrootR : R * Real.sqrt M ≤ 3 * R ^ 2 * d * Real.sqrt b := by
    nlinarith [mul_le_mul_of_nonneg_left hroot hR0]
  have hqR : R * Real.exp (-a) ≤ R * d * Real.sqrt b := by
    nlinarith [mul_le_mul_of_nonneg_left hq hR0,
      mul_le_mul_of_nonneg_left hdroot hR0]
  have hRroot : R * d * Real.sqrt b ≤ R ^ 2 * d * Real.sqrt b := by
    have hnonneg : 0 ≤ d * Real.sqrt b := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hR2 hnonneg]
  have hfirst : R * (Real.sqrt M + Real.exp (-a)) ≤
      4 * R ^ 2 * d * Real.sqrt b := by
    nlinarith [hrootR, hqR, hRroot]
  have hlast : 4 * R ^ 2 * d * Real.sqrt b ≤
      8 * R ^ 2 * Real.sqrt b * (Dnext : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hhalf
      (by positivity : 0 ≤ 4 * R ^ 2 * Real.sqrt b)
    nlinarith
  simpa only [R, d, C, k, M] using hfirst.trans hlast
/-- Integer floors retain at least half the current cap and at least the exact
exponential survival scale when `a r ≤ 1/100` and `a D ≥ 4`. -/


theorem floor_decay_bounds
    {r D Dnext : ℕ} {a : ℝ}
    (hr : 2 ≤ r) (ha : 0 ≤ a)
    (har : (r : ℝ) * a ≤ 1 / 100)
    (had : 4 ≤ a * (D : ℝ))
    (hfloor : Real.exp ((1 - (r : ℝ)) * a) * (D : ℝ) <
      (Dnext : ℝ) + 1) :
    (D : ℝ) ≤ 2 * (Dnext : ℝ) ∧
      (D : ℝ) * Real.exp (-(r : ℝ) * a) ≤ (Dnext : ℝ) := by
  let R : ℝ := r
  let d : ℝ := D
  let e : ℝ := Real.exp ((1 - R) * a)
  let q : ℝ := Real.exp (-a)
  have hR : 2 ≤ R := by dsimp [R]; exact_mod_cast hr
  have ha1 : a ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith : (0:ℝ) ≤ R-1)) ha]
  have hdpos : 0 < d := by
    by_contra h
    have hdle : d ≤ 0 := le_of_not_gt h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ha hdle]
  have hd4 : 4 ≤ d := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hdpos.le]
  have he : 3 / 4 ≤ e := by
    have h := Real.add_one_le_exp ((1 - R) * a)
    dsimp [e]
    nlinarith [h, har, ha]
  have hepos : 0 < e := by dsimp [e]; positivity
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hExp := Real.add_one_le_exp a
  have hqmul : (1 + a) * q ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hExp hqpos.le
    have hcancel : Real.exp a * q = 1 := by
      dsimp [q]
      rw [← Real.exp_add]
      simp
    nlinarith
  have hbound : 1 ≤ (1 + a) * (1 - a / 2) := by
    nlinarith [mul_nonneg ha (sub_nonneg.mpr ha1)]
  have hqgap : q ≤ 1 - a / 2 := by
    have hpos : 0 < 1 + a := by linarith
    apply le_of_mul_le_mul_left _ hpos
    nlinarith [hqmul, hbound]
  have hed : (3 / 4) * d ≤ e * d :=
    mul_le_mul_of_nonneg_right he hdpos.le
  have hfloor' : e * d < (Dnext : ℝ) + 1 := hfloor
  have hhalf : d ≤ 2 * (Dnext : ℝ) := by nlinarith [hed, hd4, hfloor']
  have hgap : a / 2 ≤ 1 - q := by linarith [hqgap]
  have hgap0 : 0 ≤ 1 - q := by linarith
  have hprod : 3 * a / 8 ≤ e * (1 - q) := by
    have h := mul_nonneg (sub_nonneg.mpr he) hgap0
    have h' := mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (sub_nonneg.mpr hgap)
    nlinarith
  have hprodD : 1 ≤ e * (1 - q) * d := by
    have h := mul_le_mul_of_nonneg_right hprod hdpos.le
    nlinarith [had, h]
  have hexp : e * q = Real.exp (-R * a) := by
    dsimp [e,q]
    rw [← Real.exp_add]
    congr 1
    ring
  constructor
  · simpa only [d] using hhalf
  · rw [← hexp]
    nlinarith [hfloor', hprodD]


/-- Explicit numerical hypotheses needed by every round of the finite
matching iteration. These are discharged by the paper's parameter choices. -/
structure MatchingSchedule (r B T : ℕ) (D : ℕ → ℕ)
    (a δ : ℝ) : Prop where
  rank_pos : 1 ≤ r
  rate_nonneg : 0 ≤ a
  error_nonneg : 0 ≤ δ
  degree_pos : ∀ i ≤ T, 0 < D i
  small : ∀ i < T,
    (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
      ((B : ℝ) * (a / (D i : ℝ))) ≤ 1
  threshold : ∀ i < T,
    (D i : ℝ) * Real.exp (a - (r : ℝ) * a) ≤
      (D (i + 1) : ℝ) + 1
  scale : ∀ i < T,
    (D (i + 1) : ℝ) * Real.exp (-a) ≤
      (D i : ℝ) * Real.exp (-((r : ℝ) * a))
  lower : ∀ i < T,
    (D i : ℝ) * Real.exp (-((r : ℝ) * a)) ≤ D (i + 1)
  error : ∀ i < T,
    (r : ℝ) *
      (Real.sqrt
        ((D i : ℝ) ^ 2 *
            (2 * ((((2 * r - 1 : ℕ) : ℝ) ^ 2) *
              ((B : ℝ) * (a / (D i : ℝ))))) +
          ((B * (r * D i) : ℕ) : ℝ)) +
        Real.exp (-a)) ≤ δ * (D (i + 1) : ℝ)

/-- Build a matching schedule from simple cap decay and codegree-ratio
bounds. Only one scalar smallness check and one scalar error budget remain. -/
theorem matchingSchedule_of_degree_bounds
    {r B T : ℕ} {D : ℕ → ℕ} {a δ b : ℝ}
    (hr : 2 ≤ r) (hB : 1 ≤ B)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hsmallBase :
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) * a * b ≤ 1)
    (hdelta : 8 * (r : ℝ) ^ 2 * Real.sqrt b ≤ δ)
    (hDpos : ∀ i ≤ T, 0 < D i)
    (hRatio : ∀ i < T, (B : ℝ) / (D i : ℝ) ≤ b)
    (hHalf : ∀ i < T, (D i : ℝ) ≤ 2 * (D (i + 1) : ℝ))
    (hThreshold : ∀ i < T,
      (D i : ℝ) * Real.exp (a - (r : ℝ) * a) ≤
        (D (i + 1) : ℝ) + 1)
    (hScale : ∀ i < T,
      (D (i + 1) : ℝ) * Real.exp (-a) ≤
        (D i : ℝ) * Real.exp (-((r : ℝ) * a)))
    (hLower : ∀ i < T,
      (D i : ℝ) * Real.exp (-((r : ℝ) * a)) ≤ D (i + 1)) :
    MatchingSchedule r B T D a δ := by
  have hδ : 0 ≤ δ := by
    have hnonneg : 0 ≤ 8 * (r : ℝ) ^ 2 * Real.sqrt b := by positivity
    linarith
  refine {
    rank_pos := by omega
    rate_nonneg := ha
    error_nonneg := hδ
    degree_pos := hDpos
    small := ?_
    threshold := hThreshold
    scale := hScale
    lower := hLower
    error := ?_
  }
  · intro i hi
    let k : ℝ := (2 * r - 1 : ℕ)
    have hka : 0 ≤ k ^ 2 * a := by positivity
    have hratio' := hRatio i hi
    have hmul := mul_le_mul_of_nonneg_left hratio' hka
    have hident : k ^ 2 * ((B : ℝ) * (a / (D i : ℝ))) =
        (k ^ 2 * a) * ((B : ℝ) / (D i : ℝ)) := by ring
    rw [hident]
    nlinarith [hmul, hsmallBase]
  · intro i hi
    have hround := one_round_error_le_eight hr hB
      (hDpos i hi.le) ha ha1 hb hb1 (hRatio i hi) (hHalf i hi)
    have hscale := mul_le_mul_of_nonneg_right hdelta
      (Nat.cast_nonneg (D (i + 1)) : (0 : ℝ) ≤ D (i + 1))
    exact hround.trans (by nlinarith [hscale])
/-- A floor recurrence supplies both half-degree preservation and the
exponential lower cap once `a D_i ≥ 4`. -/
theorem matchingSchedule_of_floor_bounds
    {r B T : ℕ} {D : ℕ → ℕ} {a δ b : ℝ}
    (hr : 2 ≤ r) (hB : 1 ≤ B)
    (ha : 0 ≤ a) (har : (r : ℝ) * a ≤ 1 / 100)
    (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hsmallBase :
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) * a * b ≤ 1)
    (hdelta : 8 * (r : ℝ) ^ 2 * Real.sqrt b ≤ δ)
    (hDpos : ∀ i ≤ T, 0 < D i)
    (hRatio : ∀ i < T, (B : ℝ) / (D i : ℝ) ≤ b)
    (haD : ∀ i < T, 4 ≤ a * (D i : ℝ))
    (hFloor : ∀ i < T,
      Real.exp ((1 - (r : ℝ)) * a) * (D i : ℝ) <
        (D (i + 1) : ℝ) + 1)
    (hScale : ∀ i < T,
      (D (i + 1) : ℝ) * Real.exp (-a) ≤
        (D i : ℝ) * Real.exp (-((r : ℝ) * a))) :
    MatchingSchedule r B T D a δ := by
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have ha1 : a ≤ 1 := by
    have h := mul_nonneg (by linarith : (0 : ℝ) ≤ (r : ℝ) - 1) ha
    nlinarith [har, h]
  apply matchingSchedule_of_degree_bounds hr hB ha ha1 hb hb1
    hsmallBase hdelta hDpos hRatio
  · intro i hi
    exact (floor_decay_bounds hr ha har (haD i hi) (hFloor i hi)).1
  · intro i hi
    have h := (hFloor i hi).le
    rw [sub_mul, one_mul] at h
    simpa only [mul_comm (Real.exp (a - (r : ℝ) * a)) (D i : ℝ)] using h
  · exact hScale
  · intro i hi
    simpa only [neg_mul] using
      (floor_decay_bounds hr ha har (haD i hi) (hFloor i hi)).2
/-- Iterate favorable marking choices through the full finite horizon. -/
theorem exists_terminal_state
    (H₀ : IndexedHypergraph V E)
    {r B T : ℕ} {D : ℕ → ℕ} {a δ : ℝ}
    (hsched : MatchingSchedule r B T D a δ)
    (hunif : H₀.IsUniform r)
    (hcap : ∀ v ∈ H₀.vertices, H₀.degree v ≤ D 0)
    (hB : H₀.maxCodegree ≤ B) :
    ∃ s : MatchingState H₀ r B D T,
      s.potential (Real.exp (-a)) δ a ((r : ℝ) * a ^ 2) T ≤
        (initialMatchingState H₀ D hunif hcap hB).potential
          (Real.exp (-a)) δ a ((r : ℝ) * a ^ 2) T := by
  let s₀ := initialMatchingState H₀ D hunif hcap hB
  have hiterate : ∀ i ≤ T,
      ∃ s : MatchingState H₀ r B D i,
        s.potential (Real.exp (-a)) δ a ((r : ℝ) * a ^ 2) T ≤
          s₀.potential (Real.exp (-a)) δ a ((r : ℝ) * a ^ 2) T := by
    intro i hi
    induction i with
    | zero =>
        exact ⟨s₀, le_refl _⟩
    | succ i ih =>
        have hiT : i < T := by omega
        obtain ⟨s, hs⟩ := ih (by omega)
        obtain ⟨ω, hstep⟩ :=
          s.exists_next_potential_le T hiT
            hsched.rate_nonneg hsched.error_nonneg hsched.rank_pos
            (hsched.degree_pos i hiT.le)
            (hsched.degree_pos (i + 1) (by omega))
            (hsched.small i hiT) (hsched.threshold i hiT)
            (hsched.scale i hiT) (hsched.lower i hiT)
            (hsched.error i hiT)
        exact ⟨s.next ω, hstep.trans hs⟩
  simpa only [s₀] using hiterate T le_rfl
/-- A valid finite schedule yields a matching whose uncovered vertices are
bounded by the initial backward potential. -/
theorem exists_matching_coverage_bound
    (H₀ : IndexedHypergraph V E)
    {r B T : ℕ} {D : ℕ → ℕ} {a δ : ℝ}
    (hsched : MatchingSchedule r B T D a δ)
    (hunif : H₀.IsUniform r)
    (hcap : ∀ v ∈ H₀.vertices, H₀.degree v ≤ D 0)
    (hB : H₀.maxCodegree ≤ B) :
    ∃ M : Finset E, H₀.IsMatching M ∧
      (H₀.vertices.card : ℝ) - (H₀.covered M).card ≤
        Theorem2.lossPotentialA (Real.exp (-a)) δ a ((r : ℝ) * a ^ 2) T 0 *
          (H₀.vertices.card : ℝ) +
        Theorem2.lossPotentialB a T 0 *
          ((H₀.degreeDeficit (D 0) : ℝ) / (D 0 : ℝ)) := by
  obtain ⟨s, hpot⟩ :=
    exists_terminal_state H₀ hsched hunif hcap hB
  have hterminal :
      s.potential (Real.exp (-a)) δ a ((r : ℝ) * a ^ 2) T =
        (s.residual.vertices.card : ℝ) + (s.wasted : ℝ) := by
    simp [MatchingState.potential,
      Theorem2.lossPotentialA_terminal, Theorem2.lossPotentialB_terminal]
  have hinitial :
      (initialMatchingState H₀ D hunif hcap hB).potential
          (Real.exp (-a)) δ a ((r : ℝ) * a ^ 2) T =
        Theorem2.lossPotentialA (Real.exp (-a)) δ a ((r : ℝ) * a ^ 2) T 0 *
          (H₀.vertices.card : ℝ) +
        Theorem2.lossPotentialB a T 0 *
          ((H₀.degreeDeficit (D 0) : ℝ) / (D 0 : ℝ)) := by
    simp [MatchingState.potential, initialMatchingState]
  rw [hterminal, hinitial] at hpot
  have hpart :
      (H₀.covered s.accepted).card + s.residual.vertices.card + s.wasted =
        H₀.vertices.card := s.partition_card
  have hpartReal :
      ((H₀.covered s.accepted).card : ℝ) +
          (s.residual.vertices.card : ℝ) + (s.wasted : ℝ) =
        (H₀.vertices.card : ℝ) := by exact_mod_cast hpart
  exact ⟨s.accepted, s.accepted_matching, by linarith⟩

/-- The nearly-perfect matching conclusion once the explicit initial
potential is at most the requested uncovered-vertex budget. -/
theorem exists_almostPerfectMatching_of_schedule
    (H₀ : IndexedHypergraph V E)
    {r B T : ℕ} {D : ℕ → ℕ} {a δ ξ : ℝ}
    (hsched : MatchingSchedule r B T D a δ)
    (hunif : H₀.IsUniform r)
    (hcap : ∀ v ∈ H₀.vertices, H₀.degree v ≤ D 0)
    (hB : H₀.maxCodegree ≤ B)
    (hbudget :
      Theorem2.lossPotentialA (Real.exp (-a)) δ a ((r : ℝ) * a ^ 2) T 0 *
          (H₀.vertices.card : ℝ) +
        Theorem2.lossPotentialB a T 0 *
          ((H₀.degreeDeficit (D 0) : ℝ) / (D 0 : ℝ)) ≤
        ξ * (H₀.vertices.card : ℝ)) :
    ∃ M : Finset E, H₀.IsMatching M ∧
      (1 - ξ) * (H₀.vertices.card : ℝ) ≤ (H₀.covered M).card := by
  obtain ⟨M, hM, hcover⟩ :=
    exists_matching_coverage_bound H₀ hsched hunif hcap hB
  exact ⟨M, hM, by nlinarith⟩
omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- Near-regular minimum degree bounds the initial deficit after
normalizing by the maximum degree. -/
theorem normalized_degreeDeficit_le
    (H : IndexedHypergraph V E) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {μ : ℝ}
    (hmin : ∀ v ∈ H.vertices,
      (1 - μ) * (D : ℝ) ≤ (H.degree v : ℝ)) :
    (H.degreeDeficit D : ℝ) / (D : ℝ) ≤
      μ * (H.vertices.card : ℝ) := by
  have hsum : (H.degreeDeficit D : ℝ) ≤
      H.vertices.sum (fun _ => μ * (D : ℝ)) := by
    unfold IndexedHypergraph.degreeDeficit
    rw [Nat.cast_sum]
    apply Finset.sum_le_sum
    intro v hv
    rw [Nat.cast_sub (hcap v hv)]
    nlinarith [hmin v hv]
  have hsum' : (H.degreeDeficit D : ℝ) ≤
      μ * (H.vertices.card : ℝ) * (D : ℝ) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hsum
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  exact (div_le_iff₀ hDreal).mpr hsum'
/-- A coarse initial-potential budget, separating survivor decay, cumulative
waste/deficit error, and the initial degree shortfall. -/
theorem initial_potential_budget
    (T : ℕ) (N z₀ q δ a β L μ ξ : ℝ)
    (hN : 0 ≤ N) (hμ : 0 ≤ μ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hδ : 0 ≤ δ) (ha : 0 ≤ a) (hβ : 0 ≤ β)
    (hqT : q ^ T ≤ ξ / 4)
    (hError : δ * a * (T : ℝ) ^ 2 + β * (T : ℝ) ≤ ξ / 2)
    (hDeficit : z₀ ≤ μ * N)
    (haT : a * (T : ℝ) ≤ 2 * L)
    (hInitial : 2 * L * μ ≤ ξ / 4) :
    Theorem2.lossPotentialA q δ a β T 0 * N +
      Theorem2.lossPotentialB a T 0 * z₀ ≤ ξ * N := by
  have hA := Theorem2.lossPotentialA_zero_le q δ a β
    hq0 hq1 hδ ha hβ T
  have hB := Theorem2.lossPotentialB_zero a T
  have hA' := mul_le_mul_of_nonneg_right hA hN
  have hqT' := mul_le_mul_of_nonneg_right hqT hN
  have hError' := mul_le_mul_of_nonneg_right hError hN
  have haT0 : 0 ≤ a * (T : ℝ) := by positivity
  have hDeficit' := mul_le_mul_of_nonneg_left hDeficit haT0
  have hμN : 0 ≤ μ * N := mul_nonneg hμ hN
  have haT' := mul_le_mul_of_nonneg_right haT hμN
  have hInitial' := mul_le_mul_of_nonneg_right hInitial hN
  rw [hB]
  nlinarith [hA', hqT', hError', hDeficit', haT', hInitial']
end Probability

end MatchingRound
end HadwigerLean
