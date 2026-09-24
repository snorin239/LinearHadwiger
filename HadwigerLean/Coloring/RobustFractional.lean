import HadwigerLean.Graph.WeightedMatching
import HadwigerLean.Coloring.FractionalLP
import HadwigerLean.ReedSeymour.Theorem

/-!
# Fractional-coloring transfer through matching contraction

The contraction argument uses the minimum of the two endpoint weights on each
matching pair.  The combinatorial input is an independent transversal for
every quotient-stable family of pairs.  It will eventually be supplied by the
short-cycle-free matching and independent-transversal lemmas.
-/

namespace HadwigerLean

open Finset

namespace IndexedMatching

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
  {G H : SimpleGraph V}

/-- The dual weight attached to a contracted matching pair. -/
noncomputable def minWeight (M : IndexedMatching G I) (w : V → ℝ) (i : I) : ℝ :=
  min (w (M.endpoint i false)) (w (M.endpoint i true))
/-- The vertices covered by the matching. -/
noncomputable def matchedVertices (M : IndexedMatching G I) : Finset V :=
  Finset.univ.image fun p : I × Bool => M.endpoint p.1 p.2

/-- The vertices left unmatched by the indexed matching. -/
noncomputable def unmatchedVertices (M : IndexedMatching G I) : Finset V :=
  Finset.univ \ M.matchedVertices

omit [Fintype V] [DecidableEq I] in
/-- A vertex is covered by an indexed matching exactly when it has a
matching-graph neighbor. -/
theorem mem_matchedVertices_iff (M : IndexedMatching G I) (x : V) :
    x ∈ M.matchedVertices ↔ ∃ y, M.edgeGraph.Adj x y := by
  classical
  constructor
  · intro hx
    obtain ⟨⟨i, b⟩, _, rfl⟩ := Finset.mem_image.mp hx
    cases b with
    | false => exact ⟨M.endpoint i true, M.edgeGraph_adj_endpoints i⟩
    | true => exact ⟨M.endpoint i false, (M.edgeGraph_adj_endpoints i).symm⟩
  · rintro ⟨y, i, hxy⟩
    rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact Finset.mem_image.mpr ⟨(i, false), Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨(i, true), Finset.mem_univ _, rfl⟩
omit [Fintype V] [DecidableEq I] in
theorem sum_matchedVertices (M : IndexedMatching G I) (w : V → ℝ) :
    ∑ v ∈ M.matchedVertices, w v =
      ∑ i : I, (w (M.endpoint i false) + w (M.endpoint i true)) := by
  classical
  rw [matchedVertices, Finset.sum_image (fun i _ j _ hij => M.injective hij)]
  simp [Fintype.sum_prod_type, add_comm]

omit [DecidableEq I] in
theorem sum_vertices_split (M : IndexedMatching G I) (w : V → ℝ) :
    ∑ v : V, w v =
      (∑ i : I, (w (M.endpoint i false) + w (M.endpoint i true))) +
        ∑ v ∈ M.unmatchedVertices, w v := by
  classical
  rw [← Finset.sum_add_sum_compl M.matchedVertices]
  rw [Finset.compl_eq_univ_sdiff]
  simp only [unmatchedVertices]
  rw [M.sum_matchedVertices w]

/-- All matching pairs in a quotient-stable family admit a stable selection in `H`. -/
def HasStableTransversals (M : IndexedMatching G I) (H : SimpleGraph V) : Prop :=
  ∀ S : StableSet M.quotient,
    ∃ c : I → Bool,
      H.IsIndepSet
        ((S.1.image fun i => M.endpoint i (c i)) : Set V)

omit [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] in
private theorem chosen_injective (M : IndexedMatching G I) (c : I → Bool) :
    Function.Injective (fun i => M.endpoint i (c i)) := by
  intro i j hij
  have hp : (i, c i) = (j, c j) := M.injective hij
  exact congrArg Prod.fst hp

omit [Fintype V] [Fintype I] [DecidableEq I] in
/-- The minimum endpoint weights satisfy every quotient dual constraint
whenever each stable family of matching pairs has a stable transversal. -/
theorem minWeight_dualFeasible (M : IndexedMatching G I)
    (w : V → ℝ) (hw : IsFractionalDualFeasible H w)
    (htrans : M.HasStableTransversals H) :
    IsFractionalDualFeasible M.quotient (M.minWeight w) := by
  classical
  constructor
  · intro i
    exact le_min (hw.1 _) (hw.1 _)
  · intro S
    obtain ⟨c, hc⟩ := htrans S
    let T : Finset V := S.1.image fun i => M.endpoint i (c i)
    have hT : T.Nonempty := S.property.1.image _
    let TS : StableSet H := ⟨T, hT, hc⟩
    have hselected : (∑ i ∈ S.1, w (M.endpoint i (c i))) =
        ∑ v ∈ T, w v := by
      simp only [T]
      exact (Finset.sum_image (fun i _ j _ hij => chosen_injective M c hij)).symm
    calc
      (∑ i ∈ S.1, M.minWeight w i) ≤
          ∑ i ∈ S.1, w (M.endpoint i (c i)) := by
            apply Finset.sum_le_sum
            intro i hi
            cases c i <;> simp [minWeight]
      _ = ∑ v ∈ T, w v := hselected
      _ ≤ 1 := hw.2 TS

private theorem twice_min_add_abs (a b : ℝ) :
    2 * min a b + |a - b| = a + b := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  · rw [min_eq_right hba, abs_of_nonneg (sub_nonneg.mpr hba)]
    ring

omit [Fintype V] [DecidableEq V] [DecidableEq I] in
theorem sum_minWeight_identity (M : IndexedMatching G I) (w : V → ℝ) :
    2 * (∑ i : I, M.minWeight w i) +
      ∑ i : I, |w (M.endpoint i false) - w (M.endpoint i true)| =
        ∑ i : I, (w (M.endpoint i false) + w (M.endpoint i true)) := by
  classical
  calc
    _ = ∑ i : I, (2 * M.minWeight w i +
        |w (M.endpoint i false) - w (M.endpoint i true)|) := by
          rw [Finset.mul_sum, Finset.sum_add_distrib]
    _ = ∑ i : I, (w (M.endpoint i false) + w (M.endpoint i true)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact twice_min_add_abs _ _

/-- The analytic part of the robust bound.  The only missing combinatorial
ingredients are a matching with small unmatched set and weight loss, and
independent transversals for quotient-stable families of its pairs. -/
theorem robust_bound_of_matching_certificate
    (M : IndexedMatching G I)
    (w : V → ℝ)
    (hw : IsFractionalDualFeasible H w)
    (hopt : fractionalDualValue w = fractionalChromaticNumber H)
    (htrans : M.HasStableTransversals H)
    (U L : ℝ)
    (hunmatched : (M.unmatchedVertices.card : ℝ) ≤ U)
    (hloss :
      (∑ i : I, |w (M.endpoint i false) - w (M.endpoint i true)|) ≤ L) :
    fractionalChromaticNumber H ≤
      4 * (cliqueMinorNumber G : ℝ) + U + L := by
  classical
  have hdual : (∑ i : I, M.minWeight w i) ≤
      fractionalChromaticNumber M.quotient :=
    fractionalDualValue_le_chromatic M.quotient
      (M.minWeight_dualFeasible w hw htrans)
  have hminor : (cliqueMinorNumber M.quotient : ℝ) ≤
      (cliqueMinorNumber G : ℝ) := by
    exact_mod_cast M.quotient_cliqueMinorNumber_le
  have hreed : fractionalChromaticNumber M.quotient ≤
      2 * (cliqueMinorNumber M.quotient : ℝ) :=
    ReedSeymour.reed_seymour_bound M.quotient
  have hsingle : (∑ v ∈ M.unmatchedVertices, w v) ≤ U := by
    calc
      (∑ v ∈ M.unmatchedVertices, w v) ≤
          ∑ v ∈ M.unmatchedVertices, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro v _
            exact dual_weight_le_one H hw v
      _ = (M.unmatchedVertices.card : ℝ) := by simp
      _ ≤ U := hunmatched
  have hsum := M.sum_minWeight_identity w
  have hsplit := M.sum_vertices_split w
  unfold fractionalDualValue at hopt
  calc
    fractionalChromaticNumber H = ∑ v : V, w v := hopt.symm
    _ = (∑ i : I, (w (M.endpoint i false) + w (M.endpoint i true))) +
        ∑ v ∈ M.unmatchedVertices, w v := hsplit
    _ = 2 * (∑ i : I, M.minWeight w i) +
          (∑ i : I, |w (M.endpoint i false) - w (M.endpoint i true)|) +
          ∑ v ∈ M.unmatchedVertices, w v := by rw [← hsum]
    _ ≤ 4 * (cliqueMinorNumber G : ℝ) + U + L := by
          linarith

omit [Fintype I] [DecidableEq I] in
/-- The cycle-free partial matching supplies stable choices from every
quotient-stable family of pairs for the union graph. -/
theorem hasStableTransversals_sup_of_no_matching_cycle
    (M : IndexedMatching G I) (D : SimpleGraph V)
    (hedgeDisjoint : ∀ a b, D.Adj a b → ¬ M.edgeGraph.Adj a b)
    (hcycles : NoMatchingEdgeCycle D M.edgeGraph) :
    M.HasStableTransversals (G ⊔ D) := by
  classical
  intro S
  obtain ⟨T, _, hTind, hTcross⟩ :=
    M.independent_transversal_pairs D hedgeDisjoint hcycles S.1
  let c : I → Bool := fun i =>
    if M.endpoint i false ∈ T then false else true
  have hchosen (i : I) (hi : i ∈ S.1) : M.endpoint i (c i) ∈ T := by
    by_cases hleft : M.endpoint i false ∈ T
    · simp [c, hleft]
    · have hright : M.endpoint i true ∈ T := by
        by_contra hnot
        exact hleft ((hTcross i hi).mpr hnot)
      simpa [c, hleft] using hright
  refine ⟨c, ?_⟩
  intro x hx y hy hne hadj
  change x ∈ S.1.image (fun i => M.endpoint i (c i)) at hx
  change y ∈ S.1.image (fun i => M.endpoint i (c i)) at hy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
  rcases (SimpleGraph.sup_adj G D _ _).mp hadj with hGadj | hDadj
  · have hij : i ≠ j := by
      intro h
      subst j
      exact hne rfl
    have hquot : M.quotient.Adj i j :=
      (M.quotient_adj_iff i j).mpr
        ⟨hij, c i, c j, hGadj⟩
    exact S.property.2 hi hj hij hquot
  · exact hTind (hchosen i hi) (hchosen j hj) hne hDadj

omit [Fintype I] [DecidableEq I] in
/-- A stable family of contracted pairs has at most the independence number
of the original graph. -/
theorem quotient_stable_card_le_independenceNumber
    (M : IndexedMatching G I) (S : StableSet M.quotient) :
    S.1.card ≤ independenceNumber G := by
  classical
  let T : Finset V := S.1.image (fun i => M.endpoint i false)
  have hTind : G.IsIndepSet (T : Set V) := by
    intro x hx y hy hne hxy
    change x ∈ T at hx
    change y ∈ T at hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    have hij : i ≠ j := by
      intro h
      subst j
      exact hne rfl
    have hquot : M.quotient.Adj i j :=
      (M.quotient_adj_iff i j).mpr ⟨hij, false, false, hxy⟩
    exact S.property.2 hi hj hij hquot
  calc
    S.1.card = T.card := by
      simpa [T] using
        (Finset.card_image_of_injective S.1 M.endpoint_left_injective).symm
    _ ≤ independenceNumber G := stable_card_le_independenceNumber G hTind

omit [Fintype I] [DecidableEq I] in
/-- The paper's short-cycle exclusion implies all quotient-stable pair
families admit stable representatives in G + D. -/
theorem hasStableTransversals_sup_of_short_cycles
    (M : IndexedMatching G I) (D : SimpleGraph V)
    (m L : ℕ) (halpha : independenceNumber G ≤ m)
    (hL : 2 * m ≤ L)
    (hedgeDisjoint : ∀ a b, D.Adj a b → ¬ M.edgeGraph.Adj a b)
    (hshort : ∀ (u : V) (c : (D ⊔ M.edgeGraph).Walk u u),
      c.IsCycle → c.length ≤ L →
        ∀ e ∈ c.edges, e ∉ M.edgeGraph.edgeSet) :
    M.HasStableTransversals (G ⊔ D) := by
  classical
  intro S
  have hScard : S.1.card ≤ m :=
    (M.quotient_stable_card_le_independenceNumber S).trans halpha
  have hpaircard : (M.pairVertices S.1).card ≤ L :=
    (M.pairVertices_card_le_two_mul S.1).trans
      ((Nat.mul_le_mul_left 2 hScard).trans hL)
  obtain ⟨T, _, hTind, hTcross⟩ :=
    M.independent_transversal_pairs_of_short D hedgeDisjoint
      S.1 L hpaircard hshort
  let c : I → Bool := fun i =>
    if M.endpoint i false ∈ T then false else true
  have hchosen (i : I) (hi : i ∈ S.1) : M.endpoint i (c i) ∈ T := by
    by_cases hleft : M.endpoint i false ∈ T
    · simp [c, hleft]
    · have hright : M.endpoint i true ∈ T := by
        by_contra hnot
        exact hleft ((hTcross i hi).mpr hnot)
      simpa [c, hleft] using hright
  refine ⟨c, ?_⟩
  intro x hx y hy hne hadj
  change x ∈ S.1.image (fun i => M.endpoint i (c i)) at hx
  change y ∈ S.1.image (fun i => M.endpoint i (c i)) at hy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
  rcases (SimpleGraph.sup_adj G D _ _).mp hadj with hGadj | hDadj
  · have hij : i ≠ j := by
      intro h
      subst j
      exact hne rfl
    have hquot : M.quotient.Adj i j :=
      (M.quotient_adj_iff i j).mpr
        ⟨hij, c i, c j, hGadj⟩
    exact S.property.2 hi hj hij hquot
  · exact hTind (hchosen i hi) (hchosen j hj) hne hDadj

/-- Combining the short-cycle transversal with the fractional dual transfer.
Here C is any common cap on unmatched vertices and matching weight loss. -/
theorem robust_bound_of_short_matching_certificate
    (M : IndexedMatching G I) (D : SimpleGraph V)
    (m L : ℕ) (halpha : independenceNumber G ≤ m)
    (hL : 2 * m ≤ L)
    (hdisjoint : ∀ a b, D.Adj a b → ¬ M.edgeGraph.Adj a b)
    (hshort : ∀ (u : V) (c : (D ⊔ M.edgeGraph).Walk u u),
      c.IsCycle → c.length ≤ L →
        ∀ e ∈ c.edges, e ∉ M.edgeGraph.edgeSet)
    (w : V → ℝ)
    (hw : IsFractionalDualFeasible (G ⊔ D) w)
    (hopt : fractionalDualValue w = fractionalChromaticNumber (G ⊔ D))
    (C : ℕ)
    (hunmatched : M.unmatchedVertices.card ≤ C)
    (hloss :
      (∑ i : I, |w (M.endpoint i false) - w (M.endpoint i true)|) ≤ (C : ℝ)) :
    fractionalChromaticNumber (G ⊔ D) ≤
      4 * (cliqueMinorNumber G : ℝ) + 2 * (C : ℝ) := by
  have htrans : M.HasStableTransversals (G ⊔ D) :=
    M.hasStableTransversals_sup_of_short_cycles D m L halpha hL hdisjoint hshort
  have hraw := M.robust_bound_of_matching_certificate w hw hopt
    htrans (C : ℝ) (C : ℝ) (by exact_mod_cast hunmatched) hloss
  linarith

omit [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] in
/-- A matching edge is automatically absent from D if D lies in the
complement of the graph matched. -/
theorem edgeGraph_disjoint_of_le_compl
    (M : IndexedMatching G I) (D : SimpleGraph V)
    (hD : D ≤ Gᶜ) :
    ∀ a b, D.Adj a b → ¬ M.edgeGraph.Adj a b := by
  intro a b hab hM
  exact ((SimpleGraph.compl_adj G a b).mp (hD hab)).2
    (M.edgeGraph_le hM)

/-- The robust fractional bound from a finite greedy trace certificate.
The only external combinatorial data are the matching, its processing-time
conditions, and the no-short-cycle insertion invariant. -/
theorem robust_bound_of_greedy_trace
    (M : IndexedMatching G I) (D : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel D.Adj]
    (hD : D ≤ Gᶜ)
    (m d r : ℕ) (halpha : independenceNumber G ≤ m)
    (hdegree : ∀ x, D.degree x ≤ d)
    (hR : 2 * m ≤ r + 1)
    (w : V → ℝ)
    (hw : IsFractionalDualFeasible (G ⊔ D) w)
    (hopt : fractionalDualValue w = fractionalChromaticNumber (G ⊔ D))
    (time : V → ℕ) (htime : Function.Injective time)
    (before : V → SimpleGraph V)
    (hbefore : ∀ x, before x ≤ D ⊔ M.edgeGraph)
    (horder : ∀ i, w (M.endpoint i true) ≤ w (M.endpoint i false))
    (hunmatchedIneligible : ∀ x ∈ M.unmatchedVertices,
      ∀ y ∈ M.unmatchedVertices,
      time x < time y → G.Adj x y →
      (before x).edist x y ≤ (r : ℕ∞))
    (hpartnerMaximal : ∀ i j : I,
      w (M.endpoint i true) < w (M.endpoint i false) →
      time (M.endpoint i false) < time (M.endpoint j false) →
      w (M.endpoint i true) < w (M.endpoint j false) →
      G.Adj (M.endpoint i false) (M.endpoint j false) →
      (before (M.endpoint i false)).edist
        (M.endpoint i false) (M.endpoint j false) ≤ (r : ℕ∞))
    (hshort : ∀ (u : V) (c : (D ⊔ M.edgeGraph).Walk u u),
      c.IsCycle → c.length ≤ r + 1 →
        ∀ e ∈ c.edges, e ∉ M.edgeGraph.edgeSet) :
    fractionalChromaticNumber (G ⊔ D) ≤
      4 * (cliqueMinorNumber G : ℝ) +
        2 * ((m * ((∑ n ∈ Finset.range (r + 1), (d + 1) ^ n) + 1) : ℕ) : ℝ) := by
  let C : ℕ := m * ((∑ n ∈ Finset.range (r + 1), (d + 1) ^ n) + 1)
  have hweight : ∀ v, 0 ≤ w v ∧ w v ≤ 1 := by
    intro v
    exact ⟨hw.1 v, dual_weight_le_one (G ⊔ D) hw v⟩
  obtain ⟨hX, hLoss⟩ :=
    matching_bounds_of_greedy_trace G D M M.unmatchedVertices
      time htime before hbefore d r m halpha hdegree
      w hweight horder hunmatchedIneligible hpartnerMaximal
  have hdisj : ∀ a b, D.Adj a b → ¬ M.edgeGraph.Adj a b :=
    M.edgeGraph_disjoint_of_le_compl D hD
  have hshort2m : ∀ (u : V) (c : (D ⊔ M.edgeGraph).Walk u u),
      c.IsCycle → c.length ≤ 2 * m →
        ∀ e ∈ c.edges, e ∉ M.edgeGraph.edgeSet := by
    intro u c hc hlen
    exact hshort u c hc (hlen.trans hR)
  exact M.robust_bound_of_short_matching_certificate D m (2 * m)
    halpha le_rfl hdisj hshort2m w hw hopt C hX hLoss
end IndexedMatching

private noncomputable instance finiteGraphEdgeSetFintype
    {V : Type*} [Fintype V] (P : SimpleGraph V) : Fintype P.edgeSet :=
  Fintype.ofFinite _
/-- The set-aside vertices recorded by the finite greedy run are precisely
the unmatched vertices of its indexed matching. -/
theorem weightedGreedyFullMatching_unmatched_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ) :
    (weightedGreedyFullMatching G D w r).unmatchedVertices =
      (weightedGreedyFullRun G D w r).unmatched := by
  classical
  ext x
  simp only [IndexedMatching.unmatchedVertices, Finset.mem_sdiff,
    Finset.mem_univ, true_and]
  rw [IndexedMatching.mem_matchedVertices_iff,
    weightedGreedyFullMatching_edgeGraph_eq]
  exact (weightedGreedyFullRun_mem_unmatched_iff G D w r x).symm
theorem IndexedMatching.unmatchedVertices_eq_of_edgeGraph_eq
    {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V]
    {G : SimpleGraph V} (M N : IndexedMatching G I)
    (hgraph : M.edgeGraph = N.edgeGraph) :
    M.unmatchedVertices = N.unmatchedVertices := by
  classical
  ext x
  simp only [IndexedMatching.unmatchedVertices, Finset.mem_sdiff,
    Finset.mem_univ, true_and]
  rw [M.mem_matchedVertices_iff, N.mem_matchedVertices_iff, hgraph]

theorem weightedGreedyFullMatchingSorted_unmatched_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ) :
    (weightedGreedyFullMatchingSorted G D w r).unmatchedVertices =
      (weightedGreedyFullRun G D w r).unmatched := by
  rw [IndexedMatching.unmatchedVertices_eq_of_edgeGraph_eq
    (weightedGreedyFullMatchingSorted G D w r)
    (weightedGreedyFullMatching G D w r)
    (by rw [weightedGreedyFullMatchingSorted_edgeGraph_eq,
      weightedGreedyFullMatching_edgeGraph_eq])]
  exact weightedGreedyFullMatching_unmatched_eq G D w r

/-- The finite greedy matching gives the robust fractional bound at any
radius that covers the short cycles needed by the transversal argument. -/
theorem robust_fractional_bound_at_radius
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (hD : D ≤ Gᶜ) (m d r : ℕ)
    (halpha : independenceNumber G ≤ m)
    (hdegree : ∀ x, D.degree x ≤ d)
    (hR : 2 * m ≤ r + 1) :
    fractionalChromaticNumber (G ⊔ D) ≤
      4 * (cliqueMinorNumber G : ℝ) +
        2 * ((m * ((∑ n ∈ Finset.range (r + 1), (d + 1) ^ n) + 1) : ℕ) : ℝ) := by
  classical
  obtain ⟨w, hw, hopt⟩ := exists_fractionalDual_optimum (G ⊔ D)
  let M := weightedGreedyFullMatchingSorted G D w r
  let C : ℕ := m * ((∑ n ∈ Finset.range (r + 1), (d + 1) ^ n) + 1)
  have hweight : ∀ v, 0 ≤ w v ∧ w v ≤ 1 := by
    intro v
    exact ⟨hw.1 v, dual_weight_le_one (G ⊔ D) hw v⟩
  obtain ⟨hX, hLoss⟩ :=
    weightedGreedyFullMatchingSorted_bounds G D w d r m halpha hdegree hweight
  have hX' : M.unmatchedVertices.card ≤ C := by
    rw [weightedGreedyFullMatchingSorted_unmatched_eq]
    exact hX
  have hdisj : ∀ a b, D.Adj a b → ¬ M.edgeGraph.Adj a b :=
    M.edgeGraph_disjoint_of_le_compl D hD
  have hshort : ∀ (u : V) (c : (D ⊔ M.edgeGraph).Walk u u),
      c.IsCycle → c.length ≤ r + 1 →
        ∀ e ∈ c.edges, e ∉ M.edgeGraph.edgeSet := by
    exact weightedGreedyFullMatchingSorted_noShortMatchingCycle G D w r
  have hLoss' :
      (∑ i : (weightedGreedyFullRun G D w r).matching.edgeSet,
        |w (M.endpoint i false) - w (M.endpoint i true)|) ≤ (C : ℝ) := hLoss
  simpa only [C] using
    (M.robust_bound_of_short_matching_certificate D m (r + 1)
      halpha hR hdisj hshort w hw hopt C hX' hLoss')

/-- A version with the radius and additive term used in Theorem 2. -/
theorem robust_fractional_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (hD : D ≤ Gᶜ) (m d : ℕ)
    (hm : 1 ≤ m)
    (halpha : independenceNumber G ≤ m)
    (hdegree : ∀ x, D.degree x ≤ d) :
    fractionalChromaticNumber (G ⊔ D) ≤
      4 * (cliqueMinorNumber G : ℝ) +
        2 * ((m * ((∑ n ∈ Finset.range (2 * m), (d + 1) ^ n) + 1) : ℕ) : ℝ) := by
  have hr : (2 * m - 1) + 1 = 2 * m := by omega
  simpa only [hr] using
    robust_fractional_bound_at_radius G D hD m d (2 * m - 1)
      halpha hdegree (by omega)

/-- The robust bound in terms of the added graph's maximum degree. -/
theorem robust_fractional_bound_maxDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (hD : D ≤ Gᶜ) (m d : ℕ)
    (hm : 1 ≤ m)
    (halpha : independenceNumber G ≤ m)
    (hdegree : D.maxDegree ≤ d) :
    fractionalChromaticNumber (G ⊔ D) ≤
      4 * (cliqueMinorNumber G : ℝ) +
        2 * ((m * ((∑ n ∈ Finset.range (2 * m), (d + 1) ^ n) + 1) : ℕ) : ℝ) := by
  apply robust_fractional_bound G D hD m d hm halpha
  intro x
  exact (D.degree_le_maxDegree x).trans hdegree
end HadwigerLean
