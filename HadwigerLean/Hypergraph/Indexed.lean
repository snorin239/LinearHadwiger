import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
Finite multihypergraphs with indexed edge copies.

The edge labels distinguish repeated edges. A residual hypergraph retains the
same ambient vertex and edge label types while changing its active finite sets.
-/

namespace HadwigerLean

/-- A finite hypergraph whose edge copies are indexed by `E`. -/
structure IndexedHypergraph (V E : Type*) where
  vertices : Finset V
  edges : Finset E
  edge : E → Finset V
  edge_subset : ∀ e ∈ edges, edge e ⊆ vertices

namespace IndexedHypergraph

variable {V E : Type*} [DecidableEq V]
variable (H : IndexedHypergraph V E)

/-- Number of active copies incident with `v`. -/
def degree (v : V) : ℕ := (H.edges.filter fun e => v ∈ H.edge e).card

/-- Number of active copies incident with both `u` and `v`. -/
def codegree (u v : V) : ℕ :=
  (H.edges.filter fun e => u ∈ H.edge e ∧ v ∈ H.edge e).card

/-- Maximum active degree, zero for an empty vertex set. -/
def maxDegree : ℕ := H.vertices.sup H.degree

/-- Maximum codegree over distinct active vertices. -/
def maxCodegree : ℕ :=
  H.vertices.sup (fun u => (H.vertices.erase u).sup (H.codegree u))

/-- Every active edge copy has cardinality r. -/
def IsUniform (r : ℕ) : Prop := ∀ e ∈ H.edges, (H.edge e).card = r

/-- The active copies in `M` have disjoint vertex sets. -/
def IsMatching (M : Finset E) : Prop :=
  M ⊆ H.edges ∧ Set.Pairwise (M : Set E) (fun e f => Disjoint (H.edge e) (H.edge f))

/-- Vertices covered by a collection of edge copies. -/
def covered (M : Finset E) : Finset V := M.biUnion H.edge

/-- The total shortfall from a proposed degree cap. -/
def degreeDeficit (D : ℕ) : ℕ :=
  H.vertices.sum (fun v => D - H.degree v)

/-- The total excess above a proposed degree cap. -/
def degreeExcess (D : ℕ) : ℕ :=
  H.vertices.sum (fun v => H.degree v - D)

/-- Discard active edge copies, preserving the ambient label types. -/
def restrictEdges (F : Finset E) (hF : F ⊆ H.edges) : IndexedHypergraph V E where
  vertices := H.vertices
  edges := F
  edge := H.edge
  edge_subset := by
    intro e he
    exact H.edge_subset e (hF he)

/-- Induce on a finite vertex set, retaining exactly the edge copies inside it. -/
def induce (U : Finset V) : IndexedHypergraph V E where
  vertices := H.vertices ∩ U
  edges := H.edges.filter (fun e => H.edge e ⊆ U)
  edge := H.edge
  edge_subset := by
    intro e he
    rcases Finset.mem_filter.mp he with ⟨heH, heU⟩
    exact Finset.subset_inter (H.edge_subset e heH) heU

omit [DecidableEq V] in
@[simp] theorem restrictEdges_vertices (F : Finset E) (hF : F ⊆ H.edges) :
    (H.restrictEdges F hF).vertices = H.vertices := rfl

omit [DecidableEq V] in
omit [DecidableEq V] in
@[simp] theorem restrictEdges_edges (F : Finset E) (hF : F ⊆ H.edges) :
    (H.restrictEdges F hF).edges = F := rfl

omit [DecidableEq V] in
@[simp] theorem restrictEdges_edge (F : Finset E) (hF : F ⊆ H.edges) (e : E) :
    (H.restrictEdges F hF).edge e = H.edge e := rfl

theorem restrictEdges_degree_le (F : Finset E) (hF : F ⊆ H.edges) (v : V) :
    (H.restrictEdges F hF).degree v ≤ H.degree v := by
  unfold degree
  simp only [restrictEdges_edges]
  exact Finset.card_le_card (Finset.filter_subset_filter _ hF)

theorem restrictEdges_codegree_le (F : Finset E) (hF : F ⊆ H.edges) (u v : V) :
    (H.restrictEdges F hF).codegree u v ≤ H.codegree u v := by
  unfold codegree
  simp only [restrictEdges_edges]
  exact Finset.card_le_card (Finset.filter_subset_filter _ hF)

theorem degree_eq_zero_of_not_mem {v : V} (hv : v ∉ H.vertices) : H.degree v = 0 := by
  classical
  unfold degree
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro e heH hve
  exact hv (H.edge_subset e heH hve)

theorem degree_le_maxDegree {v : V} (hv : v ∈ H.vertices) :
    H.degree v ≤ H.maxDegree := Finset.le_sup hv

theorem codegree_le_maxCodegree {u v : V}
    (hu : u ∈ H.vertices) (hv : v ∈ H.vertices) (hne : u ≠ v) :
    H.codegree u v ≤ H.maxCodegree := by
  unfold maxCodegree
  have hinner : H.codegree u v ≤
      (H.vertices.erase u).sup (H.codegree u) :=
    Finset.le_sup (Finset.mem_erase.mpr ⟨hne.symm, hv⟩)
  exact hinner.trans (Finset.le_sup (f := fun w => (H.vertices.erase w).sup (H.codegree w)) hu)

/-- An active edge of uniform rank at least two gives a positive codegree. -/
theorem maxCodegree_pos_of_maxDegree_pos (H : IndexedHypergraph V E)
    {r : ℕ} (hr : 2 ≤ r) (hunif : H.IsUniform r)
    (hdegree : 0 < H.maxDegree) : 0 < H.maxCodegree := by
  classical
  have hE : H.edges.Nonempty := by
    by_contra h
    have he : H.edges = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [IndexedHypergraph.maxDegree, IndexedHypergraph.degree, he] at hdegree
  obtain ⟨e, he⟩ := hE
  have hcard : 1 < (H.edge e).card := by rw [hunif e he]; omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcard
  have hsub := H.edge_subset e he
  have hcodeg : 0 < H.codegree u v := by
    unfold IndexedHypergraph.codegree
    apply Finset.card_pos.mpr
    exact ⟨e, Finset.mem_filter.mpr ⟨he, hu, hv⟩⟩
  exact lt_of_lt_of_le hcodeg
    (H.codegree_le_maxCodegree (hsub hu) (hsub hv) huv)
theorem codegree_le_degree_left (u v : V) : H.codegree u v ≤ H.degree u := by
  unfold codegree degree
  exact Finset.card_le_card (by
    intro e he
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1,
      (Finset.mem_filter.mp he).2.1⟩)

theorem codegree_le_degree_right (u v : V) : H.codegree u v ≤ H.degree v := by
  unfold codegree degree
  exact Finset.card_le_card (by
    intro e he
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1,
      (Finset.mem_filter.mp he).2.2⟩)

/-- Counting incidences first by vertex and then by edge copy. -/
theorem sum_degrees_eq_sum_edge_card :
    H.vertices.sum H.degree = H.edges.sum (fun e => (H.edge e).card) := by
  classical
  calc
    H.vertices.sum H.degree =
        H.vertices.sum (fun v => H.edges.sum (fun e => if v ∈ H.edge e then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro v hv
      simpa only [degree] using
        (Finset.card_filter (fun e => v ∈ H.edge e) H.edges)
    _ = H.edges.sum (fun e => H.vertices.sum
        (fun v => if v ∈ H.edge e then 1 else 0)) := Finset.sum_comm
    _ = H.edges.sum (fun e => (H.edge e).card) := by
      apply Finset.sum_congr rfl
      intro e he
      have hfilter : H.vertices.filter (fun v => v ∈ H.edge e) = H.edge e := by
        ext v
        simp only [Finset.mem_filter]
        constructor
        · exact And.right
        · intro hv
          exact ⟨H.edge_subset e he hv, hv⟩
      calc
        H.vertices.sum (fun v => if v ∈ H.edge e then 1 else 0) =
            (H.vertices.filter (fun v => v ∈ H.edge e)).card :=
          (Finset.card_filter (fun v => v ∈ H.edge e) H.vertices).symm
        _ = (H.edge e).card := congrArg Finset.card hfilter

/-- The incidence count is r times the number of active copies. -/
theorem sum_degrees_uniform {r : ℕ} (hunif : H.IsUniform r) :
    H.vertices.sum H.degree = r * H.edges.card := by
  rw [H.sum_degrees_eq_sum_edge_card]
  calc
    H.edges.sum (fun e => (H.edge e).card) =
        H.edges.sum (fun _ => r) := by
      apply Finset.sum_congr rfl
      intro e he
      exact hunif e he
    _ = r * H.edges.card := by simp [mul_comm]

/-- Count pairs consisting of an edge copy through v and a vertex on it. -/
theorem sum_codegrees_eq_sum_incident_edge_card (v : V) :
    H.vertices.sum (H.codegree v) =
      (H.edges.filter (fun e => v ∈ H.edge e)).sum (fun e => (H.edge e).card) := by
  classical
  calc
    H.vertices.sum (H.codegree v) =
        H.vertices.sum (fun u => H.edges.sum
          (fun e => if v ∈ H.edge e ∧ u ∈ H.edge e then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro u hu
      simpa only [codegree] using
        (Finset.card_filter (fun e => v ∈ H.edge e ∧ u ∈ H.edge e) H.edges)
    _ = H.edges.sum (fun e => H.vertices.sum
        (fun u => if v ∈ H.edge e ∧ u ∈ H.edge e then 1 else 0)) :=
      Finset.sum_comm
    _ = H.edges.sum (fun e => if v ∈ H.edge e then (H.edge e).card else 0) := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases hve : v ∈ H.edge e
      · simp only [hve, true_and, ite_true]
        have hfilter : H.vertices.filter (fun u => u ∈ H.edge e) = H.edge e := by
          ext u
          simp only [Finset.mem_filter]
          constructor
          · exact And.right
          · intro hu
            exact ⟨H.edge_subset e he hu, hu⟩
        calc
          H.vertices.sum (fun u => if u ∈ H.edge e then 1 else 0) =
              (H.vertices.filter (fun u => u ∈ H.edge e)).card :=
            (Finset.card_filter (fun u => u ∈ H.edge e) H.vertices).symm
          _ = (H.edge e).card := congrArg Finset.card hfilter
      · simp [hve]
    _ = (H.edges.filter (fun e => v ∈ H.edge e)).sum
        (fun e => (H.edge e).card) := by
      rw [Finset.sum_ite]
      simp

/-- Total codegree at v, including the diagonal, is r times its degree. -/
theorem sum_codegrees_uniform {r : ℕ} (hunif : H.IsUniform r) (v : V) :
    H.vertices.sum (H.codegree v) = r * H.degree v := by
  rw [H.sum_codegrees_eq_sum_incident_edge_card]
  calc
    (H.edges.filter (fun e => v ∈ H.edge e)).sum (fun e => (H.edge e).card) =
        (H.edges.filter (fun e => v ∈ H.edge e)).sum (fun _ => r) := by
      apply Finset.sum_congr rfl
      intro e he
      exact hunif e (Finset.mem_filter.mp he).1
    _ = r * H.degree v := by simp [degree, mul_comm]

/-- Off-diagonal codegrees account for the other vertices on incident edges. -/
theorem sum_codegrees_offdiag_add_degree {r : ℕ}
    (hunif : H.IsUniform r) {v : V} (hv : v ∈ H.vertices) :
    (H.vertices.erase v).sum (H.codegree v) + H.degree v =
      r * H.degree v := by
  have hdiag : H.codegree v v = H.degree v := by
    simp [codegree, degree]
  calc
    (H.vertices.erase v).sum (H.codegree v) + H.degree v =
        H.vertices.sum (H.codegree v) := by
      rw [← hdiag]
      exact Finset.sum_erase_add H.vertices (H.codegree v) hv
    _ = r * H.degree v := H.sum_codegrees_uniform hunif v
/-- The overlapping-edge contribution to the variance is controlled by
maximum codegree and degree. -/
theorem sum_codegree_sq_le {r B D : ℕ} (hunif : H.IsUniform r)
    {v : V} (hv : v ∈ H.vertices)
    (hB : H.maxCodegree ≤ B) (hD : H.degree v ≤ D) :
    (H.vertices.erase v).sum (fun u => H.codegree v u * H.codegree v u) ≤
      B * (r * D) := by
  have hpoint : ∀ u ∈ H.vertices.erase v,
      H.codegree v u * H.codegree v u ≤ B * H.codegree v u := by
    intro u hu
    have hcodeg : H.codegree v u ≤ B :=
      (H.codegree_le_maxCodegree hv (Finset.mem_erase.mp hu).2
        (Finset.mem_erase.mp hu).1.symm).trans hB
    exact Nat.mul_le_mul_right (H.codegree v u) hcodeg
  have hoff : (H.vertices.erase v).sum (H.codegree v) ≤ r * H.degree v := by
    have h := H.sum_codegrees_offdiag_add_degree hunif hv
    omega
  calc
    (H.vertices.erase v).sum (fun u => H.codegree v u * H.codegree v u) ≤
        (H.vertices.erase v).sum (fun u => B * H.codegree v u) :=
      Finset.sum_le_sum hpoint
    _ = B * (H.vertices.erase v).sum (H.codegree v) := by
      rw [Finset.mul_sum]
    _ ≤ B * (r * H.degree v) := Nat.mul_le_mul_left B hoff
    _ ≤ B * (r * D) :=
      Nat.mul_le_mul_left B (Nat.mul_le_mul_left r hD)
/-- The paper's total degree deficit, expressed without truncated subtraction. -/
theorem degreeDeficit_add_edges {r D : ℕ} (hunif : H.IsUniform r)
    (hD : ∀ v ∈ H.vertices, H.degree v ≤ D) :
    H.degreeDeficit D + r * H.edges.card = H.vertices.card * D := by
  have hsum : H.degreeDeficit D + H.vertices.sum H.degree =
      H.vertices.card * D := by
    unfold degreeDeficit
    rw [← Finset.sum_add_distrib]
    calc
      H.vertices.sum (fun v => D - H.degree v + H.degree v) =
          H.vertices.sum (fun _ => D) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact Nat.sub_add_cancel (hD v hv)
      _ = H.vertices.card * D := by simp
  rwa [H.sum_degrees_uniform hunif] at hsum

/-- A uniform matching covers exactly r vertices per selected copy. -/
theorem covered_card_of_matching {r : ℕ} (hunif : H.IsUniform r)
    {M : Finset E} (hM : H.IsMatching M) :
    (H.covered M).card = r * M.card := by
  classical
  have hdisj : (M : Set E).PairwiseDisjoint H.edge := by
    intro e he f hf hne
    exact hM.2 he hf hne
  rw [covered, Finset.card_biUnion hdisj]
  calc
    M.sum (fun e => (H.edge e).card) = M.sum (fun _ => r) := by
      apply Finset.sum_congr rfl
      intro e he
      exact hunif e (hM.1 he)
    _ = r * M.card := by simp [mul_comm]
section Trimming
variable [DecidableEq E]

/-- Removing an incident copy lowers a vertex degree by exactly one. -/
theorem degree_restrict_erase_add_one {e : E} (he : e ∈ H.edges)
    {v : V} (hve : v ∈ H.edge e) :
    (H.restrictEdges (H.edges.erase e) (Finset.erase_subset e H.edges)).degree v + 1 =
      H.degree v := by
  classical
  unfold degree
  simp only [restrictEdges_edges, Finset.filter_erase]
  exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨he, hve⟩)

/-- Removing an edge incident to an overfull vertex strictly lowers total excess. -/
theorem degreeExcess_restrict_erase_lt {D : ℕ} {e : E} (he : e ∈ H.edges)
    {v : V} (hv : v ∈ H.vertices) (hve : v ∈ H.edge e)
    (hover : D < H.degree v) :
    (H.restrictEdges (H.edges.erase e) (Finset.erase_subset e H.edges)).degreeExcess D <
      H.degreeExcess D := by
  classical
  let H' := H.restrictEdges (H.edges.erase e) (Finset.erase_subset e H.edges)
  have hle : ∀ u ∈ H.vertices, H'.degree u - D ≤ H.degree u - D := by
    intro u hu
    exact Nat.sub_le_sub_right (H.restrictEdges_degree_le _ _ u) D
  have hdeg : H'.degree v + 1 = H.degree v :=
    H.degree_restrict_erase_add_one he hve
  have hvlt : H'.degree v - D < H.degree v - D := by omega
  exact Finset.sum_lt_sum hle ⟨v, hv, hvlt⟩
/-- Delete at most the initial total degree excess to obtain a degree cap. -/
theorem exists_degree_trim (D : ℕ) :
    ∃ F : Finset E, ∃ hF : F ⊆ H.edges,
      (∀ v ∈ H.vertices, (H.restrictEdges F hF).degree v ≤ D) ∧
      H.edges.card ≤ F.card + H.degreeExcess D := by
  classical
  have aux : ∀ n, ∀ K : IndexedHypergraph V E,
      K.degreeExcess D = n →
      ∃ F : Finset E, ∃ hF : F ⊆ K.edges,
        (∀ v ∈ K.vertices, (K.restrictEdges F hF).degree v ≤ D) ∧
        K.edges.card ≤ F.card + K.degreeExcess D := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro K hKn
      by_cases hcap : ∀ v ∈ K.vertices, K.degree v ≤ D
      · refine ⟨K.edges, Finset.Subset.rfl, ?_, ?_⟩
        · intro v hv
          simpa [degree, restrictEdges] using hcap v hv
        · simp
      · push Not at hcap
        obtain ⟨v, hv, hover⟩ := hcap
        have hpos : 0 < K.degree v := by omega
        have hne : (K.edges.filter (fun e => v ∈ K.edge e)).Nonempty :=
          Finset.card_pos.mp hpos
        obtain ⟨e, heinc⟩ := hne
        obtain ⟨he, hve⟩ := Finset.mem_filter.mp heinc
        let K' := K.restrictEdges (K.edges.erase e) (Finset.erase_subset e K.edges)
        have hstrict : K'.degreeExcess D < K.degreeExcess D :=
          K.degreeExcess_restrict_erase_lt he hv hve hover
        have hsmall : K'.degreeExcess D < n := by omega
        obtain ⟨F, hF, hcapF, hboundF⟩ := ih _ hsmall K' rfl
        have hF' : F ⊆ K.edges := hF.trans (Finset.erase_subset e K.edges)
        refine ⟨F, hF', ?_, ?_⟩
        · intro u hu
          have hu' : u ∈ K'.vertices := hu
          have h := hcapF u hu'
          change (F.filter (fun f => u ∈ K.edge f)).card ≤ D at h ⊢
          exact h
        · have hcard : K'.edges.card + 1 = K.edges.card :=
            Finset.card_erase_add_one he
          omega
  exact aux (H.degreeExcess D) H rfl
end Trimming

@[simp] theorem induce_vertices (U : Finset V) :
    (H.induce U).vertices = H.vertices ∩ U := rfl

@[simp] theorem induce_edges (U : Finset V) :
    (H.induce U).edges = H.edges.filter (fun e => H.edge e ⊆ U) := rfl

@[simp] theorem induce_edge (U : Finset V) (e : E) :
    (H.induce U).edge e = H.edge e := rfl

theorem induce_edges_subset (U : Finset V) :
    (H.induce U).edges ⊆ H.edges := Finset.filter_subset _ _

theorem induce_uniform {r : ℕ} (hunif : H.IsUniform r) (U : Finset V) :
    (H.induce U).IsUniform r := by
  intro e he
  exact hunif e (H.induce_edges_subset U he)

theorem induce_degree_le (U : Finset V) (v : V) :
    (H.induce U).degree v ≤ H.degree v := by
  unfold degree
  simp only [induce_edges]
  exact Finset.card_le_card (Finset.filter_subset_filter _ (H.induce_edges_subset U))

theorem induce_codegree_le (U : Finset V) (u v : V) :
    (H.induce U).codegree u v ≤ H.codegree u v := by
  unfold codegree
  simp only [induce_edges]
  exact Finset.card_le_card (Finset.filter_subset_filter _ (H.induce_edges_subset U))

theorem covered_subset_vertices {M : Finset E} (hM : M ⊆ H.edges) :
    H.covered M ⊆ H.vertices := by
  intro v hv
  obtain ⟨e, heM, hve⟩ := Finset.mem_biUnion.mp hv
  exact H.edge_subset e (hM heM) hve
end IndexedHypergraph

end HadwigerLean
