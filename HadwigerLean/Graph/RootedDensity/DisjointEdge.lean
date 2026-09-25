import HadwigerLean.Graph.RootedDensity.Definitions
import HadwigerLean.Graph.ContractionEdges
import HadwigerLean.Graph.Minor
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Tactic

/-! Adding a new disjoint edge component to a minor model. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- A minor outside the ends of an edge extends to a minor of its disjoint
sum with `K₂`. -/
theorem minor_sum_edge_of_induced_minor
    {W : Type u} {V : Type v} (H : SimpleGraph W) (G : SimpleGraph V)
    {s t : V} (hst : G.Adj s t)
    (M : MinorModel H (G.induce {x : V | x ≠ s ∧ x ≠ t})) :
    Nonempty (MinorModel (H ⊕g SimpleGraph.completeGraph (Fin 2)) G) := by
  classical
  let S : Set V := {x | x ≠ s ∧ x ≠ t}
  let N : MinorModel H G :=
    M.map (SimpleGraph.Embedding.induce S).toHom Subtype.val_injective
  have hN (i : W) {x : V} (hx : x ∈ N.branch i) : x ∈ S := by
    change x ∈ (Subtype.val '' M.branch i) at hx
    rcases hx with ⟨y, _, rfl⟩
    exact y.property
  let p : Fin 2 → V := fun i => if i = 0 then s else t
  have hp0 : p 0 = s := by simp [p]
  have hp1 : p 1 = t := by simp [p]
  have hpinj : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [p, hst.ne]
  refine ⟨{
    branch := fun z => match z with
      | .inl i => N.branch i
      | .inr i => {p i}
    connected := ?_
    disjoint := ?_
    adjacent := ?_
  }⟩
  · rintro (i | i)
    · exact N.connected i
    · simp
  · rintro (i | i) (j | j) hij
    · exact N.disjoint (by simpa using hij)
    · apply Set.disjoint_left.mpr
      intro x hx hxp
      have hxs := hN i hx
      have hxp' : x = p j := by simpa using hxp
      subst x
      fin_cases j <;> simp_all [S, p]
    · apply Set.disjoint_left.mpr
      intro x hxp hx
      have hxs := hN j hx
      have hxp' : x = p i := by simpa using hxp
      subst x
      fin_cases i <;> simp_all [S, p]
    · apply Set.disjoint_left.mpr
      intro x hxi hxj
      have hne : i ≠ j := by simpa using hij
      exact (hpinj.ne hne) ((Set.mem_singleton_iff.mp hxi).symm.trans
        (Set.mem_singleton_iff.mp hxj))
  · rintro (i | i) (j | j) hij
    · exact N.adjacent (by simpa using hij)
    · simp at hij
    · simp at hij
    · have hpne : i ≠ j := by simpa using hij
      fin_cases i <;> fin_cases j <;> simp_all [p, hst.symm]


/-- Deleting the ends of an edge loses fewer than twice the order in edge
count. A density budget of `c + 2` therefore leaves density at least `c`. -/
theorem dense_after_delete_edge_endpoints
    {V : Type v} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {s t : V} (hst : G.Adj s t) (c : ℝ) (hc : 0 ≤ c)
    (hdense : (c + 2) * (Fintype.card V : ℝ) ≤ (edgeCount G : ℝ)) :
    c * (Fintype.card {x : V // x ≠ s ∧ x ≠ t} : ℝ) ≤
      (edgeCount (G.induce {x : V | x ≠ s ∧ x ≠ t}) : ℝ) := by
  classical
  let U : Finset V := {s, t}
  have hUcard : U.card = 2 := Finset.card_pair hst.ne
  have hSCard : Fintype.card {x : V // x ≠ s ∧ x ≠ t} + 2 =
      Fintype.card V := by
    have hcard : Fintype.card {x : V // x ≠ s ∧ x ≠ t} = Uᶜ.card := by
      apply Fintype.card_of_subtype
      intro x
      simp [U]
    have hcomp := Finset.card_compl_add_card U
    omega
  have hpart : edgeCount (G.induce {x : V | x ≠ s ∧ x ≠ t}) +
      edgeIncidenceCount G U = edgeCount G := by
    have h := edgeCount_induce_compl_add_incidence (G := G) U
    have hset : ((Uᶜ : Finset V) : Set V) = {x : V | x ≠ s ∧ x ≠ t} := by
      ext x
      simp [U, and_comm]
    rw [hset] at h
    exact h
  have hinc : edgeIncidenceCount G U + 1 = G.degree s + G.degree t :=
    edgeIncidenceCount_pair_add_one (G := G) hst
  have hsdeg := G.degree_lt_card_verts s
  have htdeg := G.degree_lt_card_verts t
  have hpartR : (edgeCount (G.induce {x : V | x ≠ s ∧ x ≠ t}) : ℝ) +
      (edgeIncidenceCount G U : ℝ) = (edgeCount G : ℝ) := by
    exact_mod_cast hpart
  have hincR : (edgeIncidenceCount G U : ℝ) + 1 =
      (G.degree s : ℝ) + G.degree t := by exact_mod_cast hinc
  have hSCardR : (Fintype.card {x : V // x ≠ s ∧ x ≠ t} : ℝ) + 2 =
      Fintype.card V := by exact_mod_cast hSCard
  have hsdegR : (G.degree s : ℝ) < Fintype.card V := by exact_mod_cast hsdeg
  have htdegR : (G.degree t : ℝ) < Fintype.card V := by exact_mod_cast htdeg
  nlinarith

/-- Adding a disjoint `K₂` to a fixed target raises its universal unrooted
edge-density threshold by at most two. -/
theorem densityForcesMinor_sum_edge
    {W : Type u} [Fintype W] (H : SimpleGraph W) (c : ℝ) (hc : 0 ≤ c)
    (hforce : DensityForcesMinor.{v,u} H c) :
    DensityForcesMinor.{v,u} (H ⊕g SimpleGraph.completeGraph (Fin 2)) (c + 2) := by
  intro V _ G hn hdense
  classical
  have hbound : edgeCount G ≤ (Fintype.card V).choose 2 := by
    rw [edgeCount_eq_card_edgeFinset]
    exact G.card_edgeFinset_le_card_choose_two
  have hcard : 3 ≤ Fintype.card V := by
    by_contra h
    have hle : Fintype.card V ≤ 2 := by omega
    have hlargeR : 2 * (Fintype.card V : ℝ) ≤ (edgeCount G : ℝ) := by
      have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
      nlinarith [mul_nonneg hc hn0]
    have hlarge : 2 * Fintype.card V ≤ edgeCount G := by
      exact_mod_cast hlargeR
    interval_cases hN : Fintype.card V <;>
      norm_num [hN] at hbound hlarge hn <;> omega
  have hpositive : 0 < edgeCount G := by
    have hNR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
    have hp : 0 < (c + 2) * (Fintype.card V : ℝ) := by positivity
    exact_mod_cast (hp.trans_le hdense)
  have hfinpos : 0 < G.edgeFinset.card := by
    rw [← edgeCount_eq_card_edgeFinset]
    exact hpositive
  obtain ⟨e, he⟩ := Finset.card_pos.mp hfinpos
  induction e using Sym2.ind with
  | _ s t =>
    have hst : G.Adj s t := by simpa [SimpleGraph.mem_edgeFinset] using he
    let J := G.induce {x : V | x ≠ s ∧ x ≠ t}
    have hJpos : 0 < Fintype.card {x : V // x ≠ s ∧ x ≠ t} := by
      have hpair : ({s, t} : Finset V).card = 2 := Finset.card_pair hst.ne
      have hcomp := Finset.card_compl_add_card ({s, t} : Finset V)
      have hJcard : Fintype.card {x : V // x ≠ s ∧ x ≠ t} =
          ({s, t}ᶜ : Finset V).card := by
        apply Fintype.card_of_subtype
        intro x
        simp
      omega
    have hJdense : c * (Fintype.card {x : V // x ≠ s ∧ x ≠ t} : ℝ) ≤
        (edgeCount J : ℝ) :=
      dense_after_delete_edge_endpoints G hst c hc hdense
    obtain ⟨M⟩ := hforce _ J hJpos hJdense
    exact minor_sum_edge_of_induced_minor H G hst M
end HadwigerLean.RootedDensity








