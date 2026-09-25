import HadwigerLean.Inseparability.CheapTreeInduced
import HadwigerLean.Inseparability.ModelTrimmingAlgebra
import Mathlib.Tactic

/-!
# Cheap-tree trimming of rooted clique-model branches

Each connected branch is shortened through its core vertices. The resulting
branches still form a rooted clique model, while all unmarked vertices need
at most two colors per branch. The total marked set has size at most three
times the old core.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {s : ℕ}

/-- Trim a rooted clique model through all core vertices, with a single
marked set of size at most three times the core size. -/
theorem exists_cheap_branch_sets
    (root : Fin s → V)
    (M : RootedMinorModel (SimpleGraph.completeGraph (Fin s)) G root)
    (core : Finset V)
    (hrootcore : ∀ i, root i ∈ core) :
    ∃ (Q T : Fin s → Finset V),
      (∀ i, (Q i : Set V) ⊆ M.branch i) ∧
      (∀ i, (G.induce (Q i : Set V)).Connected) ∧
      (∀ i v, v ∈ M.branch i → v ∈ core → v ∈ Q i) ∧
      (∀ i, T i ⊆ Q i) ∧
      ((Finset.univ : Finset (Fin s)).biUnion T).card ≤ 3 * core.card ∧
      chromatic (G.induce
        ((((Finset.univ : Finset (Fin s)).biUnion Q) : Finset V) : Set V)) ≤
        chromatic (G.induce
          ((((Finset.univ : Finset (Fin s)).biUnion T) : Finset V) : Set V)) +
          2 * s := by
  classical
  let B : Fin s → Finset V := fun i =>
    Finset.univ.filter (· ∈ M.branch i)
  let S : Fin s → Finset V := fun i => core ∩ B i
  have hBset : ∀ i, (B i : Set V) = M.branch i := by
    intro i
    ext v
    simp [B]
  have hSsub : ∀ i, S i ⊆ B i := by
    intro i
    exact Finset.inter_subset_right
  have hSnonempty : ∀ i, (S i).Nonempty := by
    intro i
    refine ⟨root i, Finset.mem_inter.mpr ⟨hrootcore i, ?_⟩⟩
    simpa [B] using M.root_mem i
  have hpiece : ∀ i : Fin s, ∃ Q T : Finset V,
      S i ⊆ T ∧ T ⊆ Q ∧ Q ⊆ B i ∧ T.card ≤ 3 * (S i).card ∧
      (G.induce (Q : Set V)).Connected ∧
      chromatic (G.induce ((Q \ T : Finset V) : Set V)) ≤ 2 := by
    intro i
    have hBconn : (G.induce (B i : Set V)).Connected := by
      rw [hBset i]
      exact M.connected i
    exact exists_cheap_tree_inside G (B i) (S i)
      hBconn (hSsub i) (hSnonempty i)
  choose Q T hST hTQ hQB hTcard hQconn hrem using hpiece
  have hQsub : ∀ i, (Q i : Set V) ⊆ M.branch i := by
    intro i v hv
    rw [← hBset i]
    exact hQB i hv
  have hcoreQ : ∀ i v, v ∈ M.branch i → v ∈ core → v ∈ Q i := by
    intro i v hv hc
    have hvB : v ∈ B i := by
      change v ∈ (B i : Set V)
      rw [hBset i]
      exact hv
    exact hTQ i (hST i (Finset.mem_inter.mpr ⟨hc,hvB⟩))
  have hSdisj : Set.PairwiseDisjoint (Set.univ : Set (Fin s))
      (fun i => (S i : Set V)) := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro v hvi hvj
    have hi : v ∈ M.branch i := by
      rw [← hBset i]
      exact (Finset.mem_inter.mp hvi).2
    have hj : v ∈ M.branch j := by
      rw [← hBset j]
      exact (Finset.mem_inter.mp hvj).2
    exact (Set.disjoint_left.mp (M.disjoint hij)) hi hj
  have hpair : ∀ i ∈ (Finset.univ : Finset (Fin s)),
      ∀ j ∈ (Finset.univ : Finset (Fin s)), i ≠ j →
      Disjoint (S i) (S j) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    exact (Set.disjoint_left.mp (hSdisj (Set.mem_univ i)
      (Set.mem_univ j) hij)) hvi hvj
  have hSunion : ((Finset.univ : Finset (Fin s)).biUnion S) ⊆ core := by
    intro v hv
    obtain ⟨i,_,hvi⟩ := Finset.mem_biUnion.mp hv
    exact (Finset.mem_inter.mp hvi).1
  have hsumS : (∑ i : Fin s, (S i).card) ≤ core.card := by
    rw [← Finset.card_biUnion hpair]
    exact Finset.card_le_card hSunion
  have hsumT : (∑ i : Fin s, (T i).card) ≤
      3 * (∑ i : Fin s, (S i).card) := by
    calc
      _ ≤ ∑ i : Fin s, 3 * (S i).card :=
        Finset.sum_le_sum (fun i _ => hTcard i)
      _ = 3 * (∑ i : Fin s, (S i).card) := by rw [Finset.mul_sum]
  have hXcard : ((Finset.univ : Finset (Fin s)).biUnion T).card ≤
      3 * core.card := by
    have hbi := Finset.card_biUnion_le
      (s := (Finset.univ : Finset (Fin s))) (t := T)
    nlinarith
  have hχ : chromatic (G.induce
        ((((Finset.univ : Finset (Fin s)).biUnion Q) : Finset V) : Set V)) ≤
        chromatic (G.induce
          ((((Finset.univ : Finset (Fin s)).biUnion T) : Finset V) : Set V)) +
          2 * s := by
    exact chromatic_model_union_le_marked_add_two_mul G Q T hrem (le_refl _)
  exact ⟨Q,T,hQsub,hQconn,hcoreQ,hTQ,hXcard,hχ⟩

/-- Trim the actual rooted model while retaining every core vertex and
bounding the chromatic cost of its vertex set. -/
theorem exists_cheap_trimmed_rooted_model
    (root : Fin s → V)
    (M : RootedMinorModel (SimpleGraph.completeGraph (Fin s)) G root)
    (core : Finset V)
    (hrootcore : ∀ i, root i ∈ core)
    (hwitness : ∀ i j, i ≠ j →
      ∃ x ∈ M.branch i, ∃ y ∈ M.branch j,
        x ∈ core ∧ y ∈ core ∧ G.Adj x y) :
    ∃ (M' : RootedMinorModel (SimpleGraph.completeGraph (Fin s)) G root)
      (A X : Finset V),
      M'.toMinorModel.vertices = (A : Set V) ∧
      M'.toMinorModel.vertices ⊆ M.toMinorModel.vertices ∧
      X ⊆ A ∧ X.card ≤ 3 * core.card ∧
      chromatic (G.induce (A : Set V)) ≤
        chromatic (G.induce (X : Set V)) + 2 * s ∧
      (∀ i v, v ∈ M.branch i → v ∈ core → v ∈ M'.branch i) := by
  classical
  obtain ⟨Q,T,hQsub,hQconn,hcoreQ,hTQ,hXcard,hχ⟩ :=
    exists_cheap_branch_sets root M core hrootcore
  let M' := rootedModel_restrict_through_core root M core
    hrootcore hwitness Q hQsub hQconn hcoreQ
  let A : Finset V := (Finset.univ : Finset (Fin s)).biUnion Q
  let X : Finset V := (Finset.univ : Finset (Fin s)).biUnion T
  have hA : M'.toMinorModel.vertices = (A : Set V) := by
    ext v
    simp [M', A, MinorModel.vertices,
      rootedModel_restrict_through_core]
  have hsub : M'.toMinorModel.vertices ⊆ M.toMinorModel.vertices := by
    intro v hv
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
    exact Set.mem_iUnion.mpr ⟨i, hQsub i hi⟩
  have hXA : X ⊆ A := by
    intro v hv
    obtain ⟨i, _, hvi⟩ := Finset.mem_biUnion.mp hv
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hTQ i hvi⟩
  refine ⟨M', A, X, hA, hsub, hXA, hXcard, hχ, ?_⟩
  intro i v hv hc
  exact hcoreQ i v hv hc
end Inseparability
end HadwigerLean



