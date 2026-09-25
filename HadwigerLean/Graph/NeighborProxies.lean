import HadwigerLean.Graph.VertexConnectivity
import Mathlib.Combinatorics.Hall.Basic

/-!
# Distinct neighbors for repeated prescribed roles

Roles may coincide. If each role has enough neighbors outside the occupied
original vertices, Hall's theorem assigns distinct adjacent proxies. The
degree corollary records the `2n` bound used in the woven induction.
-/

namespace HadwigerLean

universe u

/-- Give each of `n` roles a distinct adjacent proxy outside `U` when each
candidate set has at least `n` members. Repeated roles are allowed. -/
theorem exists_distinct_neighbor_proxies_of_candidates
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ)
    (role : Fin n → V) (U : Finset V)
    (hcard : ∀ i, n ≤ (G.neighborFinset (role i) \ U).card) :
    ∃ proxy : Fin n → V, Function.Injective proxy ∧
      (∀ i, G.Adj (role i) (proxy i)) ∧
      (∀ i, proxy i ∉ U) := by
  classical
  let C : Fin n → Finset V := fun i => G.neighborFinset (role i) \ U
  have hall : ∀ s : Finset (Fin n), s.card ≤ (s.biUnion C).card := by
    intro s
    by_cases hs : s.Nonempty
    · obtain ⟨i, hi⟩ := hs
      calc
        s.card ≤ n := by simpa using (Finset.card_le_univ s)
        _ ≤ (C i).card := hcard i
        _ ≤ (s.biUnion C).card := by
          apply Finset.card_le_card
          intro x hx
          exact Finset.mem_biUnion.mpr ⟨i, hi, hx⟩
    · simp [Finset.not_nonempty_iff_eq_empty.mp hs]
  obtain ⟨proxy, hinj, hproxy⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective C).mp hall
  refine ⟨proxy, hinj, ?_, ?_⟩
  · intro i
    exact (G.mem_neighborFinset (role i) (proxy i)).mp
      (Finset.mem_sdiff.mp (hproxy i)).1
  · intro i
    exact (Finset.mem_sdiff.mp (hproxy i)).2

/-- Minimum degree `2n` leaves enough distinct neighbors for `n` roles
after forbidding at most `n` original occupied vertices. -/
theorem exists_distinct_neighbor_proxies
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ)
    (role : Fin n → V) (U : Finset V)
    (hU : U.card ≤ n)
    (hdegree : ∀ i, 2 * n ≤ G.degree (role i)) :
    ∃ proxy : Fin n → V, Function.Injective proxy ∧
      (∀ i, G.Adj (role i) (proxy i)) ∧
      (∀ i, proxy i ∉ U) := by
  classical
  apply exists_distinct_neighbor_proxies_of_candidates G n role U
  intro i
  have hcut := Finset.card_le_card_sdiff_add_card
    (s := G.neighborFinset (role i)) (t := U)
  have hdegree' : 2 * n ≤ (G.neighborFinset (role i)).card := by
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdegree i
  omega

/-- A `2n` degree bound separates all proxies from all original roles,
even when several occurrences name the same vertex. -/
theorem exists_distinct_neighbor_proxies_for_roles
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ)
    (role : Fin n → V)
    (hdegree : ∀ i, 2 * n ≤ G.degree (role i)) :
    ∃ proxy : Fin n → V, Function.Injective proxy ∧
      (∀ i, G.Adj (role i) (proxy i)) ∧
      (∀ i j, proxy i ≠ role j) := by
  let U : Finset V := Finset.univ.image role
  have hU : U.card ≤ n := by
    calc
      U.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by simp
  obtain ⟨proxy, hinj, hadj, hav⟩ :=
    exists_distinct_neighbor_proxies G n role U hU hdegree
  refine ⟨proxy, hinj, hadj, ?_⟩
  intro i j heq
  exact hav i (heq ▸ Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
end HadwigerLean
