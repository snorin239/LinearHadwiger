import HadwigerLean.Graph.NeighborProxies
import HadwigerLean.Graph.Linkedness.Final

/-!
# Distinct neighbor proxies for a finite family of repeated terminal roles

The knitting proof attaches a separate proxy to every occurrence of a
specified vertex as an endpoint of a star edge. A role can occur many times;
Hall's theorem selects all proxies simultaneously.
-/

namespace HadwigerLean
namespace Woven

variable {V ι : Type*} [Fintype V] [DecidableEq V]
  [Fintype ι] [DecidableEq ι]

/-- A finite-index version of the repeated-role neighbor proxy selection
lemma, with the exact candidate-set cardinality as input. -/
theorem exists_injective_neighbor_proxies_finite_of_candidates
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (role : ι → V) (U : Finset V)
    (hcard : ∀ i, Fintype.card ι ≤
      (G.neighborFinset (role i) \ U).card) :
    ∃ proxy : ι → V,
      Function.Injective proxy ∧
      (∀ i, G.Adj (role i) (proxy i)) ∧
      (∀ i, proxy i ∉ U) := by
  classical
  let C : ι → Finset V := fun i => G.neighborFinset (role i) \ U
  have hall : ∀ s : Finset ι, s.card ≤ (s.biUnion C).card := by
    intro s
    by_cases hs : s.Nonempty
    · obtain ⟨i, hi⟩ := hs
      calc
        s.card ≤ Fintype.card ι := by simpa using Finset.card_le_univ s
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

/-- Degree at least the number of proxy occurrences plus the number of
forbidden original vertices suffices for an injective choice. -/
theorem exists_injective_neighbor_proxies_finite
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (role : ι → V) (U : Finset V)
    (hdegree : ∀ i, U.card + Fintype.card ι ≤ G.degree (role i)) :
    ∃ proxy : ι → V,
      Function.Injective proxy ∧
      (∀ i, G.Adj (role i) (proxy i)) ∧
      (∀ i, proxy i ∉ U) := by
  classical
  apply exists_injective_neighbor_proxies_finite_of_candidates G role U
  intro i
  have hcut := Finset.card_le_card_sdiff_add_card
    (s := G.neighborFinset (role i)) (t := U)
  have hdeg : U.card + Fintype.card ι ≤
      (G.neighborFinset (role i)).card := by
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdegree i
  omega

end Woven
end HadwigerLean
