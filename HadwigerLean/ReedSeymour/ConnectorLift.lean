import HadwigerLean.ReedSeymour.Fusion

/-!
# Lifting a terminal connector from a minimal induced subgraph

The parity dichotomy is stated inside the minimal connector U. The fusion
argument uses the corresponding walk in the ambient graph.
-/

namespace HadwigerLean
namespace ReedSeymour

variable {V I : Type*} {G : SimpleGraph V}

/-- Forgetting the induced-subgraph subtype preserves the endpoint-only
terminal connector property. -/
theorem lift_induced_terminal_connector
    (P : ConnectedPartition G I) (i₀ : I) (U : Set V)
    (i j : {k : I // P.touchingQuotient.Adj i₀ k})
    {a b : U} (p : (G.induce U).Walk a b)
    (hp : IsTerminalConnector (inducedTerminalSet P i₀ U) i j p) :
    IsTerminalConnector (terminalSet P i₀) i.1 j.1
      (CentralSplit.liftInducedWalk p) := by
  refine ⟨CentralSplit.liftInducedWalk_isPath hp.isPath,
    CentralSplit.liftInducedWalk_isChordless hp.isChordless,
    hp.start_mem, hp.end_mem, ?_, ?_⟩
  · intro z hz hNi
    have hmap := hz
    change z ∈ (p.map (SimpleGraph.Embedding.induce U).toHom).support at hmap
    rw [SimpleGraph.Walk.support_map] at hmap
    obtain ⟨z', hz', hval⟩ := List.mem_map.mp hmap
    have hval' : z'.1 = z := hval
    have hNi' : z' ∈ inducedTerminalSet P i₀ U i := by
      change z'.1 ∈ terminalSet P i₀ i.1
      exact hval' ▸ hNi
    have hstart := congrArg Subtype.val (hp.start_only z' hz' hNi')
    exact hval'.symm.trans hstart
  · intro z hz hNj
    have hmap := hz
    change z ∈ (p.map (SimpleGraph.Embedding.induce U).toHom).support at hmap
    rw [SimpleGraph.Walk.support_map] at hmap
    obtain ⟨z', hz', hval⟩ := List.mem_map.mp hmap
    have hval' : z'.1 = z := hval
    have hNj' : z' ∈ inducedTerminalSet P i₀ U j := by
      change z'.1 ∈ terminalSet P i₀ j.1
      exact hval' ▸ hNj
    have hend := congrArg Subtype.val (hp.end_only z' hz' hNj')
    exact hval'.symm.trans hend


/-- The lifted walk has the same length as the induced walk. -/
theorem liftInducedWalk_length {U : Set V} {a b : U} (p : (G.induce U).Walk a b) :
    (CentralSplit.liftInducedWalk p).length = p.length := by
  change (p.map (SimpleGraph.Embedding.induce U).toHom).length = p.length
  rw [SimpleGraph.Walk.length_map]

/-- Every lifted vertex still belongs to the inducing set. -/
theorem liftInducedWalk_support_subset {U : Set V} {a b : U}
    (p : (G.induce U).Walk a b) :
    ∀ z, z ∈ (CentralSplit.liftInducedWalk p).support → z ∈ U := by
  intro z hz
  change z ∈ (p.map (SimpleGraph.Embedding.induce U).toHom).support at hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨z', _, hval⟩ := List.mem_map.mp hz
  have hval' : z'.1 = z := hval
  exact hval' ▸ z'.2
end ReedSeymour
end HadwigerLean
