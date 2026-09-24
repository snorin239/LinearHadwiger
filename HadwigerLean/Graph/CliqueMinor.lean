import HadwigerLean.Graph.Minor
import HadwigerLean.Graph.Finite

/-! A clique embeds as a complete graph, hence gives a complete minor. -/

namespace HadwigerLean

/-- The largest clique order is bounded by the largest complete-minor order. -/
theorem cliqueNum_le_cliqueMinorNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : G.cliqueNum ≤ cliqueMinorNumber G := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  let e := G.topEmbeddingOfNotCliqueFree hs.not_cliqueFree
  have h := cliqueMinorNumber_map e.toHom e.injective
  rw [cliqueMinorNumber_completeGraph] at h
  exact h

end HadwigerLean