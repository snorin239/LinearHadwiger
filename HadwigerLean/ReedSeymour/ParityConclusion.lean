import HadwigerLean.ReedSeymour.ParityStems

/-!
# Bipartiteness of a minimal terminal transversal

This closes the combinatorial parity argument in Reed--Seymour: a minimal
connected set meeting every terminal set is bipartite if there is no odd
induced endpoint-only connector between distinct terminal sets.
-/

namespace HadwigerLean
namespace ReedSeymour

variable {V : Type*} {G : SimpleGraph V}

/-- A minimal connected transversal is two-colorable whenever all induced
endpoint-only connectors between different terminal sets have even length. -/
theorem colorable_two_of_minimal_connected_transversal
    {I : Type*} {N : I → Set V}
    (hmin : IsMinimalConnectedTransversal G N)
    (hno : NoOddConnector G N) : G.Colorable 2 := by
  by_contra hnot
  obtain ⟨u, c, hc, hodd⟩ :=
    exists_odd_cycle_of_not_colorable_two hmin.1 hnot
  obtain ⟨x, y, hxy, sx, sy, hij, hparity⟩ :=
    odd_cycle_has_distinct_equal_parity_gated_stems hmin c hc hodd
  obtain ⟨r, hconnector, hoddR⟩ :=
    odd_connector_of_gated_stems c sx sy (c.adj_of_mem_edges hxy) hparity
  have heven : Even r.length := hno sx.index sy.index hij r hconnector
  exact (Nat.not_even_iff_odd.mpr hoddR) heven

end ReedSeymour
end HadwigerLean