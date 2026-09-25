import HadwigerLean.Graph.SetMengerTheorem
import HadwigerLean.Graph.VertexConnectivity
import Mathlib.Tactic

/-!
# Disjoint connectors between large sets in a connected graph
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertex connectivity and two large endpoint sets yield the requested
number of disjoint paths, allowing an endpoint to lie in both sets. -/
theorem exists_disjoint_connectors_of_vertexConnected
    (G : SimpleGraph V) (A B : Finset V) (k m : ℕ)
    (hconn : VertexConnected G k) (hm : m ≤ k)
    (hA : m ≤ A.card) (hB : m ≤ B.card) :
    ∃ (P : IndexedPairs (Fin m) V) (L : IndexedLinkage G P),
      SetMenger.IsABLinkage L A B := by
  classical
  apply SetMenger.exists_linkage_of_separator_lower_bound G A B m
  intro Q hQ
  by_contra hsmall
  have hQsmall : Q.card < m := by omega
  have hqk : Q.card < k := by omega
  have hAout : ∃ a ∈ A, a ∉ Q := by
    by_contra h
    push Not at h
    have hsub : A ⊆ Q := by
      intro a ha
      exact h a ha
    have hcard := Finset.card_le_card hsub
    omega
  have hBout : ∃ b ∈ B, b ∉ Q := by
    by_contra h
    push Not at h
    have hsub : B ⊆ Q := by
      intro b hb
      exact h b hb
    have hcard := Finset.card_le_card hsub
    omega
  obtain ⟨a, ha, haQ⟩ := hAout
  obtain ⟨b, hb, hbQ⟩ := hBout
  let U : Set V := (Q : Set V)ᶜ
  let aa : U := ⟨a, haQ⟩
  let bb : U := ⟨b, hbQ⟩
  let p : (G.induce U).Path aa bb :=
    ((hconn.connected_delete Q hqk).preconnected aa bb).some.toPath
  let q : G.Path a b := p.mapEmbedding (SimpleGraph.Embedding.induce U)
  obtain ⟨v, hvQ, hvq⟩ := hQ a ha b hb q
  have hvmap : v ∈ (p : (G.induce U).Walk aa bb).support.map Subtype.val := by
    change v ∈ ((p : (G.induce U).Walk aa bb).map
      (SimpleGraph.Embedding.induce U).toHom).support at hvq
    rw [SimpleGraph.Walk.support_map] at hvq
    simpa using hvq
  obtain ⟨z, _, hz⟩ := List.mem_map.mp hvmap
  exact z.property (hz ▸ hvQ)

end Woven
end HadwigerLean
