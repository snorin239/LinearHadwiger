import HadwigerLean.Graph.SetMengerTheorem

/-!
# Connectivity and set Menger

Deleting fewer than `k` vertices from a `k`-connected graph leaves any
two terminal sets of size at least `k` joined. Set Menger then supplies
`k` disjoint terminal-to-terminal paths.
-/

namespace HadwigerLean

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  {k : ℕ}

theorem VertexConnected.no_small_AB_separator (hconn : VertexConnected G k)
    (A B : Finset V) (hA : k ≤ A.card) (hB : k ≤ B.card)
    (Q : Finset V) (hQ : Q.card < k) :
    ¬ SetMenger.IsABSeparator G A B Q := by
  classical
  intro hsep
  have ha : ∃ a ∈ A, a ∉ Q := by
    by_contra hn
    have hAQ : A ⊆ Q := by
      intro a hmem
      by_contra hnot
      exact hn ⟨a, hmem, hnot⟩
    have hcard := Finset.card_le_card hAQ
    omega
  have hb : ∃ b ∈ B, b ∉ Q := by
    by_contra hn
    have hBQ : B ⊆ Q := by
      intro b hmem
      by_contra hnot
      exact hn ⟨b, hmem, hnot⟩
    have hcard := Finset.card_le_card hBQ
    omega
  obtain ⟨a, haA, haQ⟩ := ha
  obtain ⟨b, hbB, hbQ⟩ := hb
  let s : Set V := (Q : Set V)ᶜ
  let a' : s := ⟨a, haQ⟩
  let b' : s := ⟨b, hbQ⟩
  let p : (G.induce s).Path a' b' :=
    ((hconn.connected_delete Q hQ).preconnected a' b').some.toPath
  let q : G.Path a b := p.mapEmbedding (SimpleGraph.Embedding.induce s)
  obtain ⟨v, hvQ, hvq⟩ := hsep a haA b hbB q
  have hvmap : v ∈ (p : (G.induce s).Walk a' b').support.map Subtype.val := by
    change v ∈ ((p : (G.induce s).Walk a' b').map
      (SimpleGraph.Embedding.induce s).toHom).support at hvq
    rw [SimpleGraph.Walk.support_map] at hvq
    simpa using hvq
  obtain ⟨z, _, hz⟩ := List.mem_map.mp hvmap
  exact z.property (hz ▸ hvQ)

theorem VertexConnected.exists_AB_linkage (hconn : VertexConnected G k)
    (A B : Finset V) (hA : k ≤ A.card) (hB : k ≤ B.card) :
    ∃ (P : IndexedPairs (Fin k) V) (L : IndexedLinkage G P),
      SetMenger.IsABLinkage L A B := by
  classical
  apply SetMenger.exists_linkage_of_separator_lower_bound G A B k
  intro Q hQ
  by_contra hsmall
  exact hconn.no_small_AB_separator A B hA hB Q (by omega) hQ

end HadwigerLean
