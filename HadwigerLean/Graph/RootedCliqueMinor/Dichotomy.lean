import HadwigerLean.Graph.RootedCliqueMinor.CriticalMenger
import HadwigerLean.Graph.RootedCliqueMinor.TerminalDichotomy
import HadwigerLean.Graph.CliqueDensity.Reduction

/-!
# The rooted-clique separator dichotomy

Strong induction on the host order implements Appendix B: contract an edge
of a root-free model branch, then either lift the quotient outcome or
recurse on the smaller completed right torso of a critical separation.
-/

namespace HadwigerLean

universe u

private theorem rootCliqueSeparatorDichotomy_of_card :
    ∀ n : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V],
      (G : SimpleGraph V) → (r : ℕ) → Fintype.card V = n →
        RootCliqueSeparatorDichotomy G r := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ G r hcard root hroot M
    rcases singleton_avoiding_or_contractable root M with
      hsingle | ⟨i₀, a, b, ha, hb, hab, haR, hbR⟩
    · exact rootClique_terminal_dichotomy root hroot M hsingle
    · have hqcard : Fintype.card (EdgeContractionVertex a b) < n := by
        have h := edgeContraction_card_add_one G hab
        omega
      have hDq : RootCliqueSeparatorDichotomy (edgeContraction G hab) r :=
        ih (Fintype.card (EdgeContractionVertex a b)) hqcard
          (edgeContraction G hab) r rfl
      rcases rootClique_contraction_reduction root hroot M hab i₀
          ha hb haR hbR hDq with hA | hO | hC
      · exact Or.inl hA
      · exact Or.inr hO
      · obtain ⟨C⟩ := hC
        letI : Fintype C.sep.left := Fintype.ofFinite _
        letI : DecidableEq C.sep.left := Classical.decEq _
        letI : Fintype C.sep.right := Fintype.ofFinite _
        obtain ⟨_, _, _, _, hsmaller, _⟩ :=
          C.smaller_torso_model hroot haR
        have hright : Fintype.card C.sep.right < n := by omega
        have hDt : RootCliqueSeparatorDichotomy
            (G.induce C.sep.right) r :=
          ih (Fintype.card C.sep.right) hright
            (G.induce C.sep.right) r rfl
        exact C.recurse hroot hDt

/-- Appendix B's separator dichotomy, with no connectivity assumption on
the host graph. -/
theorem rootCliqueSeparatorDichotomy
    {V : Type u} [Fintype V] (G : SimpleGraph V) (r : ℕ) :
    RootCliqueSeparatorDichotomy G r := by
  classical
  exact rootCliqueSeparatorDichotomy_of_card
    (Fintype.card V) G r rfl

/-- The rooted clique minor theorem (Kawarabayashi's bound): every
r-connected graph with a K_(2r) minor has a rooted K_r minor at any r
distinct prescribed vertices. -/
theorem rootedCliqueMinor_of_connected_cliqueMinor
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} {r : ℕ}
    (hconn : VertexConnected G r)
    (hminor : HasCliqueMinor G (2 * r))
    (root : Fin r → V) (hroot : Function.Injective root) :
    HasRootedCliqueMinor G root :=
  rootedCliqueMinor_of_dichotomy hconn hminor
    (rootCliqueSeparatorDichotomy G r) root hroot

end HadwigerLean
