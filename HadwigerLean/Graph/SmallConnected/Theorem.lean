import HadwigerLean.Graph.SmallConnected.PackedWitnessLift
import HadwigerLean.Graph.SmallConnected.ExactDensity
import Mathlib.Tactic

/-!
# The small connected subgraph theorem

This is the constructive Section 8 endpoint: the constant is explicit and
the resulting graph is induced on the chosen vertices.
-/

namespace HadwigerLean

universe u

/-- Every sufficiently dense K_t-minor-free graph has a small
k-vertex-connected induced subgraph. -/
theorem small_connected_subgraph_of_density
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t k : ℕ) (ht : 3 ≤ t) (htk : t ≤ k)
    (hcard : 0 < Fintype.card V)
    (hminor : ¬ HasCliqueMinor G t)
    (hdense : (480 * 6400 * k) * Fintype.card V ≤ edgeCount G) :
    ∃ (W : Type u) (_ : Fintype W) (f : W ↪ V),
      (Fintype.card W : ℝ) ≤
        (480 * 6400 : ℝ)^2 * (t : ℝ) * (Real.log (t : ℝ))^3 ∧
      VertexConnected (G.comap f) k := by
  classical
  let N := Fintype.card V
  obtain ⟨G₀, hsub, hexact⟩ :=
    exists_spanning_subgraph_exact_edgeCount G
      ((480 * 6400 * k) * N) hdense
  letI : DecidableRel G₀.Adj := Classical.decRel _
  have hminor₀ : ¬ HasCliqueMinor G₀ t := by
    intro hm
    exact hminor (hasCliqueMinor_mono hsub hm)
  obtain ⟨F, W, instW, f, hWcard, hf, hWconn⟩ :=
    exists_small_connected_quotient_witness G₀ t k N ht htk
      rfl hcard hminor₀ hexact
  letI : Fintype W := instW
  obtain ⟨e, heconn⟩ :=
    lift_uncovered_vertexConnected_witness G₀ F W f k hf hWconn
  have hgraph : G₀.comap e ≤ G.comap e := by
    intro a b hab
    exact hsub hab
  exact ⟨W, instW, e, hWcard, heconn.mono_graph hgraph⟩

end HadwigerLean