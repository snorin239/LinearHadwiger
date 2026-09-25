import HadwigerLean.Graph.RootedDensity.CliqueBridge
import HadwigerLean.Graph.Linkedness.Massed
import Mathlib.Tactic

/-! Vertex connectivity supplies the density used by the clique bridge. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- The edge-per-vertex density is at least half the vertex-connectivity
parameter, by minimum degree and handshaking. -/
theorem half_connectivity_le_edgeDensity
    {V : Type u} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hconn : VertexConnected G k) :
    (k : ℝ) / 2 ≤ edgeDensity G := by
  classical
  have hdeg : ∀ v : V, k ≤ G.degree v := by
    intro v
    exact Linkedness.degree_ge_of_vertexConnected hconn v
  have hsum : k * Fintype.card V ≤ ∑ v : V, G.degree v := by
    calc
      k * Fintype.card V = ∑ _v : V, k := by simp [mul_comm]
      _ ≤ ∑ v : V, G.degree v := by
        apply Finset.sum_le_sum
        intro v _
        exact hdeg v
  rw [sum_degree_eq_two_edgeCount] at hsum
  have hsumR : (k : ℝ) * (Fintype.card V : ℝ) ≤
      2 * (edgeCount G : ℝ) := by exact_mod_cast hsum
  have hn : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast (Nat.zero_lt_of_lt hconn.order_gt)
  unfold edgeDensity
  apply (le_div_iff₀ hn).2
  nlinarith

/-- A connectivity parameter high enough to force a `K_(2h)` minor
therefore roots every target `H` of order `h`. -/
theorem rootedMinor_of_connected_clique_threshold
    {W : Type v} {V : Type u} [Fintype W] [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V)
    (hh : 1 ≤ Fintype.card W) (k : ℕ)
    (hconn : VertexConnected G k)
    (hrootconn : Fintype.card W ≤ k)
    (hKT : 60 * (Fintype.card W : ℝ) *
      Real.sqrt (Real.log (2 * (Fintype.card W : ℝ))) ≤ (k : ℝ) / 2)
    (root : W → V) (hroot : Function.Injective root) :
    Nonempty (RootedMinorModel H G root) := by
  have hm : VertexConnected G (Fintype.card W) := hconn.of_le hrootconn
  apply rootedMinor_of_clique_density H G hh hm _ root hroot
  exact hKT.trans (half_connectivity_le_edgeDensity G k hconn)

end HadwigerLean.RootedDensity

