import HadwigerLean.Inseparability.DensePieceFinder
import HadwigerLean.Graph.SmallConnected.Theorem
import Mathlib.Tactic

/-!
# Small connected pieces from the Section 8 theorem

This module combines the small-connected-subgraph theorem with sparse greedy
coloring and the disjoint-piece packing lemma.
-/

namespace HadwigerLean
namespace Inseparability

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

private theorem sc_piece_inside
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t k N : ℕ) (ht : 3 ≤ t) (htk : t ≤ k)
    (hminor : ¬ HasCliqueMinor G t)
    (hsize : (480 * 6400 : ℝ)^2 * (t : ℝ) *
      (Real.log (t : ℝ))^3 ≤ (N : ℝ))
    (R : Finset V) (hR : R.Nonempty)
    (hdense : (480 * 6400 * k) * R.card ≤
      edgeCount (G.induce (R : Set V))) :
    ∃ J : Finset V, J ⊆ R ∧ J.card ≤ N ∧
      VertexConnected (G.induce (J : Set V)) k := by
  classical
  have hminorR : ¬ HasCliqueMinor (G.induce (R : Set V)) t := by
    intro hm
    exact hminor (hasCliqueMinor_of_minor (induce_isMinor G (R : Set V)) hm)
  have hcardR : Fintype.card (R : Set V) = R.card := by
    apply Fintype.card_of_finset' R
    intro x
    rfl
  have hpos : 0 < Fintype.card (R : Set V) := by
    rw [hcardR]
    exact Finset.card_pos.mpr hR
  have hdenseR : (480 * 6400 * k) * Fintype.card (R : Set V) ≤
      edgeCount (G.induce (R : Set V)) := by
    rw [hcardR]
    exact hdense
  obtain ⟨W, instW, f, hWsize, hWconn⟩ :=
    small_connected_subgraph_of_density
      (G.induce (R : Set V)) t k ht htk hpos hminorR hdenseR
  letI : Fintype W := instW
  let e : W ↪ V := f.trans (Function.Embedding.subtype (· ∈ (R : Set V)))
  let J : Finset V := Finset.univ.image e
  have hJsub : J ⊆ R := by
    intro v hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact (f w).property
  have hJcard : J.card = Fintype.card W := by
    simp [J, Finset.card_image_of_injective _ e.injective]
  have hJsize : J.card ≤ N := by
    have hWR : (Fintype.card W : ℝ) ≤ (N : ℝ) := hWsize.trans hsize
    rw [hJcard]
    exact_mod_cast hWR
  have hrange : (J : Set V) = Set.range e := by
    ext v
    simp [J]
  have hconnE : VertexConnected (G.comap e) k := by
    exact hWconn
  have hconnJ : VertexConnected (G.induce (J : Set V)) k := by
    have hconnRange : VertexConnected (G.induce (Set.range e)) k :=
      VertexConnected.of_iso
        (SimpleGraph.Embedding.comap e G).isoInduceRange k hconnE
    let φ : (Set.range e) ≃ (J : Set V) := Equiv.setCongr hrange.symm
    let iso : G.induce (Set.range e) ≃g G.induce (J : Set V) := {
      toEquiv := φ
      map_rel_iff' := by
        intro x y
        rfl
    }
    exact VertexConnected.of_iso iso k hconnRange
  exact ⟨J, hJsub, hJsize, hconnJ⟩

/-- A `K_t`-minor-free residual of chromatic number above twice the SC
density threshold contains a small `k`-connected induced graph. -/
theorem exists_small_connected_piece_inside_of_SC
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t k N : ℕ) (ht : 3 ≤ t) (htk : t ≤ k)
    (hminor : ¬ HasCliqueMinor G t)
    (hsize : (480 * 6400 : ℝ)^2 * (t : ℝ) *
      (Real.log (t : ℝ))^3 ≤ (N : ℝ))
    (R : Finset V)
    (hχ : 2 * (480 * 6400 * k) <
      chromatic (G.induce (R : Set V))) :
    ∃ J : Finset V, J ⊆ R ∧ J.card ≤ N ∧
      VertexConnected (G.induce (J : Set V)) k := by
  apply exists_small_connected_piece_inside_of_chromatic_gt G
    (480 * 6400 * k) k N _ R hχ
  intro S hS hdense
  exact sc_piece_inside G t k N ht htk hminor hsize S hS hdense

/-- The checked small-connected theorem supplies the finder in the maximal
packing argument. The local chromatic bound is stated at the union size that
the packing actually uses. -/
theorem exists_disjoint_small_connected_pieces_of_SC
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t k r N q : ℕ) (ht : 3 ≤ t) (htk : t ≤ k)
    (hminor : ¬ HasCliqueMinor G t)
    (hsize : (480 * 6400 : ℝ)^2 * (t : ℝ) *
      (Real.log (t : ℝ))^3 ≤ (N : ℝ))
    (hlocal : ∀ U : Finset V, U.card ≤ r * N →
      chromatic (G.induce (U : Set V)) ≤ q)
    (hχ : q + 2 * (480 * 6400 * k) < chromatic G) :
    ∃ J : Fin r → Finset V,
      (∀ i, (J i).card ≤ N ∧
        VertexConnected (G.induce (J i : Set V)) k) ∧
      (Pairwise fun i j => Disjoint (J i) (J j)) := by
  apply exists_disjoint_small_connected_pieces G r k N q
    (2 * (480 * 6400 * k)) ?_ hlocal hχ
  intro R hR
  exact exists_small_connected_piece_inside_of_SC
    G t k N ht htk hminor hsize R hR

end Inseparability
end HadwigerLean


