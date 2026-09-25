import HadwigerLean.Inseparability.SmallPieces
import HadwigerLean.Graph.CliqueDensity.Coloring
import HadwigerLean.Woven.ThreeChildGN
import HadwigerLean.Graph.ContractionEdges
import Mathlib.Tactic

/-!
# A dense-piece theorem supplies the chromatic packing finder

The small-connected-subgraph theorem is naturally stated with an edge-density
premise.  This lemma packages its contrapositive with greedy coloring, so the
packing argument can ask for a piece in each colorful residual set.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If every induced subgraph with at least `c` edges per vertex contains a
small `k`-connected piece, then chromatic number greater than `2*c` forces
such a piece. -/
theorem exists_small_connected_piece_of_chromatic_gt
    (G : SimpleGraph V) [DecidableRel G.Adj] (c k N : ℕ)
    (hdense : ∀ R : Finset V,
      R.Nonempty → c * R.card ≤ edgeCount (G.induce (R : Set V)) →
      ∃ J : Finset V, J ⊆ R ∧ J.card ≤ N ∧
        VertexConnected (G.induce (J : Set V)) k)
    (hχ : 2 * c < chromatic G) :
    ∃ J : Finset V, J.card ≤ N ∧
      VertexConnected (G.induce (J : Set V)) k := by
  classical
  by_contra hnone
  push Not at hnone
  have hlow : ∀ R : Finset V, R.Nonempty →
      edgeCount (G.induce (R : Set V)) < c * R.card := by
    intro R hR
    by_contra h
    have he : c * R.card ≤ edgeCount (G.induce (R : Set V)) := by omega
    obtain ⟨J, _, hJcard, hJconn⟩ := hdense R hR he
    exact hnone J hJcard hJconn
  have hcolor : G.Colorable (2 * c) := by
    apply colorable_of_induced_low_degree G (2 * c)
    intro R hR
    have hcard : 0 < Fintype.card (R : Set V) := by
      letI : Nonempty (R : Set V) := ⟨⟨hR.choose, hR.choose_spec⟩⟩
      exact Fintype.card_pos
    have hedges : (edgeCount (G.induce (R : Set V)) : ℝ) <
        (c : ℝ) * (Fintype.card (R : Set V) : ℝ) := by
      have hcardR : Fintype.card (R : Set V) = R.card := by
        apply Fintype.card_of_finset' R
        intro x
        rfl
      rw [hcardR]
      exact_mod_cast hlow R hR
    obtain ⟨v, hv⟩ :=
      exists_degree_lt_twice_of_edgeCount_lt
        (G.induce (R : Set V)) (c : ℝ) hcard hedges
    exact ⟨v, by exact_mod_cast hv⟩
  have hchrom : chromatic G ≤ 2 * c :=
    (chromatic_le_iff_colorable G _).mpr hcolor
  omega

/-- The same finder inside any prescribed residual vertex set. -/
theorem exists_small_connected_piece_inside_of_chromatic_gt
    (G : SimpleGraph V) [DecidableRel G.Adj] (c k N : ℕ)
    (hdense : ∀ R : Finset V,
      R.Nonempty → c * R.card ≤ edgeCount (G.induce (R : Set V)) →
      ∃ J : Finset V, J ⊆ R ∧ J.card ≤ N ∧
        VertexConnected (G.induce (J : Set V)) k)
    (R : Finset V)
    (hχ : 2 * c < chromatic (G.induce (R : Set V))) :
    ∃ J : Finset V, J ⊆ R ∧ J.card ≤ N ∧
      VertexConnected (G.induce (J : Set V)) k := by
  classical
  -- Apply the preceding theorem to every induced subset by restricting the
  -- density input.  Its witness is returned in the ambient vertex type.
  by_contra hnone
  push Not at hnone
  have hlow : ∀ S : Finset (R : Set V), S.Nonempty →
      edgeCount ((G.induce (R : Set V)).induce (S : Set (R : Set V))) <
        c * S.card := by
    intro S hS
    by_contra h
    have he : c * S.card ≤
        edgeCount ((G.induce (R : Set V)).induce (S : Set (R : Set V))) := by
      omega
    let T : Finset V := S.image Subtype.val
    have hTcard : T.card = S.card := Finset.card_image_of_injective _ Subtype.val_injective
    have hTsub : T ⊆ R := by
      intro v hv
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
      exact w.property
    have hiso : ((G.induce (R : Set V)).induce (S : Set (R : Set V))) ≃g
        G.induce (T : Set V) := Woven.nestedInducedIso G R S
    have hTedges : edgeCount (G.induce (T : Set V)) =
        edgeCount ((G.induce (R : Set V)).induce (S : Set (R : Set V))) := by
      exact edgeCount_eq_of_iso hiso.symm
    have hdT : c * T.card ≤ edgeCount (G.induce (T : Set V)) := by
      rw [hTcard, hTedges]
      exact he
    have hTne : T.Nonempty := Finset.Nonempty.image hS _
    obtain ⟨J, hJT, hJcard, hJconn⟩ := hdense T hTne hdT
    exact hnone J (hJT.trans hTsub) hJcard hJconn
  have hcolor : (G.induce (R : Set V)).Colorable (2 * c) := by
    apply colorable_of_induced_low_degree (G.induce (R : Set V)) (2 * c)
    intro S hS
    have hcard : 0 < Fintype.card (S : Set (R : Set V)) := by
      letI : Nonempty (S : Set (R : Set V)) := ⟨⟨hS.choose, hS.choose_spec⟩⟩
      exact Fintype.card_pos
    have hedges :
        (edgeCount ((G.induce (R : Set V)).induce (S : Set (R : Set V))) : ℝ) <
        (c : ℝ) * (Fintype.card (S : Set (R : Set V)) : ℝ) := by
      have hcardS : Fintype.card (S : Set (R : Set V)) = S.card := by
        apply Fintype.card_of_finset' S
        intro x
        rfl
      rw [hcardS]
      exact_mod_cast hlow S hS
    obtain ⟨v, hv⟩ :=
      exists_degree_lt_twice_of_edgeCount_lt
        ((G.induce (R : Set V)).induce (S : Set (R : Set V)))
        (c : ℝ) hcard hedges
    exact ⟨v, by exact_mod_cast hv⟩
  have hchrom : chromatic (G.induce (R : Set V)) ≤ 2 * c :=
    (chromatic_le_iff_colorable _ _).mpr hcolor
  omega

end Inseparability
end HadwigerLean






