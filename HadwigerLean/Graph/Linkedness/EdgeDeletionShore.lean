import HadwigerLean.Graph.EdgeIncidenceMono
import HadwigerLean.Graph.Linkedness.Massed
import Mathlib.Tactic

/-!
# Edge deletion preserves the massed shore bound at an edge-tight pair

If an edge has at least as many common neighbors as there are roots,
removing that edge cannot create a new separation whose adhesion is
smaller than the root set. Its possible crossing edge would force every
common neighbor into the adhesion.
-/

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem deleted_adj_of_edge_ne
    (G : SimpleGraph V) (u v x y : V) (hxy : G.Adj x y)
    (hne : s(x, y) ≠ s(u, v)) :
    (G.deleteEdges {s(u, v)}).Adj x y := by
  simpa only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] using
    (show G.Adj x y ∧ s(x, y) ≠ s(u, v) from ⟨hxy, hne⟩)

/-- An edge deletion does not create a low-order separation when the edge
has sufficiently many common neighbors. -/
noncomputable def separation_of_delete_edge_of_common_neighbors
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (u v : V) (huv : G.Adj u v)
    (hcommon : X.card ≤ (G.neighborFinset u ∩ G.neighborFinset v).card)
    (S : VertexSeparation (G.deleteEdges {s(u, v)}))
    (hsmall : Nat.card S.separator < X.card) :
    VertexSeparation G := by
  classical
  let C := G.neighborFinset u ∩ G.neighborFinset v
  have hcommonC : X.card ≤ C.card := hcommon
  have hsep_card : S.separatorFinset.card = Nat.card S.separator := by
    simp [VertexSeparation.separatorFinset]
  have hsep_common (S' : VertexSeparation (G.deleteEdges {s(u, v)})) (huL : u ∈ S'.strictLeft) (hvR : v ∈ S'.strictRight) :
      C ⊆ S'.separatorFinset := by
    intro w hw
    have huw : G.Adj u w :=
      (G.mem_neighborFinset u w).mp (Finset.mem_inter.mp hw).1
    have hvw : G.Adj v w :=
      (G.mem_neighborFinset v w).mp (Finset.mem_inter.mp hw).2
    have hkeep_u : (G.deleteEdges {s(u, v)}).Adj u w := by
      apply deleted_adj_of_edge_ne G u v u w huw
      intro heq
      rcases (Sym2.eq_iff.mp heq) with h | h
      · have hwv : w = v := h.2
        exact hvw.ne hwv.symm
      · have huv' : u = v := h.1
        exact huv.ne huv'
    have hkeep_v : (G.deleteEdges {s(u, v)}).Adj v w := by
      apply deleted_adj_of_edge_ne G u v v w hvw
      intro heq
      rcases (Sym2.eq_iff.mp heq) with h | h
      · have hvu : v = u := h.1
        exact huv.ne hvu.symm
      · have hwu : w = u := h.2
        exact huw.ne hwu.symm
    have hwR : w ∈ S'.right := by
      by_contra hnotR
      have hwL : w ∈ S'.left := by
        have hcov : w ∈ S'.left ∪ S'.right := by rw [S'.cover]; trivial
        exact by rcases hcov with hL | hR; exact hL; exact False.elim (hnotR hR)
      exact (S'.no_cross hwL hnotR hvR.1 hvR.2) hkeep_v.symm
    have hwL : w ∈ S'.left := by
      by_contra hnotL
      exact (S'.no_cross huL.1 huL.2 hwR hnotL) hkeep_u
    exact (S'.mem_separatorFinset w).mpr ⟨hwL, hwR⟩
  have hsep_common_rev (huR : u ∈ S.strictRight) (hvL : v ∈ S.strictLeft) :
      C ⊆ S.separatorFinset := by
    let Sswap : VertexSeparation (G.deleteEdges {s(u, v)}) := {
      left := S.right
      right := S.left
      cover := by simpa only [Set.union_comm] using S.cover
      no_cross := by
        intro x y hxR hxNotL hyL hyNotR hxy
        exact (S.no_cross hyL hyNotR hxR hxNotL) hxy.symm
    }
    have hsub : C ⊆ Sswap.separatorFinset :=
      hsep_common Sswap huR hvL
    simpa [VertexSeparation.separatorFinset, VertexSeparation.separator,
      Sswap, and_comm, Finset.inter_comm] using hsub
  refine {
    left := S.left
    right := S.right
    cover := S.cover
    no_cross := ?_
  }
  intro x y hxL hxNotR hyR hyNotL hxy
  have hdeleted : ¬ (G.deleteEdges {s(u, v)}).Adj x y :=
    S.no_cross hxL hxNotR hyR hyNotL
  have hed : s(x, y) = s(u, v) := by
    by_contra hne
    exact hdeleted (deleted_adj_of_edge_ne G u v x y hxy hne)
  rcases (Sym2.eq_iff.mp hed) with h | h
  · have hxu : x = u := h.1
    have hyv : y = v := h.2
    have hsub : C ⊆ S.separatorFinset := by
      subst x
      subst y
      exact hsep_common S ⟨hxL, hxNotR⟩ ⟨hyR, hyNotL⟩
    have hle := Finset.card_le_card hsub
    omega
  · have hxv : x = v := h.1
    have hyu : y = u := h.2
    have hsub : C ⊆ S.separatorFinset := by
      subst x
      subst y
      exact hsep_common_rev ⟨hyR, hyNotL⟩ ⟨hxL, hxNotR⟩
    have hle := Finset.card_le_card hsub
    omega

/-- The second massed-pair condition survives deleting a single
edge with at least `|X|` common neighbors. -/
theorem massed_shore_delete_edge
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (α : ℝ) (hm : MassedPair G (X : Set V) α)
    (u v : V) (huv : G.Adj u v)
    (hcommon : X.card ≤ (G.neighborFinset u ∩ G.neighborFinset v).card)
    (S : VertexSeparation (G.deleteEdges {s(u, v)}))
    (hroot : (X : Set V) ⊆ S.left)
    (hsmall : Nat.card S.separator < Nat.card (X : Set V)) :
    (edgeIncidenceSetCount (G.deleteEdges {s(u, v)}) S.strictRight : ℝ) ≤
      α * (Nat.card S.strictRight : ℝ) := by
  classical
  let T : VertexSeparation G :=
    separation_of_delete_edge_of_common_neighbors G X u v huv hcommon S
      (by simpa using hsmall)
  have hshore := hm.shore T hroot hsmall
  have hle := edgeIncidenceSetCount_deleteEdges_le G
    ({s(u, v)} : Set (Sym2 V)) S.strictRight
  exact (by exact_mod_cast hle :
    (edgeIncidenceSetCount (G.deleteEdges {s(u, v)}) S.strictRight : ℝ) ≤
      (edgeIncidenceSetCount G S.strictRight : ℝ)).trans hshore

/-- Edges of a graph incident to a vertex set, viewed in the common
ambient symmetric-pair type. -/
private def incidentSym2 (G : SimpleGraph V) (S : Set V) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ ∃ w ∈ S, w ∈ e}

private theorem edgeIncidenceSetCount_eq_incident_ncard
    (G : SimpleGraph V) (S : Set V) :
    edgeIncidenceSetCount G S = (incidentSym2 G S).ncard := by
  let e : edgeIncidenceSet G S ≃ incidentSym2 G S := {
    toFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
    invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
  }
  exact Nat.card_congr e

/-- Deleting an existing edge meeting the outside of `X` removes exactly
one edge from the outside-incidence count. -/
theorem edgeIncidenceSetCount_delete_edge_add_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (u v : V) (huv : G.Adj u v)
    (hout : u ∉ X ∨ v ∉ X) :
    edgeIncidenceSetCount (G.deleteEdges {s(u, v)}) (X : Set V)ᶜ + 1 =
      edgeIncidenceSetCount G (X : Set V)ᶜ := by
  classical
  let e : Sym2 V := s(u, v)
  let S : Set V := (X : Set V)ᶜ
  have hmem : e ∈ incidentSym2 G S := by
    refine ⟨by simpa [e] using huv, ?_⟩
    rcases hout with hu | hv
    · exact ⟨u, by simpa [S] using hu, by simp [e]⟩
    · exact ⟨v, by simpa [S] using hv, by simp [e]⟩
  have hset : incidentSym2 (G.deleteEdges {s(u, v)}) S =
      incidentSym2 G S \ {e} := by
    ext f
    simp [incidentSym2, SimpleGraph.edgeSet_deleteEdges, e]
    tauto
  rw [edgeIncidenceSetCount_eq_incident_ncard,
    edgeIncidenceSetCount_eq_incident_ncard, hset]
  exact Set.ncard_sdiff_singleton_add_one hmem (by toFinite_tac)
/-- The exact global incidence count (D.3) at an edge-tight massed pair.
Minimality supplies failure of the strict global inequality after one
exterior edge is deleted; the original pair has the strict inequality. -/
theorem massed_global_edge_tight
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (r : ℕ)
    (hm : MassedPair G (X : Set V) (r : ℝ))
    (u v : V) (huv : G.Adj u v)
    (hout : u ∉ X ∨ v ∉ X)
    (hfail : ¬ ((r : ℝ) * (Nat.card {w : V // w ∉ (X : Set V)} : ℝ) <
      (edgeIncidenceSetCount (G.deleteEdges {s(u, v)}) (X : Set V)ᶜ : ℝ))) :
    edgeIncidenceSetCount G (X : Set V)ᶜ =
      r * ((X : Set V)ᶜ).ncard + 1 := by
  have hdrop := edgeIncidenceSetCount_delete_edge_add_one G X u v huv hout
  have hN : Nat.card {w : V // w ∉ (X : Set V)} =
      ((X : Set V)ᶜ).ncard := rfl
  have hglobal : r * ((X : Set V)ᶜ).ncard <
      edgeIncidenceSetCount G (X : Set V)ᶜ := by
    change r * Nat.card {w : V // w ∉ (X : Set V)} <
      edgeIncidenceSetCount G (X : Set V)ᶜ
    exact_mod_cast hm.global
  have hfailNat : edgeIncidenceSetCount
      (G.deleteEdges {s(u, v)}) (X : Set V)ᶜ ≤
      r * ((X : Set V)ᶜ).ncard := by
    have hf := le_of_not_gt hfail
    change edgeIncidenceSetCount (G.deleteEdges {s(u, v)})
      (X : Set V)ᶜ ≤ r * Nat.card {w : V // w ∉ (X : Set V)}
    exact_mod_cast hf
  omega

end Linkedness
end HadwigerLean
