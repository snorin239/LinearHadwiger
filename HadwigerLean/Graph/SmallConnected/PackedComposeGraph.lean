import HadwigerLean.Graph.SmallConnected.PackedComposeVertices
import HadwigerLean.Graph.SmallConnected.ContractionCount
import Mathlib.Tactic

/-!
# Adjacency compatibility for a second connected-set contraction
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} (F : ConnectedBlockFamily G)

private theorem lift_block_union
    (H : Finset V) (hdisj : Disjoint H F.covered) (a : V) :
    a ∈ H ↔ ∃ q ∈ F.singletonLift H, a ∈ F.block q := by
  constructor
  · intro ha
    have haout : a ∉ F.covered := by
      intro hacov
      exact (Finset.disjoint_left.mp hdisj ha) hacov
    refine ⟨.inr ⟨a, haout⟩,
      (F.mem_singletonLift_inr H ⟨a, haout⟩).mpr ha, ?_⟩
    simp [ConnectedBlockFamily.block]
  · rintro ⟨q, hq, ha⟩
    cases q with
    | inl B => exact False.elim (F.not_mem_singletonLift_inl H B hq)
    | inr x =>
        have hxH := (F.mem_singletonLift_inr H x).mp hq
        have hax : a = x.1 := by simpa [ConnectedBlockFamily.block] using ha
        simpa [hax] using hxH

private theorem secondAdded_block_none
    (H : Finset V) (hconn : (G.induce (H : Set V)).Connected)
    (hdisj : Disjoint H F.covered) :
    (F.add H hconn hdisj).block
      ((F.secondAddedEquiv H hconn hdisj) none) = (H : Set V) := rfl

private theorem secondAdded_block_some
    (H : Finset V) (hconn : (G.induce (H : Set V)).Connected)
    (hdisj : Disjoint H F.covered)
    (q : {q : F.Vertex // q ∉ (F.singletonLift H : Set F.Vertex)}) :
    (F.add H hconn hdisj).block
      ((F.secondAddedEquiv H hconn hdisj) (some q)) = F.block q.1 := by
  cases q with
  | mk q hq =>
      cases q with
      | inl B => rfl
      | inr x => rfl

private theorem secondAdded_adj_some_some
    (H : Finset V) (hconn : (G.induce (H : Set V)).Connected)
    (hdisj : Disjoint H F.covered)
    (q r : {q : F.Vertex // q ∉ (F.singletonLift H : Set F.Vertex)}) :
    (connectedSetContractionGraph F.quotient
      (F.singletonLift H : Set F.Vertex)
      (F.singletonLift_connected H hdisj hconn)).Adj (some q) (some r) ↔
    (F.add H hconn hdisj).quotient.Adj
      ((F.secondAddedEquiv H hconn hdisj) (some q))
      ((F.secondAddedEquiv H hconn hdisj) (some r)) := by
  let e := F.secondAddedEquiv H hconn hdisj
  rw [connectedSetContraction_adj_some_some]
  have hne : q.1 ≠ r.1 ↔ e (some q) ≠ e (some r) := by
    constructor
    · intro hqr heq
      have hsame : (some q : ConnectedSetContractionVertex (F.singletonLift H : Set F.Vertex)) = some r := e.injective heq
      exact hqr (congrArg Subtype.val (Option.some.inj hsame))
    · intro heq hqr
      apply heq
      have hsub : q = r := Subtype.ext hqr
      rw [hsub]
  change (q.1 ≠ r.1 ∧
      ∃ a ∈ F.block q.1, ∃ b ∈ F.block r.1, G.Adj a b) ↔
    (e (some q) ≠ e (some r) ∧
      ∃ a ∈ (F.add H hconn hdisj).block (e (some q)),
        ∃ b ∈ (F.add H hconn hdisj).block (e (some r)), G.Adj a b)
  rw [secondAdded_block_some F H hconn hdisj q,
    secondAdded_block_some F H hconn hdisj r]
  exact and_congr hne Iff.rfl

private theorem secondAdded_adj_none_some
    (H : Finset V) (hconn : (G.induce (H : Set V)).Connected)
    (hdisj : Disjoint H F.covered)
    (q : {q : F.Vertex // q ∉ (F.singletonLift H : Set F.Vertex)}) :
    (connectedSetContractionGraph F.quotient
      (F.singletonLift H : Set F.Vertex)
      (F.singletonLift_connected H hdisj hconn)).Adj none (some q) ↔
    (F.add H hconn hdisj).quotient.Adj
      ((F.secondAddedEquiv H hconn hdisj) none)
      ((F.secondAddedEquiv H hconn hdisj) (some q)) := by
  let e := F.secondAddedEquiv H hconn hdisj
  rw [connectedSetContraction_adj_none_some]
  have hne : e none ≠ e (some q) := e.injective.ne (by simp)
  change (∃ p ∈ F.singletonLift H, F.quotient.Adj p q.1) ↔
    (e none ≠ e (some q) ∧
      ∃ a ∈ (F.add H hconn hdisj).block (e none),
        ∃ b ∈ (F.add H hconn hdisj).block (e (some q)), G.Adj a b)
  rw [secondAdded_block_none F H hconn hdisj,
    secondAdded_block_some F H hconn hdisj q]
  constructor
  · rintro ⟨p, hp, hpq⟩
    obtain ⟨_, a, ha, b, hb, hab⟩ := hpq
    exact ⟨hne, a, (lift_block_union F H hdisj a).mpr ⟨p, hp, ha⟩,
      b, hb, hab⟩
  · rintro ⟨_, a, ha, b, hb, hab⟩
    obtain ⟨p, hp, haP⟩ := (lift_block_union F H hdisj a).mp ha
    have hpq : p ≠ q.1 := by
      intro heq
      exact q.2 (heq ▸ hp)
    exact ⟨p, hp, ⟨hpq, a, haP, b, hb, hab⟩⟩

/-- Contracting a further connected set of uncovered singleton vertices
+is isomorphic to adding that set to the simultaneous block family. -/
noncomputable def ConnectedBlockFamily.secondAddedIso
    (H : Finset V) (hconn : (G.induce (H : Set V)).Connected)
    (hdisj : Disjoint H F.covered) :
    (connectedSetContractionGraph F.quotient
      (F.singletonLift H : Set F.Vertex)
      (F.singletonLift_connected H hdisj hconn)) ≃g
      (F.add H hconn hdisj).quotient where
  toEquiv := F.secondAddedEquiv H hconn hdisj
  map_rel_iff' := by
    intro i j
    cases i with
    | none =>
        cases j with
        | none => simp
        | some q => exact (secondAdded_adj_none_some F H hconn hdisj q).symm
    | some q =>
        cases j with
        | none =>
            have h := secondAdded_adj_none_some F H hconn hdisj q
            exact ⟨fun hab => (h.mpr hab.symm).symm,
              fun hab => (h.mp hab.symm).symm⟩
        | some r => exact (secondAdded_adj_some_some F H hconn hdisj q r).symm
/-- Exact edge loss when a new uncovered connected block is added to a
simultaneous contraction family. -/
theorem ConnectedBlockFamily.add_edgeCount_add_loss
    (H : Finset V) (hconn : (G.induce (H : Set V)).Connected)
    (hdisj : Disjoint H F.covered)
    [DecidableRel F.quotient.Adj]
    [DecidableRel (connectedSetContractionGraph F.quotient
      (F.singletonLift H : Set F.Vertex)
      (F.singletonLift_connected H hdisj hconn)).Adj] :
    edgeCount (F.add H hconn hdisj).quotient +
      connectedSetContractionLoss F.quotient (F.singletonLift H) =
        edgeCount F.quotient := by
  classical
  have hcount := connectedSetContraction_edgeCount_add_loss
    F.quotient (F.singletonLift H)
    (F.singletonLift_connected H hdisj hconn)
  have hiso := edgeCount_eq_of_iso (F.secondAddedIso H hconn hdisj)
  rw [hiso] at hcount
  exact hcount
end HadwigerLean
