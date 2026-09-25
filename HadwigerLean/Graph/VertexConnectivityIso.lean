import HadwigerLean.Graph.VertexConnectivity
import Mathlib.Tactic

/-!
# Vertex connectivity is invariant under finite graph isomorphisms
-/

namespace HadwigerLean

/-- Isomorphic finite graphs have the same vertex-connectivity guarantees. -/
theorem VertexConnected.of_iso
    {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (k : ℕ) (hG : VertexConnected G k) :
    VertexConnected H k := by
  classical
  have horder : Fintype.card V = Fintype.card W := Fintype.card_congr e.toEquiv
  have horderG := hG.order_gt
  refine ⟨by omega, ?_⟩
  intro U hU
  let S : Finset V := U.image e.symm
  have hScard : S.card = U.card :=
    Finset.card_image_of_injective U e.symm.injective
  have hS : S.card < k := by omega
  have hconn := hG.connected_delete S hS
  let φ : (G.induce (S : Set V)ᶜ) →g (H.induce (U : Set W)ᶜ) := {
    toFun := fun x => ⟨e x.1, by
      intro hu
      exact x.2 (Finset.mem_image.mpr ⟨e x.1, hu, e.symm_apply_apply x.1⟩)⟩
    map_rel' := by
      intro x y hxy
      exact e.map_rel_iff.mpr hxy
  }
  have hsurj : Function.Surjective φ := by
    intro y
    have hpre : e.symm y.1 ∉ S := by
      intro hs
      obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hs
      have hyu : y.1 = u := by
        have h := congrArg e heq
        simpa using h.symm
      exact y.2 (hyu ▸ hu)
    refine ⟨⟨e.symm y.1, hpre⟩, ?_⟩
    apply Subtype.ext
    simp [φ]
  exact hconn.map φ hsurj


/-- Graph isomorphisms preserve vertex degree. -/
theorem degree_eq_of_iso
    {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) (v : V) : G.degree v = H.degree (e v) := by
  classical
  let φ : G.neighborSet v ≃ H.neighborSet (e v) := {
    toFun := fun x => ⟨e x.1, e.map_rel_iff.mpr x.2⟩
    invFun := fun y => ⟨e.symm y.1, by
      have h := e.symm.map_rel_iff.mpr y.2
      simpa using h⟩
    left_inv := by
      intro x
      apply Subtype.ext
      simp
    right_inv := by
      intro y
      apply Subtype.ext
      simp
  }
  calc
    G.degree v = Fintype.card (G.neighborSet v) := (G.card_neighborSet_eq_degree v).symm
    _ = Fintype.card (H.neighborSet (e v)) := Fintype.card_congr φ
    _ = H.degree (e v) := H.card_neighborSet_eq_degree (e v)

end HadwigerLean
