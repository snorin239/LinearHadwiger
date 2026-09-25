import HadwigerLean.Graph.SmallConnected.PackedAdd
import Mathlib.Tactic

/-!
# Lifting an uncovered vertex set to singleton quotient vertices
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} (F : ConnectedBlockFamily G)

/-- The singleton quotient vertices corresponding to vertices of `H`. -/
noncomputable def ConnectedBlockFamily.singletonLift (H : Finset V) :
    Finset F.Vertex := by
  classical
  exact Finset.univ.filter fun q =>
    match q with
    | .inl _ => False
    | .inr x => x.1 ∈ H

theorem ConnectedBlockFamily.mem_singletonLift_inr
    (H : Finset V) (x : {v : V // v ∉ F.covered}) :
    (Sum.inr x : F.Vertex) ∈ F.singletonLift H ↔ x.1 ∈ H := by
  simp [ConnectedBlockFamily.singletonLift]

theorem ConnectedBlockFamily.not_mem_singletonLift_inl
    (H : Finset V) (B : ↥(F.blocks : Set (Finset V))) :
    (Sum.inl B : F.Vertex) ∉ F.singletonLift H := by
  simp [ConnectedBlockFamily.singletonLift]

noncomputable def ConnectedBlockFamily.singletonLiftEquiv
    (H : Finset V) (hdisj : Disjoint H F.covered) :
    ↥(H : Set V) ≃ ↥(F.singletonLift H : Set F.Vertex) where
  toFun x := by
    have hxout : x.1 ∉ F.covered := by
      intro hc
      exact (Finset.disjoint_left.mp hdisj x.2) hc
    exact ⟨.inr ⟨x.1, hxout⟩,
      (F.mem_singletonLift_inr H ⟨x.1, hxout⟩).mpr x.2⟩
  invFun q := by
    rcases q with ⟨q, hq⟩
    cases q with
    | inl B => exact False.elim (F.not_mem_singletonLift_inl H B hq)
    | inr x => exact ⟨x.1, (F.mem_singletonLift_inr H x).mp hq⟩
  left_inv := by
    intro x
    apply Subtype.ext
    rfl
  right_inv := by
    rintro ⟨q, hq⟩
    cases q with
    | inl B => exact False.elim (F.not_mem_singletonLift_inl H B hq)
    | inr x => rfl

/-- On uncovered singleton vertices the quotient retains exactly the
original adjacency relation. -/
noncomputable def ConnectedBlockFamily.singletonLiftIso
    (H : Finset V) (hdisj : Disjoint H F.covered) :
    (G.induce (H : Set V)) ≃g
      (F.quotient.induce (F.singletonLift H : Set F.Vertex)) where
  toEquiv := F.singletonLiftEquiv H hdisj
  map_rel_iff' := by
    intro x y
    have hxout : x.1 ∉ F.covered := by
      intro hc
      exact (Finset.disjoint_left.mp hdisj x.2) hc
    have hyout : y.1 ∉ F.covered := by
      intro hc
      exact (Finset.disjoint_left.mp hdisj y.2) hc
    change F.quotient.Adj (.inr ⟨x.1, hxout⟩) (.inr ⟨y.1, hyout⟩) ↔
      G.Adj x.1 y.1
    change ((Sum.inr ⟨x.1, hxout⟩ : F.Vertex) ≠
        Sum.inr ⟨y.1, hyout⟩) ∧
      (∃ a ∈ ({x.1} : Set V), ∃ b ∈ ({y.1} : Set V), G.Adj a b) ↔
        G.Adj x.1 y.1
    constructor
    · rintro ⟨_, a, rfl, b, rfl, hab⟩
      exact hab
    · intro hab
      refine ⟨?_, x.1, rfl, y.1, rfl, hab⟩
      intro heq
      exact (G.ne_of_adj hab) (congrArg (fun q : F.Vertex =>
        match q with | .inl _ => x.1 | .inr z => z.1) heq)

theorem ConnectedBlockFamily.singletonLift_connected
    (H : Finset V) (hdisj : Disjoint H F.covered)
    (hconn : (G.induce (H : Set V)).Connected) :
    (F.quotient.induce (F.singletonLift H : Set F.Vertex)).Connected :=
  (F.singletonLiftIso H hdisj).connected_iff.mp hconn

theorem ConnectedBlockFamily.singletonLift_card
    (H : Finset V) (hdisj : Disjoint H F.covered) :
    (F.singletonLift H).card = H.card := by
  have hcard := Fintype.card_congr (F.singletonLiftEquiv H hdisj)
  simpa using hcard.symm

end HadwigerLean
