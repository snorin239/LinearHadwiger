import HadwigerLean.Graph.SmallConnected.PackedLift
import HadwigerLean.Graph.ContractionEdges
import Mathlib.Tactic

/-!
# The empty connected block family
-/

namespace HadwigerLean

universe u
variable {V : Type u} [DecidableEq V]

noncomputable def emptyConnectedBlockFamily (G : SimpleGraph V) :
    ConnectedBlockFamily G where
  blocks := ∅
  connected := by intro B hB; simp at hB
  disjoint := by intro B hB; simp at hB

theorem emptyConnectedBlockFamily_covered (G : SimpleGraph V) :
    (emptyConnectedBlockFamily G).covered = ∅ := by
  simp [emptyConnectedBlockFamily, ConnectedBlockFamily.covered]

/-- Contracting no blocks gives the original graph, up to renaming. -/
noncomputable def emptyConnectedBlockFamilyIso (G : SimpleGraph V) :
    G ≃g (emptyConnectedBlockFamily G).quotient where
  toEquiv := {
    toFun v := .inr ⟨v, by simp [emptyConnectedBlockFamily_covered]⟩
    invFun q := by
      cases q with
      | inl B => exact False.elim (by simpa [emptyConnectedBlockFamily] using B.2)
      | inr x => exact x.1
    left_inv := by intro v; rfl
    right_inv := by
      intro q
      cases q with
      | inl B => exact False.elim (by simpa [emptyConnectedBlockFamily] using B.2)
      | inr x => apply congrArg Sum.inr; apply Subtype.ext; rfl
  }
  map_rel_iff' := by
    intro x y
    have hx : x ∉ (emptyConnectedBlockFamily G).covered := by
      simp [emptyConnectedBlockFamily_covered]
    have hy : y ∉ (emptyConnectedBlockFamily G).covered := by
      simp [emptyConnectedBlockFamily_covered]
    change (emptyConnectedBlockFamily G).quotient.Adj
        (.inr ⟨x, hx⟩) (.inr ⟨y, hy⟩) ↔ G.Adj x y
    constructor
    · rintro ⟨_, a, ha, b, hb, hab⟩
      have hax : a = x := by simpa [ConnectedBlockFamily.partition,
        ConnectedBlockFamily.block] using ha
      have hby : b = y := by simpa [ConnectedBlockFamily.partition,
        ConnectedBlockFamily.block] using hb
      simpa [hax, hby] using hab
    · intro hxy
      have hne : x ≠ y := G.ne_of_adj hxy
      exact ⟨by simpa using hne,
        x, by simp [ConnectedBlockFamily.partition, ConnectedBlockFamily.block],
        y, by simp [ConnectedBlockFamily.partition, ConnectedBlockFamily.block], hxy⟩

theorem emptyConnectedBlockFamily_edgeCount
    [Fintype V] (G : SimpleGraph V) :
    edgeCount (emptyConnectedBlockFamily G).quotient = edgeCount G :=
  (edgeCount_eq_of_iso (emptyConnectedBlockFamilyIso G)).symm

end HadwigerLean
