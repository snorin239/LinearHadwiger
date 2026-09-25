import HadwigerLean.Graph.Linkedness.Massed
import Mathlib.Tactic

/-! Convert the F.b contraction root correction into the deletion-shore budget. -/

namespace HadwigerLean.RootedDensity

universe u

/-- Common neighbors plus the noncommon root neighbors of an outside
endpoint equal outside common neighbors plus all its other root neighbors. -/
theorem common_add_rootCorrection_eq_outside_common_add_rootNeighbors
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (u v : V) :
    (G.neighborFinset u ∩ G.neighborFinset v).card +
      (((G.neighborFinset v ∩ X.erase u) \ G.neighborFinset u).card) =
      (((G.neighborFinset u ∩ G.neighborFinset v) \ X).card) +
        (G.neighborFinset v ∩ X.erase u).card := by
  classical
  let C := G.neighborFinset u ∩ G.neighborFinset v
  let R := G.neighborFinset v ∩ X.erase u
  have hCX : C ∩ X = R ∩ C := by
    ext z
    constructor
    · intro hz
      have hzC : z ∈ C := (Finset.mem_inter.mp hz).1
      have hzX : z ∈ X := (Finset.mem_inter.mp hz).2
      have hzu : z ≠ u := by
        intro heq
        subst z
        have hadj : G.Adj u u :=
          (G.mem_neighborFinset u u).mp (Finset.mem_inter.mp hzC).1
        exact hadj.ne rfl
      apply Finset.mem_inter.mpr
      constructor
      · apply Finset.mem_inter.mpr
        exact ⟨(Finset.mem_inter.mp hzC).2,
          Finset.mem_erase.mpr ⟨hzu,hzX⟩⟩
      · exact hzC
    · intro hz
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hz).2,
          (Finset.mem_erase.mp (Finset.mem_inter.mp
            (Finset.mem_inter.mp hz).1).2).2⟩
  have hRC : R \ C = R \ G.neighborFinset u := by
    ext z
    simp [C,R,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  have hC := Finset.card_sdiff_add_card_inter C X
  have hR := Finset.card_sdiff_add_card_inter R C
  rw [hCX] at hC
  rw [hRC] at hR
  dsimp [C,R] at hC hR
  omega

end HadwigerLean.RootedDensity
