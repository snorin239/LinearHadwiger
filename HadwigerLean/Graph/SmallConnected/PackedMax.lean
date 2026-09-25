import HadwigerLean.Graph.SmallConnected.PackedEmpty
import HadwigerLean.Graph.SmallConnected.PackedCount
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic

/-!
# A maximal family of low-loss connected blocks
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- An admissible family has uniform block size and total contraction
loss at most `p` times the number of removed vertices. -/
noncomputable def GoodPackedFamily
    (G : SimpleGraph V) (h p : ℕ) (F : ConnectedBlockFamily G) : Prop := by
  classical
  exact (∀ B ∈ F.blocks, B.card = h) ∧
    edgeCount G ≤ edgeCount F.quotient + p * F.blocks.card * (h - 1) ∧
    edgeCount F.quotient ≤ edgeCount G

theorem goodPackedFamily_empty
    (G : SimpleGraph V) (h p : ℕ) :
    GoodPackedFamily G h p (emptyConnectedBlockFamily G) := by
  classical
  unfold GoodPackedFamily
  constructor
  · intro B hB
    simp [emptyConnectedBlockFamily] at hB
  · constructor
    · change edgeCount G ≤
        edgeCount (emptyConnectedBlockFamily G).quotient + p * 0 * (h - 1)
      simpa [emptyConnectedBlockFamily_edgeCount]
    · exact le_of_eq (emptyConnectedBlockFamily_edgeCount G)

/-- Finite maximality of the number of admissible disjoint blocks. -/
theorem exists_maximal_good_packed_family
    (G : SimpleGraph V) (h p : ℕ) :
    ∃ F : ConnectedBlockFamily G,
      GoodPackedFamily G h p F ∧
      ∀ F' : ConnectedBlockFamily G,
        GoodPackedFamily G h p F' → F'.blocks.card ≤ F.blocks.card := by
  classical
  let P : Set (Finset (Finset V)) :=
    {B | ∃ F : ConnectedBlockFamily G,
      F.blocks = B ∧ GoodPackedFamily G h p F}
  have hfinite : P.Finite := Set.toFinite P
  have hnonempty : P.Nonempty := by
    refine ⟨∅, ?_⟩
    exact ⟨emptyConnectedBlockFamily G, rfl, goodPackedFamily_empty G h p⟩
  obtain ⟨B, hB, hmax⟩ :=
    hfinite.exists_maximalFor (fun B : Finset (Finset V) => B.card) P hnonempty
  obtain ⟨F, hFB, hgood⟩ := hB
  refine ⟨F, hgood, ?_⟩
  intro F' hgood'
  by_contra hnot
  have hlt : F.blocks.card < F'.blocks.card := Nat.lt_of_not_ge hnot
  have hP' : F'.blocks ∈ P := ⟨F', rfl, hgood'⟩
  have hle : B.card ≤ F'.blocks.card := by simpa [← hFB] using hlt.le
  have hback := hmax hP' hle
  change F'.blocks.card ≤ B.card at hback
  rw [← hFB] at hback
  omega

/-- An admissible family of `h`-sets removes at most `N` vertices. -/
theorem GoodPackedFamily.savings_le_card
    (G : SimpleGraph V) (h p : ℕ) (hh : 1 ≤ h)
    (F : ConnectedBlockFamily G) (hF : GoodPackedFamily G h p F) :
    F.blocks.card * (h - 1) ≤ Fintype.card V := by
  have hsize := hF.1
  have hcard := F.vertex_card_add_savings hsize hh
  omega

/-- Exact initial edge count and admissibility imply at least 90 percent
of the original edges survive the simultaneous contraction. -/
theorem GoodPackedFamily.retained_edges
    (G : SimpleGraph V) (h p : ℕ) (hh : 1 ≤ h)
    (F : ConnectedBlockFamily G) (hF : GoodPackedFamily G h p F)
    (N : ℕ) (hN : Fintype.card V = N)
    (hexact : edgeCount G = 10 * p * N) :
    9 * p * N ≤ edgeCount F.quotient := by
  classical
  have hsav := hF.savings_le_card G h p hh
  rw [hN] at hsav
  have hmul := Nat.mul_le_mul_left p hsav
  have hgood := hF.2.1
  rw [hexact] at hgood
  nlinarith

end HadwigerLean
