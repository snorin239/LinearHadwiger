import HadwigerLean.ReedSeymour.Egg

/-!
# Absorbing a bipartite connector into a neighboring egg

In Reed and Seymour's odd-path contradiction, the connector has two stable
parity classes. Its heavier class is a yolk of the connector. Depending on
which class is heavier, that yolk joins one of two neighboring eggs.
-/

namespace HadwigerLean

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {w : V → ℝ}

/-- If opposite sides of a bipartite connector avoid the yolks of two eggs,
one of the eggs can absorb the connector. The path argument supplies the
connectivity and no-cross-edge hypotheses at the application point. -/
theorem egg_absorbs_bipartite_connector
    {X₁ X₂ U A B Y₁ Y₂ : Set V}
    (hY₁ : IsYolk G w X₁ Y₁) (hY₂ : IsYolk G w X₂ Y₂)
    (hU : U = A ∪ B) (hAB : Disjoint A B)
    (hA : G.IsIndepSet A) (hB : G.IsIndepSet B)
    (hX₁U : Disjoint X₁ U) (hX₂U : Disjoint X₂ U)
    (hconn₁ : (G.induce (X₁ ∪ U)).Connected)
    (hconn₂ : (G.induce (X₂ ∪ U)).Connected)
    (hcross₁ : ∀ u ∈ Y₁, ∀ v ∈ B, ¬ G.Adj u v)
    (hcross₂ : ∀ u ∈ Y₂, ∀ v ∈ A, ¬ G.Adj u v) :
    IsEgg G w (X₁ ∪ U) ∨ IsEgg G w (X₂ ∪ U) := by
  have hweight : setWeight w U = setWeight w A + setWeight w B := by
    rw [hU, setWeight_union_of_disjoint w hAB]
  rcases le_total (setWeight w A) (setWeight w B) with hle | hle
  · have hBU : IsYolk G w U B := by
      refine ⟨?_, hB, ?_⟩
      · rw [hU]
        exact Set.subset_union_right
      · rw [hweight]
        linarith
    left
    exact ⟨hconn₁, ⟨Y₁ ∪ B,
      hY₁.union_of_no_cross hBU hX₁U hcross₁⟩⟩
  · have hAU : IsYolk G w U A := by
      refine ⟨?_, hA, ?_⟩
      · rw [hU]
        exact Set.subset_union_left
      · rw [hweight]
        linarith
    right
    exact ⟨hconn₂, ⟨Y₂ ∪ A,
      hY₂.union_of_no_cross hAU hX₂U hcross₂⟩⟩

end HadwigerLean
