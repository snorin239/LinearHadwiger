import HadwigerLean.Graph.DensityConnectivity
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Tactic

namespace HadwigerLean

/-- Deleting a left-side vertex preserves a bipartition and updates its
part sizes and edge count exactly. -/
theorem bipartite_vertex_deletion_data
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hcover : A ∪ B = Finset.univ) (v : V) (hv : v ∈ A) :
    let S : Set V := ({v} : Set V)ᶜ
    let A' : Finset S := Finset.univ.filter (fun x => (x : V) ∈ A)
    let B' : Finset S := Finset.univ.filter (fun x => (x : V) ∈ B)
    (G.induce S).IsBipartiteWith (A' : Set S) (B' : Set S) ∧
      A'.card + 1 = A.card ∧ B'.card = B.card ∧
      A' ∪ B' = Finset.univ ∧
      edgeCount (G.induce S) + G.degree v = edgeCount G := by
  classical
  intro S A' B'
  have hvB : v ∉ B := by
    exact (Set.disjoint_left.mp hG.disjoint) hv
  have hAimage : A'.image Subtype.val = A.erase v := by
    ext x
    simp only [Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨y,hy,hyx⟩
      have hyA : (y : V) ∈ A := by simpa [A'] using hy
      have hyv : (y : V) ≠ v := y.property
      exact ⟨by simpa [hyx] using hyv, by simpa [hyx] using hyA⟩
    · rintro ⟨hxv,hxA⟩
      refine ⟨⟨x, ?_⟩, ?_, rfl⟩
      · exact hxv
      · simp [A',hxA]
  have hBimage : B'.image Subtype.val = B := by
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y,hy,hyx⟩
      have hyB : (y : V) ∈ B := by simpa [B'] using hy
      simpa [hyx] using hyB
    · intro hxB
      refine ⟨⟨x, ?_⟩, ?_, rfl⟩
      · exact ne_of_mem_of_not_mem hxB hvB
      · simp [B',hxB]
  have hAcard : A'.card + 1 = A.card := by
    have hc : A'.card = (A.erase v).card := by
      rw [← hAimage]
      exact (Finset.card_image_of_injective _ Subtype.val_injective).symm
    rw [hc, Finset.card_erase_of_mem hv]
    have hApos : 0 < A.card := Finset.card_pos.mpr ⟨v,hv⟩
    omega
  have hBcard : B'.card = B.card := by
    rw [← hBimage]
    exact (Finset.card_image_of_injective _ Subtype.val_injective).symm
  have hcover' : A' ∪ B' = Finset.univ := by
    ext x
    have hx : (x : V) ∈ A ∪ B := by rw [hcover]; simp
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    rcases Finset.mem_union.mp hx with hA | hB
    · exact Or.inl (by simpa [A'] using hA)
    · exact Or.inr (by simpa [B'] using hB)
  have hbip : (G.induce S).IsBipartiteWith (A' : Set S) (B' : Set S) := by
    refine ⟨?_,?_⟩
    · apply Set.disjoint_left.mpr
      intro x hxA hxB
      exact (Set.disjoint_left.mp hG.disjoint)
        (by simpa [A'] using hxA) (by simpa [B'] using hxB)
    · intro x y hxy
      rcases hG.mem_of_adj hxy with hAB | hBA
      · exact Or.inl ⟨by simpa [A'] using hAB.1, by simpa [B'] using hAB.2⟩
      · exact Or.inr ⟨by simpa [B'] using hBA.1, by simpa [A'] using hBA.2⟩
  exact ⟨hbip,hAcard,hBcard,hcover',edgeCount_induce_compl_singleton_add_degree G v⟩

end HadwigerLean



