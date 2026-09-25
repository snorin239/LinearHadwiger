import HadwigerLean.Graph.ChromaticSlice
import HadwigerLean.ReedSeymour.PathBipartite

/-!
# Reuse two colors across anticomplete pieces

The cheap-tree induction adjoins a chordless path whose unmarked interior has
no edge to the old piece. Both remainders can reuse the same two colors.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

/-- Two induced sets of chromatic number at most two can reuse a palette when
there are no edges between them. -/
theorem chromatic_union_le_two_of_no_cross
    (A B : Finset V)
    (hA : chromatic (G.induce (A : Set V)) ≤ 2)
    (hB : chromatic (G.induce (B : Set V)) ≤ 2)
    (hno : ∀ {a b : V}, a ∈ A → b ∈ B → ¬ G.Adj a b) :
    chromatic (G.induce ((A ∪ B : Finset V) : Set V)) ≤ 2 := by
  classical
  obtain ⟨cA⟩ := (chromatic_le_iff_colorable _ _).mp hA
  obtain ⟨cB⟩ := (chromatic_le_iff_colorable _ _).mp hB
  apply (chromatic_le_iff_colorable _ _).mpr
  refine ⟨SimpleGraph.Coloring.mk
    (fun x => if hx : x.1 ∈ A then cA ⟨x.1,hx⟩
      else cB ⟨x.1,?_⟩) ?_⟩
  · exact (Finset.mem_union.mp x.2).resolve_left hx
  · intro x y hxy
    dsimp
    by_cases hxA : x.1 ∈ A
    · by_cases hyA : y.1 ∈ A
      · have hab : (G.induce (A : Set V)).Adj ⟨x.1,hxA⟩ ⟨y.1,hyA⟩ := hxy
        simpa [hxA,hyA] using (cA.valid hab)
      · have hyB : y.1 ∈ B :=
          (Finset.mem_union.mp y.2).resolve_left hyA
        exact False.elim (hno hxA hyB hxy)
    · by_cases hyA : y.1 ∈ A
      · have hxB : x.1 ∈ B :=
          (Finset.mem_union.mp x.2).resolve_left hxA
        exact False.elim (hno hyA hxB hxy.symm)
      · have hxB : x.1 ∈ B :=
          (Finset.mem_union.mp x.2).resolve_left hxA
        have hyB : y.1 ∈ B :=
          (Finset.mem_union.mp y.2).resolve_left hyA
        have hab : (G.induce (B : Set V)).Adj ⟨x.1,hxB⟩ ⟨y.1,hyB⟩ := hxy
        simpa [hxA,hyA] using (cB.valid hab)

end Inseparability
end HadwigerLean


