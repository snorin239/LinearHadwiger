import HadwigerLean.Woven.DoubleFan
import HadwigerLean.ReedSeymour.PathBipartite
import HadwigerLean.Graph.Finite
import Mathlib.Tactic

/-!
# A private two-color palette for every chordless fan path
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {Z H : Finset V}

/-- The union of all vertices used by a double fan. -/
noncomputable def DoubleFan.vertexFinset (F : DoubleFan G Z H) :
    Finset V := by
  classical
  exact (Finset.univ : Finset (Z × Fin 2)).biUnion (fun slot =>
    (F.path slot : G.Walk slot.1.1 (F.finish slot)).support.toFinset)

/-- Each chordless fan path receives its own Boolean palette.
The resulting induced graph uses at most four colors per source. -/
theorem DoubleFan.chromatic_vertexFinset_le_four_mul
    (F : DoubleFan G Z H)
    (hchord : ∀ slot,
      (F.path slot : G.Walk slot.1.1 (F.finish slot)).IsChordless) :
    chromatic (G.induce (F.vertexFinset : Set V)) ≤ 4 * Z.card := by
  classical
  let I := Z × Fin 2
  let S := F.vertexFinset
  have hmember (x : S) :
      ∃ slot : I,
        x.1 ∈ (F.path slot : G.Walk slot.1.1 (F.finish slot)).support := by
    have hxS : x.1 ∈ (Finset.univ : Finset I).biUnion
        (fun slot => (F.path slot :
          G.Walk slot.1.1 (F.finish slot)).support.toFinset) := x.property
    obtain ⟨slot, -, hx⟩ := Finset.mem_biUnion.mp hxS
    exact ⟨slot, List.mem_toFinset.mp hx⟩
  let chosen (x : S) : I := Classical.choose (hmember x)
  have hchosen (x : S) :
      x.1 ∈ (F.path (chosen x) :
        G.Walk (chosen x).1.1 (F.finish (chosen x))).support :=
    Classical.choose_spec (hmember x)
  let C (slot : I) :
      (G.induce {v | v ∈
        (F.path slot : G.Walk slot.1.1 (F.finish slot)).support}).Coloring Bool :=
    ReedSeymour.chordless_path_support_bicoloring (G := G)
      (F.path slot : G.Walk slot.1.1 (F.finish slot))
      (F.path slot).property (hchord slot)
  let color (x : S) : I × Bool :=
    ⟨chosen x, C (chosen x) ⟨x.1,hchosen x⟩⟩
  have color_transport (i j : I) (hij : i = j) (u v : V)
      (hu : u ∈ (F.path i : G.Walk i.1.1 (F.finish i)).support)
      (hv : v ∈ (F.path j : G.Walk j.1.1 (F.finish j)).support)
      (hv' : v ∈ (F.path i : G.Walk i.1.1 (F.finish i)).support)
      (h : C i ⟨u,hu⟩ = C j ⟨v,hv⟩) :
      C i ⟨u,hu⟩ = C i ⟨v,hv'⟩ := by
    subst j
    exact h
  let T : (G.induce (S : Set V)).Coloring (I × Bool) :=
    SimpleGraph.Coloring.mk color (by
      intro x y hxy
      intro heq
      have hs : chosen x = chosen y := congrArg Prod.fst heq
      have hbool : (color x).2 = (color y).2 :=
        congrArg Prod.snd heq
      have hy : y.1 ∈ (F.path (chosen x) :
          G.Walk (chosen x).1.1 (F.finish (chosen x))).support := by
        rw [hs]
        exact hchosen y
      have hxy' : (G.induce {v | v ∈
          (F.path (chosen x) :
            G.Walk (chosen x).1.1 (F.finish (chosen x))).support}).Adj
          ⟨x.1,hchosen x⟩ ⟨y.1,hy⟩ := hxy
      have hbool' : C (chosen x) ⟨x.1,hchosen x⟩ =
          C (chosen x) ⟨y.1,hy⟩ := by
        change C (chosen x) ⟨x.1,hchosen x⟩ =
          C (chosen y) ⟨y.1,hchosen y⟩ at hbool
        exact color_transport (chosen x) (chosen y) hs x.1 y.1
          (hchosen x) (hchosen y) hy hbool
      exact (C (chosen x)).valid hxy' hbool')
  have hcolorable :
      (G.induce (S : Set V)).Colorable (Fintype.card (I × Bool)) :=
    T.colorable
  have hcard : Fintype.card (I × Bool) = 4 * Z.card := by
    simp [I, Fintype.card_prod]
    omega
  rw [← hcard]
  exact (chromatic_le_iff_colorable _ _).mpr hcolorable

end Woven
end HadwigerLean
