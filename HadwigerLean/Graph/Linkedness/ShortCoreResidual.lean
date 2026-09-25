import HadwigerLean.Graph.Linkedness.ShortCoreAugment
import HadwigerLean.Graph.Linkedness.DenseDiameter

/-!
# A residual path augments a maximal short partial linkage
-/

namespace HadwigerLean
namespace Linkedness

set_option maxHeartbeats 1000000

namespace ShortPartial

/-- A path of length at most five between exterior neighbors of an
unused terminal pair gives a new path of length at most seven. -/
theorem extend_of_residual_path
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {k : ℕ} {P : IndexedPairs (Fin k) V}
    (C : ShortPartial G P (terminalFinset P))
    (hP : P.DisjointTerminals)
    (i : Fin k) (hi : i ∉ C.used)
    (u v : {x : V | x ∉ C.occupied})
    (hs : G.Adj (P.start i) u.1)
    (ht : G.Adj v.1 (P.finish i))
    (p : (G.induce {x : V | x ∉ C.occupied}).Path u v)
    (hlen : (p : (G.induce {x : V | x ∉ C.occupied}).Walk u v).length ≤ 5) :
    ∃ D : ShortPartial G P (terminalFinset P),
      C.used.card < D.used.card := by
  classical
  let R : Set V := {x | x ∉ C.occupied}
  let q : G.Path (P.start i) (P.finish i) :=
    extendInducedPath R u v p hs ht
  have hqshort :
      (q : G.Walk (P.start i) (P.finish i)).length ≤ 7 := by
    have h := extendInducedPath_length_le R u v p hs ht
    dsimp only [q]
    omega
  have hsubset :
      pathVertexSet q ⊆
        ({P.start i, P.finish i} : Set V) ∪
          (Subtype.val '' pathVertexSet p) :=
    extendInducedPath_vertices_subset R u v p hs ht
  have hqavoid (x : V) (hx : x ∈ pathVertexSet q)
      (hxX : x ∈ terminalFinset P) : x ∈ P.terminals i := by
    rcases hsubset hx with hxend | hxinner
    · simpa [IndexedPairs.terminals] using hxend
    · rcases hxinner with ⟨z, -, rfl⟩
      exact False.elim (z.2 (C.terminal_subset_occupied hxX))
  have hqdis (j : C.used) :
      Disjoint (pathVertexSet q) (pathVertexSet (C.path j)) := by
    apply Set.disjoint_left.mpr
    intro x hxq hxj
    rcases hsubset hxq with hxend | hxinner
    · have hxi : x ∈ P.terminals i := by
        simpa [IndexedPairs.terminals] using hxend
      have hxX : x ∈ terminalFinset P :=
        terminals_subset_terminalFinset P i hxi
      have hxjt : x ∈ P.terminals j.1 :=
        C.avoids j x hxj hxX
      have hij : i ≠ j.1 := by
        intro h
        exact hi (h ▸ j.2)
      exact (Set.disjoint_left.mp (hP hij)) hxi hxjt
    · rcases hxinner with ⟨z, -, rfl⟩
      exact z.2 (C.path_subset_occupied j hxj)
  exact C.extend i hi q hqshort hqavoid hqdis

end ShortPartial
end Linkedness
end HadwigerLean
