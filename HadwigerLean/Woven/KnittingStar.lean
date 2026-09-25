import HadwigerLean.Woven.KnittingPaths

/-!
# Gluing repeated-endpoint paths into knitted parts

Each linkage path joins a specified vertex to its part's representative
through two adjacent proxies. Paths avoid every specified vertex and are
mutually disjoint. Their unions form pairwise disjoint connected parts.
-/

namespace HadwigerLean
namespace Woven

variable {V ι : Type*} {G : SimpleGraph V}
  {q : ℕ} {X : Finset V}

/-- A single original edge together with its proxy path and two attachment
vertices. -/
def knittingEdgePiece {P : IndexedPairs ι V}
    (edgeStart edgeFinish : ι → V)
    (L : IndexedLinkage G P) (i : ι) : Set V :=
  insert (edgeStart i) (insert (edgeFinish i)
    (pathVertexSet (L.path i)))

/-- One connected patch in a knitted part. The `none` patch protects the
representative when its part has no other specified vertices. -/
def knittingStarPatch {P : IndexedPairs ι V}
    (rep : Fin q → V) (edgeStart edgeFinish : ι → V)
    (group : ι → Fin q) (L : IndexedLinkage G P)
    (g : Fin q) (slot : Option {i : ι // group i = g}) : Set V :=
  match slot with
  | none => {rep g}
  | some i => knittingEdgePiece edgeStart edgeFinish L i.1

/-- The resulting vertex set of one knitted part. -/
def knittingStarPiece {P : IndexedPairs ι V}
    (rep : Fin q → V) (edgeStart edgeFinish : ι → V)
    (group : ι → Fin q) (L : IndexedLinkage G P)
    (g : Fin q) : Set V :=
  ⋃₀ Set.range (knittingStarPatch rep edgeStart edgeFinish group L g)

theorem knittingEdgePiece_connected
    {P : IndexedPairs ι V} (L : IndexedLinkage G P)
    (edgeStart edgeFinish : ι → V)
    (hadjStart : ∀ i, G.Adj (edgeStart i) (P.start i))
    (hadjFinish : ∀ i, G.Adj (edgeFinish i) (P.finish i))
    (i : ι) :
    (G.induce (knittingEdgePiece edgeStart edgeFinish L i)).Connected := by
  have hPath : (G.induce (pathVertexSet (L.path i))).Connected :=
    (L.path i : G.Walk (P.start i) (P.finish i)).connected_induce_support
  have h₁ : (G.induce
      (insert (edgeStart i) (pathVertexSet (L.path i)))).Connected := by
    have h := G.connected_induce_union
      (by simp : (G.induce ({edgeStart i} : Set V)).Preconnected)
      hPath.preconnected
      (by simp : edgeStart i ∈ ({edgeStart i} : Set V))
      (pathVertexSet.start_mem (L.path i))
      (hadjStart i)
    simpa only [Set.singleton_union] using h
  have h₂ := G.connected_induce_union h₁.preconnected
    (by simp : (G.induce ({edgeFinish i} : Set V)).Preconnected)
    (Or.inr (pathVertexSet.finish_mem (L.path i)) :
      P.finish i ∈ insert (edgeStart i) (pathVertexSet (L.path i)))
    (by simp : edgeFinish i ∈ ({edgeFinish i} : Set V))
    (hadjFinish i).symm
  have heq : insert (edgeStart i) (pathVertexSet (L.path i)) ∪
      {edgeFinish i} = knittingEdgePiece edgeStart edgeFinish L i := by
    ext x
    simp [knittingEdgePiece, or_assoc, or_left_comm, or_comm]
  rw [heq] at h₂
  exact h₂

end Woven
end HadwigerLean



