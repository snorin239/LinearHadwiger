import HadwigerLean.Graph.SmallConnected.QuotientEndpoint
import HadwigerLean.Graph.SmallConnected.PackedRecover
import Mathlib.Tactic

/-!
# Lifting an uncovered quotient witness to original vertices
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A k-connected graph supported on singleton vertices of a packing
quotient is an induced k-connected subgraph of the original graph, with
the same vertex count. -/
theorem lift_uncovered_vertexConnected_witness
    (G : SimpleGraph V) (F : ConnectedBlockFamily G)
    (W : Type u) [Fintype W] (f : W ↪ F.Vertex)
    (k : ℕ)
    (hf : ∀ w, f w ∉ F.blockVertices)
    (hconn : VertexConnected (F.quotient.comap f) k) :
    ∃ e : W ↪ V, VertexConnected (G.comap e) k := by
  classical
  let U : Finset F.Vertex := F.blockVerticesᶜ
  have hU : Disjoint U F.blockVertices := by
    apply Finset.disjoint_left.mpr
    intro q hq hblock
    exact (Finset.mem_compl.mp hq) hblock
  let H := F.originalOfSingletons U
  have hdisj : Disjoint H F.covered :=
    F.originalOfSingletons_disjoint_covered U
  have hlift : F.singletonLift H = U :=
    F.singletonLift_originalOfSingletons U hU
  have hfU : ∀ w, f w ∈ U := by
    intro w
    exact Finset.mem_compl.mpr (hf w)
  let fU : W ↪ ↥(U : Set F.Vertex) := {
    toFun := fun w => ⟨f w, hfU w⟩
    inj' := by
      intro a b heq
      exact f.injective (congrArg Subtype.val heq)
  }
  let isoU : (G.induce (H : Set V)) ≃g
      (F.quotient.induce (U : Set F.Vertex)) := by
    have iso' := F.singletonLiftIso H hdisj
    rw [hlift] at iso'
    exact iso'
  let eH : W ↪ ↥(H : Set V) :=
    fU.trans isoU.symm.toEquiv.toEmbedding
  let e : W ↪ V :=
    eH.trans (Function.Embedding.subtype (· ∈ (H : Set V)))
  have hgraph : G.comap e = F.quotient.comap f := by
    ext a b
    change G.Adj (e a) (e b) ↔ F.quotient.Adj (f a) (f b)
    change (G.induce (H : Set V)).Adj (eH a) (eH b) ↔
      (F.quotient.induce (U : Set F.Vertex)).Adj (fU a) (fU b)
    exact isoU.symm.map_rel_iff
  exact ⟨e, hgraph ▸ hconn⟩

end HadwigerLean