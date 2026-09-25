import HadwigerLean.Woven.DoubleFan
import HadwigerLean.ReedSeymour.ConnectorLift
import HadwigerLean.ReedSeymour.Parity
import Mathlib.Tactic

/-!
# Shortening each double-fan path inside its own support
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {Z H : Finset V}

/-- A fan path can be shortened inside its old support to a chordless path
with the same endpoints. -/
theorem DoubleFan.exists_chordless_subpath
    (F : DoubleFan G Z H) (slot : Z × Fin 2) :
    ∃ q : G.Path slot.1.1 (F.finish slot),
      (q : G.Walk slot.1.1 (F.finish slot)).IsChordless ∧
      pathVertexSet q ⊆ pathVertexSet (F.path slot) := by
  classical
  let U : Set V := pathVertexSet (F.path slot)
  let a : U := ⟨slot.1.1, (F.path slot : G.Walk slot.1.1 (F.finish slot)).start_mem_support⟩
  let b : U := ⟨F.finish slot, (F.path slot : G.Walk slot.1.1 (F.finish slot)).end_mem_support⟩
  have hconn : (G.induce U).Connected := by
    simpa [U, pathVertexSet] using
      (F.path slot : G.Walk slot.1.1 (F.finish slot)).connected_induce_support
  obtain ⟨p, hp⟩ := (hconn.preconnected a b).exists_walk_length_eq_dist
  have hpath : p.IsPath := p.isPath_of_length_eq_dist hp
  have hchord : p.IsChordless :=
    ReedSeymour.shortest_walk_isChordless p hp
  let q0 : G.Path a.1 b.1 :=
    SimpleGraph.Path.mapEmbedding (SimpleGraph.Embedding.induce U)
      (⟨p, hpath⟩ : (G.induce U).Path a b)
  let q : G.Path slot.1.1 (F.finish slot) :=
    ⟨(q0 : G.Walk a.1 b.1).copy rfl rfl, by
      simpa using q0.property⟩
  refine ⟨q, ?_, ?_⟩
  · simpa [q, q0, ReedSeymour.CentralSplit.liftInducedWalk, SimpleGraph.Walk.IsChordless, SimpleGraph.Walk.IsChord] using
      ReedSeymour.CentralSplit.liftInducedWalk_isChordless hchord
  · intro v hv
    have hv' : v ∈ (ReedSeymour.CentralSplit.liftInducedWalk p).support := by
      simpa [q, q0, ReedSeymour.CentralSplit.liftInducedWalk, pathVertexSet] using hv
    exact ReedSeymour.liftInducedWalk_support_subset p v hv'

/-- Shorten every path independently. Its support can only shrink, so all
source and disjointness guarantees remain valid. -/
theorem DoubleFan.exists_chordless_subfan
    (F : DoubleFan G Z H) :
    ∃ F' : DoubleFan G Z H,
      (∀ slot, (F'.path slot : G.Walk slot.1.1 (F'.finish slot)).IsChordless) ∧
      (∀ slot, pathVertexSet (F'.path slot) ⊆ pathVertexSet (F.path slot)) := by
  classical
  let q (slot : Z × Fin 2) := Classical.choose (F.exists_chordless_subpath slot)
  have hq (slot : Z × Fin 2) :
      (q slot : G.Walk slot.1.1 (F.finish slot)).IsChordless ∧
      pathVertexSet (q slot) ⊆ pathVertexSet (F.path slot) :=
    Classical.choose_spec (F.exists_chordless_subpath slot)
  let F' : DoubleFan G Z H := {
    finish := F.finish
    path := q
    finish_mem := F.finish_mem
    source_only := by
      intro slot v hv hvZ
      exact F.source_only slot v ((hq slot).2 hv) hvZ
    disjoint_outside := by
      intro slot₁ slot₂ hne
      apply Set.disjoint_left.mpr
      intro v hv₁ hv₂
      exact (Set.disjoint_left.mp (F.disjoint_outside hne))
        ⟨(hq slot₁).2 hv₁.1, hv₁.2⟩
        ⟨(hq slot₂).2 hv₂.1, hv₂.2⟩
  }
  exact ⟨F', (fun slot => (hq slot).1), (fun slot => (hq slot).2)⟩

end Woven
end HadwigerLean
