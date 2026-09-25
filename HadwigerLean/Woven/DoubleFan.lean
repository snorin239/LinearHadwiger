import HadwigerLean.Woven.DoubleFanCollapse
import Mathlib.Tactic

/-!
# Two paths per source from a connected graph to a hub
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two source-to-hub paths per source, disjoint outside the
source set and using each source only at its own path start. -/
structure DoubleFan (G : SimpleGraph V) (Z H : Finset V) where
  finish : Z × Fin 2 → V
  path : ∀ slot : Z × Fin 2, G.Path slot.1.1 (finish slot)
  finish_mem : ∀ slot, finish slot ∈ H
  source_only : ∀ slot v, v ∈ pathVertexSet (path slot) →
    v ∈ Z → v = slot.1.1
  disjoint_outside : Pairwise fun slot₁ slot₂ : Z × Fin 2 =>
    Disjoint (pathVertexSet (path slot₁) \ (Z : Set V))
      (pathVertexSet (path slot₂) \ (Z : Set V))

namespace DoubleFan

/-- Once a residual set avoids the chosen fan paths, the double
fan meets the redundant-fan interface used by mixed Menger. -/
def toRedundantFan (F : DoubleFan G Z H) (U : Finset V)
    (hU : ∀ slot v, v ∈ pathVertexSet (F.path slot) → v ∉ U) :
    RedundantFan G Z H U where
  finish := F.finish
  path := F.path
  finish_mem := F.finish_mem
  source_only := F.source_only
  avoids_other := hU
  disjoint_outside := F.disjoint_outside

end DoubleFan

/-- The clone Menger construction gives two paths per source in
the original graph whenever it is 3|Z|-connected and the hub
contains at least 2|Z| vertices. -/
theorem exists_double_fan_of_vertexConnected
    (G : SimpleGraph V) (Z H : Finset V) (r : ℕ)
    (hconn : VertexConnected G r)
    (hr : 3 * Z.card ≤ r)
    (hH : 2 * Z.card ≤ H.card)
    (hdis : Disjoint Z H) :
    Nonempty (DoubleFan G Z H) := by
  classical
  obtain ⟨P,L,hAB⟩ :=
    exists_double_clone_linkage G Z H r hconn hr hH hdis
  obtain ⟨f,hfinj,hf⟩ :=
    doubleClone_slot_index G Z H hdis P L hAB
  let finish (slot : Z × Fin 2) : V :=
    doubleCloneCollapse Z (P.finish (f slot))
  let p (slot : Z × Fin 2) :
      G.Path slot.1.1 (finish slot) := by
    have hp :=
      collapseClonePath G Z H hdis P L hAB (f slot)
    have hstart : doubleCloneCollapse Z (P.start (f slot)) =
        slot.1.1 := by
      rw [hf]
      rfl
    exact ⟨(hp : G.Walk
      (doubleCloneCollapse Z (P.start (f slot)))
      (doubleCloneCollapse Z (P.finish (f slot)))).copy hstart rfl,
      by simpa using hp.property⟩
  have hpverts (slot : Z × Fin 2) :
      pathVertexSet (p slot) =
        pathVertexSet (collapseClonePath G Z H hdis P L hAB (f slot)) := by
    ext v
    simp [p, pathVertexSet, SimpleGraph.Walk.support_copy]
  have hpmem (slot : Z × Fin 2) :
      finish slot ∈ H :=
    doubleClone_finish_mem_hub G Z H hdis P L hAB (f slot)
  have hpsource (slot : Z × Fin 2) (v : V)
      (hv : v ∈ pathVertexSet (p slot)) (hvZ : v ∈ Z) :
      v = slot.1.1 := by
    have hv' : v ∈ pathVertexSet
        (collapseClonePath G Z H hdis P L hAB (f slot)) := by
      rw [← hpverts slot]
      exact hv
    have hsource :=
      collapseClonePath_source_only G Z H hdis P L hAB
        (f slot) v hv' hvZ
    simpa [hf, doubleClone, doubleCloneCollapse] using hsource
  have hpdis : Pairwise fun slot₁ slot₂ : Z × Fin 2 =>
      Disjoint (pathVertexSet (p slot₁) \ (Z : Set V))
        (pathVertexSet (p slot₂) \ (Z : Set V)) := by
    intro slot₁ slot₂ hne
    have hne' : f slot₁ ≠ f slot₂ := fun h => hne (hfinj h)
    rw [hpverts slot₁, hpverts slot₂]
    exact collapseClonePath_disjoint_outside G Z H hdis P L hAB
      (f slot₁) (f slot₂) hne'
  exact ⟨{
    finish := finish
    path := p
    finish_mem := hpmem
    source_only := hpsource
    disjoint_outside := hpdis
  }⟩

end Woven
end HadwigerLean
