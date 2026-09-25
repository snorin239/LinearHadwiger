import HadwigerLean.Woven.HubInducedRouting

import HadwigerLean.Woven.HubResidualControl

import HadwigerLean.Woven.WovenSolutionFromPaths

/-!
# Proxy woven solution from a clean mixed fan and linked hub

The paired incoming paths and hub linkage produce `m` disjoint paths.
Some carry proxy roots into a residual rooted model; the rest realize
terminal pairs while avoiding that model.
-/

namespace HadwigerLean
namespace Woven

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
  {G : SimpleGraph V} {a j m : ℕ}

/-- Abstract final splice for the outer woven induction. A linked hub,
clean incoming linkage, and rooted residual model give a proxy woven
solution with exact intersection. -/
theorem exists_woven_solution_of_hub_splice
    (G : SimpleGraph V) (H U : Finset V)
    (P : IndexedPairs ι V) (N : IndexedLinkage G P)
    (slot : Fin m × Fin 2 ≃ ι)
    (rootSlot : Fin a ↪ Fin m)
    (terminalSlot : Fin j ↪ Fin m)
    (hslots : ∀ i k, rootSlot i ≠ terminalSlot k)
    (M : RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G
      ((hubSplicedPairs P slot).finish ∘ rootSlot))
    (hMsubset : ∀ i, M.branch i ⊆ (U : Set V))
    (hfinishH : ∀ i, P.finish i ∈ H)
    (hNhub : ∀ i v, v ∈ pathVertexSet (N.path i) →
      v ∈ H → v = P.finish i)
    (hNU : ∀ i v, v ∈ pathVertexSet (N.path i) →
      v ∈ U → v = P.start i ∨ v = P.finish i)
    (hfirstOutside : ∀ k, P.start (slot (k,0)) ∉ U)
    (hterminalSecondOutside : ∀ k : Fin j,
      P.start (slot (terminalSlot k,1)) ∉ U)
    (hUH : Disjoint U H)
    (hlinked : Linkedness.KLinked (G.induce (H : Set V)) m)
    (horder : 2 * m ≤ Fintype.card (↥(H : Set V))) :
    Nonempty (WovenSolution G
      ((hubSplicedPairs P slot).start ∘ rootSlot)
      ((hubSplicedPairs P slot).reindex terminalSlot)) := by
  obtain ⟨J,hJhub,hJavoid⟩ :=
    exists_induced_hub_arrival_routing G H P.finish
      N.finish_injective hfinishH slot hlinked horder
  let L : IndexedLinkage G (hubSplicedPairs P slot) :=
    hubSpliceLinkage N slot J N.finish_injective hNhub hJhub hJavoid
  have hrootClean (i : Fin a) (v : V)
      (hv : v ∈ pathVertexSet (L.path (rootSlot i)))
      (hvU : v ∈ U) :
      v = (hubSplicedPairs P slot).finish (rootSlot i) := by
    change v ∈ pathVertexSet (hubSplicePath N slot J (rootSlot i)) at hv
    exact hubSplicePath_residual_only_finish N slot J
      hfinishH hNU hJhub hUH (rootSlot i)
      (hfirstOutside (rootSlot i)) v hv hvU
  have hterminalAvoid (k : Fin j) (v : V)
      (hv : v ∈ pathVertexSet (L.path (terminalSlot k))) :
      v ∉ U := by
    change v ∈ pathVertexSet (hubSplicePath N slot J (terminalSlot k)) at hv
    exact hubSplicePath_avoids_residual N slot J hfinishH hNU
      hJhub hUH (terminalSlot k) (hfirstOutside (terminalSlot k))
      (hterminalSecondOutside k) v hv
  exact exists_woven_solution_of_partitioned_linkage L
    rootSlot terminalSlot hslots (U : Set V) M hMsubset
    hrootClean hterminalAvoid

end Woven
end HadwigerLean
