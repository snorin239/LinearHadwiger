import HadwigerLean.Woven.HubPathSplice

import HadwigerLean.Graph.RootedCliqueMinor.InducedLinkage

/-!
# Routing mixed-fan arrivals inside an induced linked hub
-/

namespace HadwigerLean
namespace Woven

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
  {G : SimpleGraph V} {m : ℕ}

/-- A linked induced hub routes the arrivals in the ambient graph. The
routes stay inside the hub and avoid all other arrivals internally. -/
theorem exists_induced_hub_arrival_routing
    (G : SimpleGraph V) (H : Finset V)
    (arrival : ι → V) (hinj : Function.Injective arrival)
    (harrival : ∀ i, arrival i ∈ H)
    (slot : Fin m × Fin 2 ≃ ι)
    (hlinked : Linkedness.KLinked (G.induce (H : Set V)) m)
    (horder : 2 * m ≤ Fintype.card (↥(H : Set V))) :
    ∃ J : IndexedLinkage G (hubArrivalPairs arrival slot),
      (∀ k, pathVertexSet (J.path k) ⊆ (H : Set V)) ∧
      Linkedness.InteriorsAvoid J (hubArrivals arrival) := by
  classical
  let arrival' : ι → (H : Set V) := fun i => ⟨arrival i, harrival i⟩
  have hinj' : Function.Injective arrival' := by
    intro i j h
    exact hinj (congrArg Subtype.val h)
  obtain ⟨J',hJ'⟩ := exists_hub_arrival_routing_of_kLinked
    (G.induce (H : Set V)) arrival' hinj' slot hlinked horder
  let J : IndexedLinkage G (hubArrivalPairs arrival slot) :=
    IndexedLinkage.mapInduce J'
  have hsupport (k : Fin m) (v : V) :
      v ∈ pathVertexSet (J.path k) ↔
        ∃ u : (H : Set V),
          u ∈ pathVertexSet (J'.path k) ∧ (u : V) = v := by
    let e : (G.induce (H : Set V)) ↪g G :=
      SimpleGraph.Embedding.induce (H : Set V)
    change v ∈ ((J'.path k :
      (G.induce (H : Set V)).Walk
        ((hubArrivalPairs arrival' slot).start k)
        ((hubArrivalPairs arrival' slot).finish k)).map e.toHom).support ↔ _
    rw [SimpleGraph.Walk.support_map]
    simpa [e, pathVertexSet]
  refine ⟨J,?_,?_⟩
  · intro k v hv
    obtain ⟨u,_,rfl⟩ := (hsupport k v).mp hv
    exact u.property
  · intro k v hv hvX
    obtain ⟨u,hu,huv⟩ := (hsupport k v).mp hv
    have huX : u ∈ hubArrivals arrival' := by
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hvX
      have hui : u = arrival' i := Subtype.ext (huv.trans hi.symm)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hui.symm⟩
    have hterm := hJ' k u hu huX
    rcases hterm with hs | ht
    · exact Or.inl (huv ▸ congrArg Subtype.val hs)
    · exact Or.inr (huv ▸ congrArg Subtype.val ht)


/-- A clean family of incoming paths to a linked induced hub can be
spliced according to any perfect matching of its arrivals. -/
theorem exists_linkage_spliced_through_induced_hub
    (G : SimpleGraph V) (H : Finset V)
    (P : IndexedPairs ι V) (N : IndexedLinkage G P)
    (hfinish : ∀ i, P.finish i ∈ H)
    (hNhub : ∀ i v, v ∈ pathVertexSet (N.path i) →
      v ∈ H → v = P.finish i)
    (slot : Fin m × Fin 2 ≃ ι)
    (hlinked : Linkedness.KLinked (G.induce (H : Set V)) m)
    (horder : 2 * m ≤ Fintype.card (↥(H : Set V))) :
    ∃ (J : IndexedLinkage G (hubArrivalPairs P.finish slot))
      (L : IndexedLinkage G (hubSplicedPairs P slot)),
      Linkedness.InteriorsAvoid J (hubArrivals P.finish) ∧
      (∀ k, pathVertexSet (J.path k) ⊆ (H : Set V)) ∧
      (∀ k, pathVertexSet (L.path k) ⊆
        hubSplicedSupport N slot J k) := by
  obtain ⟨J,hJhub,hJavoid⟩ :=
    exists_induced_hub_arrival_routing G H P.finish
      N.finish_injective hfinish slot hlinked horder
  let L := hubSpliceLinkage N slot J N.finish_injective
    hNhub hJhub hJavoid
  exact ⟨J,L,hJavoid,hJhub,
    fun k => hubSpliceLinkage_support_subset N slot J
      N.finish_injective hNhub hJhub hJavoid k⟩
end Woven
end HadwigerLean
