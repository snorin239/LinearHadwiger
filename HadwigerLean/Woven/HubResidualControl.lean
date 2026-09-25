import HadwigerLean.Woven.HubPathSplice

/-!
# Residual-set control for paths spliced through a hub
-/

namespace HadwigerLean
namespace Woven

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
  {G : SimpleGraph V} {P : IndexedPairs ι V}
  {H U : Finset V} {m : ℕ}

/-- If the first incoming path starts outside the residual set, a path
spliced through a disjoint hub can meet the residual set only at its
second incoming start. -/
theorem hubSplicePath_residual_only_finish
    (N : IndexedLinkage G P)
    (slot : Fin m × Fin 2 ≃ ι)
    (J : IndexedLinkage G (hubArrivalPairs P.finish slot))
    (hfinishH : ∀ i, P.finish i ∈ H)
    (hNU : ∀ i v, v ∈ pathVertexSet (N.path i) →
      v ∈ U → v = P.start i ∨ v = P.finish i)
    (hJH : ∀ k, pathVertexSet (J.path k) ⊆ (H : Set V))
    (hUH : Disjoint U H)
    (k : Fin m)
    (hfirst : P.start (slot (k,0)) ∉ U)
    (v : V) (hv : v ∈ pathVertexSet (hubSplicePath N slot J k))
    (hvU : v ∈ U) : v = P.start (slot (k,1)) := by
  have hnotH : v ∉ H := fun hvH =>
    (Finset.disjoint_left.mp hUH) hvU hvH
  have hpiece := hubSplicePath_support_subset N slot J k hv
  rcases hpiece with (hv0 | hvJ) | hv1
  · rcases hNU (slot (k,0)) v hv0 hvU with hs | ht
    · exact False.elim (hfirst (hs ▸ hvU))
    · exact False.elim (hnotH (ht ▸ hfinishH (slot (k,0))))
  · exact False.elim (hnotH (hJH k hvJ))
  · rcases hNU (slot (k,1)) v hv1 hvU with hs | ht
    · exact hs
    · exact False.elim (hnotH (ht ▸ hfinishH (slot (k,1))))

/-- If both incoming starts lie outside the residual set, their spliced
path avoids it entirely. -/
theorem hubSplicePath_avoids_residual
    (N : IndexedLinkage G P)
    (slot : Fin m × Fin 2 ≃ ι)
    (J : IndexedLinkage G (hubArrivalPairs P.finish slot))
    (hfinishH : ∀ i, P.finish i ∈ H)
    (hNU : ∀ i v, v ∈ pathVertexSet (N.path i) →
      v ∈ U → v = P.start i ∨ v = P.finish i)
    (hJH : ∀ k, pathVertexSet (J.path k) ⊆ (H : Set V))
    (hUH : Disjoint U H)
    (k : Fin m)
    (hfirst : P.start (slot (k,0)) ∉ U)
    (hsecond : P.start (slot (k,1)) ∉ U)
    (v : V) (hv : v ∈ pathVertexSet (hubSplicePath N slot J k)) :
    v ∉ U := by
  intro hvU
  exact hsecond (hubSplicePath_residual_only_finish N slot J
    hfinishH hNU hJH hUH k hfirst v hv hvU ▸ hvU)

end Woven
end HadwigerLean
