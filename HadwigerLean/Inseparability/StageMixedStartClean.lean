import HadwigerLean.Inseparability.StageMixedIndexed
import HadwigerLean.Woven.ReroutingPreserveClean

/-!
# Clean H3 starts before and after child rerouting

Each owner has one final path starting at its chosen H3 root. If a path
visits H3 only at its owner's root, linkage disjointness forces that path
to be the owner's final path. The start-only property then survives
rerouting through child pieces disjoint from H3.
-/

namespace HadwigerLean.Inseparability

variable {V : Type*} {G : SimpleGraph V}
  {p x : ℕ} {P : IndexedPairs (CIPathIndex p x) V}

theorem ci_path_H3_only_start
    (L : IndexedLinkage G P)
    (root : CIRawIndex p x → V) (H : Set V)
    (hFinal : ∀ z, root z = P.start (ciFinalIndex p x z))
    (hClean : ∀ k v, v ∈ pathVertexSet (L.path k) →
      v ∈ H → v = root (pathOwner p x k)) :
    ∀ k v, v ∈ pathVertexSet (L.path k) →
      v ∈ H → v = P.start k := by
  intro k v hv hvH
  have hroot := hClean k v hv hvH
  let z := pathOwner p x k
  have hfinalPath : root z ∈ pathVertexSet
      (L.path (ciFinalIndex p x z)) := by
    rw [hFinal]
    exact pathVertexSet.start_mem (L.path (ciFinalIndex p x z))
  have hk : k = ciFinalIndex p x z := by
    by_contra hne
    exact (Set.disjoint_left.mp (L.disjoint hne))
      hv (hroot ▸ hfinalPath)
  rw [hk]
  exact hroot.trans (hFinal z)

theorem ci_path_H3_only_root_after_reroute
    (L₀ L : IndexedLinkage G P)
    (root : CIRawIndex p x → V) (H J : Set V)
    (hFinal : ∀ z, root z = P.start (ciFinalIndex p x z))
    (hClean : ∀ k v, v ∈ pathVertexSet (L₀.path k) →
      v ∈ H → v = root (pathOwner p x k))
    (hSupport : L.vertices ⊆ L₀.vertices ∪ J)
    (hJH : Disjoint J H) :
    ∀ k v, v ∈ pathVertexSet (L.path k) →
      v ∈ H → v = root (pathOwner p x k) := by
  have hStartOld := ci_path_H3_only_start L₀ root H hFinal hClean
  have hStartNew :=
    Woven.IndexedLinkage.clean_start_of_supported_reroute
      L₀ L H J hStartOld hSupport hJH
  intro k v hv hvH
  have hvstart : v = P.start k := hStartNew k v hv hvH
  have hstartH : P.start k ∈ H := hvstart ▸ hvH
  exact hvstart.trans
    (hClean k (P.start k) (pathVertexSet.start_mem (L₀.path k))
      hstartH)

end HadwigerLean.Inseparability

