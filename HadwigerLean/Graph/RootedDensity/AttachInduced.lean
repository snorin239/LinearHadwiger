import HadwigerLean.Graph.RootedDensity.AttachLinkage
import HadwigerLean.Graph.RootedCliqueMinor.InducedLinkage

/-! Attaching a minor inside an induced set through paths in its complement. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- A minor inside `S` and a disjoint linkage in its complement combine to
a rooted minor when each path finish is adjacent to its assigned branch. -/
theorem rootedMinor_of_induced_minor_and_complement_linkage
    {W : Type u} {V : Type v} {H : SimpleGraph W} {G : SimpleGraph V}
    (S : Set V) (M : MinorModel H (G.induce S))
    (P : IndexedPairs W ↥(Sᶜ : Set V))
    (L : IndexedLinkage (G.induce Sᶜ) P)
    (root : W → V) (hstart : ∀ i, (P.start i : V) = root i)
    (hattach : ∀ i, ∃ x ∈ M.branch i,
      G.Adj (x : V) (P.finish i : V)) :
    Nonempty (RootedMinorModel H G root) := by
  let E : (G.induce S) ↪g G := SimpleGraph.Embedding.induce S
  let N : MinorModel H G := M.map E.toHom E.injective
  let L' := L.mapInduce
  have hN (i : W) {x : V} (hx : x ∈ N.branch i) : x ∈ S := by
    rcases hx with ⟨y, _, rfl⟩
    exact y.property
  have hL (j : W) {x : V} (hx : x ∈ pathVertexSet (L'.path j)) : x ∈ Sᶜ := by
    change x ∈ ((L.path j : (G.induce Sᶜ).Walk (P.start j) (P.finish j)).map
      (SimpleGraph.Embedding.induce Sᶜ).toHom).support at hx
    rw [SimpleGraph.Walk.support_map] at hx
    obtain ⟨y, _, hy⟩ := List.mem_map.mp hx
    exact hy ▸ y.property
  have havoid (i j : W) : Disjoint (N.branch i) (pathVertexSet (L'.path j)) := by
    apply Set.disjoint_left.mpr
    intro x hxM hxL
    exact (hL j hxL) (hN i hxM)
  have hattach' (i : W) : ∃ x ∈ N.branch i,
      G.Adj x ((⟨fun i => (P.start i : V), fun i => (P.finish i : V)⟩ :
        IndexedPairs W V).finish i) := by
    obtain ⟨x, hx, hadj⟩ := hattach i
    exact ⟨x, ⟨x, hx, rfl⟩, hadj⟩
  exact rootedMinor_of_minor_and_linkage N
    ⟨fun i => (P.start i : V), fun i => (P.finish i : V)⟩ L'
    hstart havoid hattach'

end HadwigerLean.RootedDensity

