import HadwigerLean.Graph.RootedDensity.Definitions
import HadwigerLean.Graph.Linkedness.RegionLinkage

/-! Extend an arbitrary rooted target model along a clean disjoint fan. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- The finishes of vertex-disjoint paths are distinct. -/
theorem IndexedLinkage.finish_injective
    {ι V : Type*} {G : SimpleGraph V} {P : IndexedPairs ι V}
    (L : IndexedLinkage G P) : Function.Injective P.finish := by
  intro i j heq
  by_contra hij
  have hdis := L.disjoint hij
  exact (Set.disjoint_left.mp hdis)
    (pathVertexSet.finish_mem (L.path i))
    (heq.symm ▸ pathVertexSet.finish_mem (L.path j))
/-- A rooted model in a region can move its roots along disjoint paths
which meet the region only at their finishes. -/
def rootedMinor_extendAlongCleanLinkage
    {W : Type u} {V : Type v} {H : SimpleGraph W} {G : SimpleGraph V}
    {P : IndexedPairs W V}
    (M : RootedMinorModel H G P.finish)
    (L : IndexedLinkage G P) (J : Set V)
    (hMsubset : ∀ i, M.branch i ⊆ J)
    (hLclean : ∀ i x, x ∈ pathVertexSet (L.path i) →
      x ∈ J → x = P.finish i) :
    RootedMinorModel H G P.start where
  branch := fun i => M.branch i ∪ pathVertexSet (L.path i)
  connected := by
    intro i
    have hB : (G.induce (M.branch i)).Connected := M.connected i
    have hP : (G.induce (pathVertexSet (L.path i))).Connected :=
      (L.path i : G.Walk (P.start i) (P.finish i)).connected_induce_support
    exact Linkedness.connected_induce_union_of_common hB hP
      (M.root_mem i) (pathVertexSet.finish_mem (L.path i))
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    rcases hxi with hxiM | hxiL <;> rcases hxj with hxjM | hxjL
    · exact (Set.disjoint_left.mp (M.disjoint hij)) hxiM hxjM
    · have hxJ : x ∈ J := hMsubset i hxiM
      have hlast : x = P.finish j := hLclean j x hxjL hxJ
      have hxjM : x ∈ M.branch j := by
        simpa [hlast] using M.root_mem j
      exact (Set.disjoint_left.mp (M.disjoint hij)) hxiM hxjM
    · have hxJ : x ∈ J := hMsubset j hxjM
      have hlast : x = P.finish i := hLclean i x hxiL hxJ
      have hxiM : x ∈ M.branch i := by
        simpa [hlast] using M.root_mem i
      exact (Set.disjoint_left.mp (M.disjoint hij)) hxiM hxjM
    · exact (Set.disjoint_left.mp (L.disjoint hij)) hxiL hxjL
  adjacent := by
    intro i j hij
    obtain ⟨x,hxi,y,hyj,hxy⟩ := M.adjacent hij
    exact ⟨x, Or.inl hxi, y, Or.inl hyj, hxy⟩
  root_mem := by
    intro i
    exact Or.inr (pathVertexSet.start_mem (L.path i))

/-- The same fan extension when the initial rooted model lives in an
induced subgraph. -/
theorem rootedMinor_of_induced_rootedMinor_and_clean_fan
    {W : Type u} {V : Type v} {H : SimpleGraph W} {G : SimpleGraph V}
    {P : IndexedPairs W V} (L : IndexedLinkage G P)
    (J : Set V) (hfinish : ∀ i, P.finish i ∈ J)
    (hfirst : ∀ i x, x ∈ pathVertexSet (L.path i) →
      x ∈ J → x = P.finish i)
    (hM : Nonempty (RootedMinorModel H (G.induce J)
      (fun i => (⟨P.finish i, hfinish i⟩ : J)))) :
    Nonempty (RootedMinorModel H G P.start) := by
  obtain ⟨M⟩ := hM
  let E : (G.induce J) ↪g G := SimpleGraph.Embedding.induce J
  let N : RootedMinorModel H G P.finish := M.map E.toHom E.injective
  have hN (i : W) : N.branch i ⊆ J := by
    intro x hx
    rcases hx with ⟨y, _, rfl⟩
    exact y.property
  exact ⟨rootedMinor_extendAlongCleanLinkage N L J hN hfirst⟩

end HadwigerLean.RootedDensity


