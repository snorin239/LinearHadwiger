import HadwigerLean.Woven.NormalizedLinkage

/-!
# Lifting a rooted model through root-proxy edges

An inner rooted model in an induced graph extends to prescribed original
roots outside that graph by adjoining each original root and its proxy edge.
-/

namespace HadwigerLean

universe v

namespace RootedMinorModel

variable {V : Type v} {G : SimpleGraph V} {S : Set V} {a : ℕ}
  {proxy : Fin a → S}

/-- Extend an inner rooted clique model to outside original roots. -/
def extendFromInduced
    (M : RootedMinorModel (SimpleGraph.completeGraph (Fin a))
      (G.induce S) proxy)
    (root : Fin a → V)
    (hroot : Function.Injective root)
    (houtside : ∀ i, root i ∉ S)
    (hadj : ∀ i, G.Adj (root i) (proxy i).1) :
    RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G root := by
  let e : (G.induce S) ↪g G := SimpleGraph.Embedding.induce S
  let N := M.map e.toHom e.injective
  have Nsub (i : Fin a) : N.branch i ⊆ S := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  refine {
    branch := fun i => insert (root i) (N.branch i)
    connected := ?_
    disjoint := ?_
    adjacent := ?_
    root_mem := ?_
  }
  · intro i
    have hs : (G.induce ({root i} : Set V)).Preconnected := by simp
    have ht : (G.induce (N.branch i)).Preconnected := (N.connected i).preconnected
    have hproxy : (proxy i).1 ∈ N.branch i := N.root_mem i
    have hc := G.connected_induce_union hs ht
      (by simp : root i ∈ ({root i} : Set V)) hproxy (hadj i)
    simpa only [Set.singleton_union] using hc
  · intro i k hik
    apply Set.disjoint_left.mpr
    intro x hxi hxk
    rcases Set.mem_insert_iff.mp hxi with hxi | hxi
    · subst x
      rcases Set.mem_insert_iff.mp hxk with hxk | hxk
      · exact hik (hroot hxk)
      · exact (houtside i) (Nsub k hxk)
    · rcases Set.mem_insert_iff.mp hxk with hxk | hxk
      · subst x
        exact (houtside k) (Nsub i hxi)
      · exact (Set.disjoint_left.mp (N.disjoint hik)) hxi hxk
  · intro i k hik
    obtain ⟨x, hx, y, hy, hxy⟩ := N.adjacent hik
    exact ⟨x, Set.mem_insert_iff.mpr (Or.inr hx),
      y, Set.mem_insert_iff.mpr (Or.inr hy), hxy⟩
  · intro i
    exact Set.mem_insert (root i) (N.branch i)

/-- All lifted model vertices are original roots or images of inner branch
vertices. -/
theorem extendFromInduced_vertices_subset
    (M : RootedMinorModel (SimpleGraph.completeGraph (Fin a))
      (G.induce S) proxy)
    (root : Fin a → V)
    (hroot : Function.Injective root)
    (houtside : ∀ i, root i ∉ S)
    (hadj : ∀ i, G.Adj (root i) (proxy i).1) :
    (M.extendFromInduced root hroot houtside hadj).toMinorModel.vertices ⊆
      Set.range root ∪ (Subtype.val '' M.toMinorModel.vertices) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
  let e : (G.induce S) ↪g G := SimpleGraph.Embedding.induce S
  change x ∈ insert (root i) ((M.map e.toHom e.injective).branch i) at hi
  rcases Set.mem_insert_iff.mp hi with hrootx | hinner
  · exact Or.inl ⟨i, hrootx.symm⟩
  · rcases hinner with ⟨z, hz, rfl⟩
    exact Or.inr ⟨z, Set.mem_iUnion.mpr ⟨i, hz⟩, rfl⟩

end RootedMinorModel

end HadwigerLean
