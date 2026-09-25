import HadwigerLean.Woven.PathExtension

/-!
# Lifting a normalized linkage through terminal-proxy edges

The inner linkage lives in the graph induced after the original terminal
vertices are deleted. Each path is extended through its prescribed proxy
edges, then shortened. Distinct original pairs stay disjoint because their
terminal sets are disjoint and the inner paths are disjoint.
-/

namespace HadwigerLean

universe v

namespace IndexedLinkage

variable {V : Type v} {G : SimpleGraph V} {j : ℕ}
  {P : IndexedPairs (Fin j) V} {S : Set V}
  {Q : IndexedPairs (Fin j) S}

/-- Lift a linkage from the normalized graph to original terminal pairs,
using one proxy edge at each end. -/
noncomputable def extendFromInduced
    (L : IndexedLinkage (G.induce S) Q)
    (hP : P.DisjointTerminals)
    (houtside : ∀ i, P.start i ∉ S ∧ P.finish i ∉ S)
    (hstart : ∀ i, G.Adj (P.start i) (Q.start i).1)
    (hfinish : ∀ i, G.Adj (Q.finish i).1 (P.finish i)) :
    IndexedLinkage G P where
  path := fun i => extendInducedPath S (Q.start i) (Q.finish i)
    (L.path i) (hstart i) (hfinish i)
  disjoint := by
    intro i k hik
    apply Set.disjoint_left.mpr
    intro x hxi hxk
    have hxi' := extendInducedPath_vertices_subset S
      (Q.start i) (Q.finish i) (L.path i) (hstart i) (hfinish i) hxi
    have hxk' := extendInducedPath_vertices_subset S
      (Q.start k) (Q.finish k) (L.path k) (hstart k) (hfinish k) hxk
    have hinner (z : V) (hz : z ∈ Subtype.val '' pathVertexSet (L.path i)) : z ∈ S := by
      rcases hz with ⟨w, _, rfl⟩
      exact w.property
    have hinner' (z : V) (hz : z ∈ Subtype.val '' pathVertexSet (L.path k)) : z ∈ S := by
      rcases hz with ⟨w, _, rfl⟩
      exact w.property
    have hterm_not (l : Fin j) (z : V) (hz : z ∈ P.terminals l) : z ∉ S := by
      rcases hz with rfl | rfl
      · exact (houtside l).1
      · exact (houtside l).2
    rcases hxi' with htermI | hinnerI
    · rcases hxk' with htermK | hinnerK
      · exact (Set.disjoint_left.mp (hP hik)) htermI htermK
      · exact hterm_not i x htermI (hinner' x hinnerK)
    · rcases hxk' with htermK | hinnerK
      · exact hterm_not k x htermK (hinner x hinnerI)
      · rcases hinnerI with ⟨u, hu, rfl⟩
        rcases hinnerK with ⟨v, hv, hval⟩
        have huv : u = v := Subtype.ext hval.symm
        subst v
        exact (Set.disjoint_left.mp (L.disjoint hik)) hu hv

/-- The lifted path vertices remain inside original terminals together
with the image of the normalized linkage vertices. -/
theorem extendFromInduced_vertices_subset
    (L : IndexedLinkage (G.induce S) Q)
    (hP : P.DisjointTerminals)
    (houtside : ∀ i, P.start i ∉ S ∧ P.finish i ∉ S)
    (hstart : ∀ i, G.Adj (P.start i) (Q.start i).1)
    (hfinish : ∀ i, G.Adj (Q.finish i).1 (P.finish i)) :
    (L.extendFromInduced hP houtside hstart hfinish).vertices ⊆
      P.allTerminals ∪ (Subtype.val '' L.vertices) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  have hsub := extendInducedPath_vertices_subset S
    (Q.start i) (Q.finish i) (L.path i) (hstart i) (hfinish i) hxi
  rcases hsub with hterm | hinner
  · exact Or.inl (Set.mem_iUnion.mpr ⟨i, hterm⟩)
  · rcases hinner with ⟨z, hz, rfl⟩
    exact Or.inr ⟨z, L.path_subset_vertices i hz, rfl⟩

end IndexedLinkage

end HadwigerLean
