import HadwigerLean.Woven.ThreeChildChromaticBridge
import HadwigerLean.Graph.VertexConnectivityIso

/-!
# Woven solutions and graph isomorphisms

The GN step works on an induced graph of a child. Its selected subgraph is
isomorphic to one induced directly in the ambient graph. These lemmas move
the woven property across that isomorphism.
-/

namespace HadwigerLean

universe u v w

namespace IndexedPairs

/-- Apply a vertex map to both endpoints of every prescribed pair. -/
def map {ι : Type u} {V : Type v} {X : Type w}
    (P : IndexedPairs ι V) (f : V → X) : IndexedPairs ι X :=
  ⟨f ∘ P.start, f ∘ P.finish⟩

@[simp] theorem map_start {ι V X : Type*} (P : IndexedPairs ι V)
    (f : V → X) (i : ι) : (P.map f).start i = f (P.start i) := rfl

@[simp] theorem map_finish {ι V X : Type*} (P : IndexedPairs ι V)
    (f : V → X) (i : ι) : (P.map f).finish i = f (P.finish i) := rfl

theorem terminals_map {ι V X : Type*} (P : IndexedPairs ι V)
    (f : V → X) (i : ι) :
    (P.map f).terminals i = f '' P.terminals i := by
  ext x
  simp [terminals, map, eq_comm]

theorem allTerminals_map {ι V X : Type*} (P : IndexedPairs ι V)
    (f : V → X) :
    (P.map f).allTerminals = f '' P.allTerminals := by
  ext x
  simp [IndexedPairs.allTerminals, terminals_map, Set.image_iUnion]

theorem disjointTerminals_map {ι V X : Type*} (P : IndexedPairs ι V)
    (f : V → X) (hf : Function.Injective f)
    (hP : P.DisjointTerminals) :
    (P.map f).DisjointTerminals := by
  intro i j hij
  rw [terminals_map, terminals_map]
  exact Set.disjoint_image_of_injective hf (hP hij)

end IndexedPairs

namespace pathVertexSet

theorem map {V X : Type*} {G : SimpleGraph V}
    {J : SimpleGraph X} {s t : V}
    (p : G.Path s t) (f : G →g J) (hf : Function.Injective f) :
    pathVertexSet (p.map f hf) = f '' pathVertexSet p := by
  ext x
  change x ∈ ((p : G.Walk s t).map f).support ↔
    ∃ y ∈ (p : G.Walk s t).support, f y = x
  rw [SimpleGraph.Walk.support_map]
  simp only [List.mem_map]

end pathVertexSet

namespace IndexedLinkage

/-- An injective graph homomorphism carries disjoint linkages forward. -/
def map {ι : Type u} {V : Type v} {X : Type w}
    {G : SimpleGraph V} {J : SimpleGraph X}
    {P : IndexedPairs ι V} (L : IndexedLinkage G P)
    (f : G →g J) (hf : Function.Injective f) :
    IndexedLinkage J (P.map f) where
  path := fun i => (L.path i).map f hf
  disjoint := by
    intro i j hij
    change Disjoint (pathVertexSet ((L.path i).map f hf))
      (pathVertexSet ((L.path j).map f hf))
    rw [pathVertexSet.map, pathVertexSet.map]
    exact Set.disjoint_image_of_injective hf (L.disjoint hij)

theorem vertices_map {ι V X : Type*}
    {G : SimpleGraph V} {J : SimpleGraph X}
    {P : IndexedPairs ι V} (L : IndexedLinkage G P)
    (f : G →g J) (hf : Function.Injective f) :
    (L.map f hf).vertices = f '' L.vertices := by
  change (⋃ i, pathVertexSet ((L.path i).map f hf)) =
    f '' (⋃ i, pathVertexSet (L.path i))
  simp only [pathVertexSet.map, Set.image_iUnion]

end IndexedLinkage

namespace WovenSolution

/-- Map a complete woven solution through an injective graph homomorphism. -/
def map {V X : Type*} {G : SimpleGraph V} {J : SimpleGraph X}
    {a j : ℕ} {root : Fin a → V}
    {P : IndexedPairs (Fin j) V}
    (S : WovenSolution G root P)
    (f : G →g J) (hf : Function.Injective f) :
    WovenSolution J (f ∘ root) (P.map f) where
  model := S.model.map f hf
  linkage := S.linkage.map f hf
  exact_intersection := by
    change (S.model.toMinorModel.map f hf).vertices ∩
      (S.linkage.map f hf).vertices =
      Set.range (f ∘ root) ∩ (P.map f).allTerminals
    rw [MinorModel.vertices_map, IndexedLinkage.vertices_map,
      ← Set.image_inter hf, S.exact_intersection,
      Set.image_inter hf, ← Set.range_comp,
      IndexedPairs.allTerminals_map]

end WovenSolution

namespace Woven

/-- Graph isomorphisms preserve wovenness. -/
theorem of_iso {V X : Type*} {G : SimpleGraph V} {J : SimpleGraph X}
    (e : G ≃g J) {a b : ℕ} (hG : Woven G a b) :
    Woven J a b := by
  intro root hroot j hj P hP
  let r : Fin a → V := e.symm ∘ root
  let Q : IndexedPairs (Fin j) V := P.map e.symm
  have hr : Function.Injective r := e.symm.injective.comp hroot
  have hQ : Q.DisjointTerminals :=
    P.disjointTerminals_map e.symm e.symm.injective hP
  obtain ⟨S⟩ := hG r hr j hj Q hQ
  let T := S.map e.toHom e.injective
  have hroot : (e ∘ r) = root := by
    funext i
    simp [r]
  have hpair : Q.map e = P := by
    cases P with
    | mk s t =>
      simp only [Q, IndexedPairs.map]
      congr 1 <;> funext i <;> simp
  exact ⟨hroot ▸ hpair ▸ T⟩

end Woven
end HadwigerLean
