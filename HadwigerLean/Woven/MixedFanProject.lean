import HadwigerLean.Woven.MixedFanRedundant
import Mathlib.Tactic

/-!
# Projecting the mixed fan from paired-source graph to the original graph
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V] {a : ℕ}

/-- The induced copy of the old vertex set in the paired-source graph. -/
def pairedFanOldSet : Set (PairedFanVertex V a) := Set.range Sum.inl

noncomputable def pairedFanOldValue (x : pairedFanOldSet (V := V) (a := a)) : V :=
  Classical.choose x.2

theorem pairedFanOldValue_spec
    (x : pairedFanOldSet (V := V) (a := a)) :
    Sum.inl (pairedFanOldValue x) = x.1 :=
  Classical.choose_spec x.2

@[simp] theorem pairedFanOldValue_inl (v : V) :
    pairedFanOldValue (⟨Sum.inl v, ⟨v,rfl⟩⟩ :
      pairedFanOldSet (V := V) (a := a)) = v :=
  Sum.inl_injective (pairedFanOldValue_spec _)

/-- Restricting the paired-source graph to old vertices recovers the
original graph. -/
noncomputable def pairedFanOldProjection
    (G : SimpleGraph V) (source : Fin a × Fin 2 → V) :
    (pairedFanGraph G source).induce (pairedFanOldSet (V := V) (a := a)) ↪g G where
  toFun := pairedFanOldValue
  inj' := by
    intro x y h
    apply Subtype.ext
    calc
      x.1 = Sum.inl (pairedFanOldValue x) := (pairedFanOldValue_spec x).symm
      _ = Sum.inl (pairedFanOldValue y) := congrArg Sum.inl h
      _ = y.1 := pairedFanOldValue_spec y
  map_rel_iff' := by
    intro x y
    change G.Adj (pairedFanOldValue x) (pairedFanOldValue y) ↔
      (pairedFanGraph G source).Adj x.1 y.1
    rw [← pairedFanOldValue_spec x, ← pairedFanOldValue_spec y]
    rfl

/-- Every auxiliary path on old vertices projects without introducing
new original vertices. -/
theorem exists_pairedFanProjectOldPath
    (G : SimpleGraph V) (source : Fin a × Fin 2 → V)
    {s t : V} (p : (pairedFanGraph G source).Path (.inl s) (.inl t))
    (hleft : ∀ v ∈ (p : (pairedFanGraph G source).Walk (.inl s) (.inl t)).support,
      v ∈ pairedFanOldSet (V := V) (a := a)) :
    ∃ q : G.Path s t, ∀ v ∈ pathVertexSet q,
      Sum.inl v ∈ pathVertexSet p := by
  let w := (p : (pairedFanGraph G source).Walk (.inl s) (.inl t)).induce
    (pairedFanOldSet (V := V) (a := a)) hleft
  have hw : w.IsPath := by
    have hmap : (w.map (SimpleGraph.Embedding.induce
        (pairedFanOldSet (V := V) (a := a))).toHom).IsPath := by
      rw [show w.map (SimpleGraph.Embedding.induce
          (pairedFanOldSet (V := V) (a := a))).toHom = p.1 by
        simp [w]]
      exact p.property
    exact hmap.of_map
  let pi : ((pairedFanGraph G source).induce
      (pairedFanOldSet (V := V) (a := a))).Path
      ⟨Sum.inl s, hleft _ (pathVertexSet.start_mem p)⟩
      ⟨Sum.inl t, hleft _ (pathVertexSet.finish_mem p)⟩ := ⟨w,hw⟩
  let q : G.Path
      (pairedFanOldValue ⟨Sum.inl s, hleft _ (pathVertexSet.start_mem p)⟩)
      (pairedFanOldValue ⟨Sum.inl t, hleft _ (pathVertexSet.finish_mem p)⟩) :=
    pi.mapEmbedding (pairedFanOldProjection G source)
  have hs : pairedFanOldValue
      (⟨Sum.inl s, hleft _ (pathVertexSet.start_mem p)⟩ :
        pairedFanOldSet (V := V) (a := a)) = s :=
    Sum.inl_injective (pairedFanOldValue_spec _)
  have ht : pairedFanOldValue
      (⟨Sum.inl t, hleft _ (pathVertexSet.finish_mem p)⟩ :
        pairedFanOldSet (V := V) (a := a)) = t :=
    Sum.inl_injective (pairedFanOldValue_spec _)
  let r : G.Path s t := ⟨(q : G.Walk
    (pairedFanOldValue ⟨Sum.inl s, hleft _ (pathVertexSet.start_mem p)⟩)
    (pairedFanOldValue ⟨Sum.inl t, hleft _ (pathVertexSet.finish_mem p)⟩)).copy hs ht,
    by simpa using q.property⟩
  refine ⟨r, ?_⟩
  intro v hv
  have hvq : v ∈ (q : G.Walk
    (pairedFanOldValue ⟨Sum.inl s, hleft _ (pathVertexSet.start_mem p)⟩)
    (pairedFanOldValue ⟨Sum.inl t, hleft _ (pathVertexSet.finish_mem p)⟩)).support := by
    simpa [r, pathVertexSet, SimpleGraph.Walk.support_copy] using hv
  have hvm : v ∈ (w.map (pairedFanOldProjection G source).toHom).support := by
    change v ∈ (w.map (pairedFanOldProjection G source).toHom).support at hvq
    exact hvq
  rw [SimpleGraph.Walk.support_map] at hvm
  obtain ⟨x, hx, hxv⟩ := List.mem_map.mp hvm
  have hxMap : x.1 ∈
      (w.map (SimpleGraph.Embedding.induce
        (pairedFanOldSet (V := V) (a := a))).toHom).support := by
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨x,hx,rfl⟩
  have hxOrig : x.1 ∈ (p : (pairedFanGraph G source).Walk (.inl s) (.inl t)).support := by
    simpa [w] using hxMap
  have hval : Sum.inl v = x.1 := by
    rw [← hxv]
    exact pairedFanOldValue_spec x
  exact hval.symm ▸ hxOrig

/-- A canonical projected path, chosen from the support-preserving result. -/
noncomputable def pairedFanProjectOldPath
    (G : SimpleGraph V) (source : Fin a × Fin 2 → V)
    {s t : V} (p : (pairedFanGraph G source).Path (.inl s) (.inl t))
    (hleft : ∀ v ∈ (p : (pairedFanGraph G source).Walk (.inl s) (.inl t)).support,
      v ∈ pairedFanOldSet (V := V) (a := a)) : G.Path s t :=
  Classical.choose (exists_pairedFanProjectOldPath G source p hleft)

theorem pairedFanProjectOldPath_support
    (G : SimpleGraph V) (source : Fin a × Fin 2 → V)
    {s t : V} (p : (pairedFanGraph G source).Path (.inl s) (.inl t))
    (hleft : ∀ v ∈ (p : (pairedFanGraph G source).Walk (.inl s) (.inl t)).support,
      v ∈ pairedFanOldSet (V := V) (a := a))
    {v : V} (hv : v ∈ pathVertexSet
      (pairedFanProjectOldPath G source p hleft)) :
    Sum.inl v ∈ pathVertexSet p :=
  Classical.choose_spec (exists_pairedFanProjectOldPath G source p hleft) v hv

end Woven
end HadwigerLean