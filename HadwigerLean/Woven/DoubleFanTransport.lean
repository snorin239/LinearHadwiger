import HadwigerLean.Woven.DoubleFan
import HadwigerLean.Woven.ThreeChildGNIso
import Mathlib.Tactic

/-!
# Transport a double fan along a graph embedding

The sequential inseparability induction constructs its double fan inside an
induced chromatic region. This maps all of its paths and source/target sets
into the ambient graph, preserving disjointness outside the source set.
-/

namespace HadwigerLean
namespace Woven

variable {V W : Type*} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]
  {G : SimpleGraph V} {H : SimpleGraph W}

private noncomputable def imageSourceEquiv
    (e : V ↪ W) (Z : Finset V) :
    Z ≃ ↥(Z.image e) := by
  classical
  let f : Z → ↥(Z.image e) := fun z =>
    ⟨e z.1, Finset.mem_image.mpr ⟨z.1,z.2,rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val hab)
  · intro y
    obtain ⟨z,hz,heq⟩ := Finset.mem_image.mp y.property
    refine ⟨⟨z,hz⟩, ?_⟩
    apply Subtype.ext
    exact heq

/-- A graph embedding carries a double fan to its image source and target
sets. -/
noncomputable def DoubleFan.map
    {Z D : Finset V} (F : DoubleFan G Z D)
    (e : G ↪g H) :
    DoubleFan H (Z.image e) (D.image e) := by
  classical
  let eZ := imageSourceEquiv e.toEmbedding Z
  let old : ↥(Z.image e) × Fin 2 → Z × Fin 2 :=
    fun slot => (eZ.symm slot.1,slot.2)
  let finish : ↥(Z.image e) × Fin 2 → W :=
    fun slot => e (F.finish (old slot))
  have hstart (slot : ↥(Z.image e) × Fin 2) :
      e ((old slot).1.1) = slot.1.1 := by
    have h := eZ.apply_symm_apply slot.1
    exact congrArg Subtype.val h
  let p (slot : ↥(Z.image e) × Fin 2) :
      H.Path slot.1.1 (finish slot) := by
    have hp := (F.path (old slot)).map e.toHom e.injective
    exact ⟨(hp : H.Walk
      (e ((old slot).1.1)) (finish slot)).copy (hstart slot) rfl,
      by simpa using hp.property⟩
  have hpverts (slot : ↥(Z.image e) × Fin 2) :
      pathVertexSet (p slot) = e '' pathVertexSet (F.path (old slot)) := by
    ext v
    simp [p, pathVertexSet, SimpleGraph.Walk.support_copy,
      pathVertexSet.map]
  refine {
    finish := finish
    path := p
    finish_mem := ?_
    source_only := ?_
    disjoint_outside := ?_
  }
  · intro slot
    exact Finset.mem_image.mpr
      ⟨F.finish (old slot),F.finish_mem (old slot),rfl⟩
  · intro slot v hv hvZ
    rw [hpverts] at hv
    obtain ⟨u,hu,huv⟩ := hv
    obtain ⟨z,hz,hzv⟩ := Finset.mem_image.mp hvZ
    have huz : u = z := e.injective (huv.trans hzv.symm)
    have huZ : u ∈ Z := huz ▸ hz
    have hueq := F.source_only (old slot) u hu huZ
    calc
      v = e u := huv.symm
      _ = e ((old slot).1.1) := by rw [hueq]
      _ = slot.1.1 := hstart slot
  · intro slot₁ slot₂ hne
    have hold : old slot₁ ≠ old slot₂ := by
      intro heq
      have h₁ : slot₁.1 = slot₂.1 := by
        apply eZ.symm.injective
        exact congrArg Prod.fst heq
      have h₂ : slot₁.2 = slot₂.2 :=
        congrArg (fun a : Z × Fin 2 => a.2) heq
      exact hne (Prod.ext h₁ h₂)
    have hd := F.disjoint_outside hold
    have hZset : (Z.image e : Set W) = e '' (Z : Set V) := by
      ext v
      simp
    rw [hpverts, hpverts, hZset,
      ← Set.image_sdiff e.injective,
      ← Set.image_sdiff e.injective]
    exact Set.disjoint_image_of_injective e.injective hd

/-- Every vertex of a mapped fan path lies in the range of the embedding. -/
theorem DoubleFan.map_path_subset_range
    {Z D : Finset V} (F : DoubleFan G Z D)
    (e : G ↪g H) (slot : (Z.image e) × Fin 2) :
    pathVertexSet ((F.map e).path slot) ⊆ Set.range e := by
  classical
  have hp : pathVertexSet ((F.map e).path slot) =
      e '' pathVertexSet (F.path ((imageSourceEquiv e.toEmbedding Z).symm slot.1,slot.2)) := by
    ext v
    simp [DoubleFan.map, pathVertexSet, SimpleGraph.Walk.support_copy]
  intro v hv
  rw [hp] at hv
  rcases hv with ⟨u, _, rfl⟩
  exact ⟨u, rfl⟩
end Woven
end HadwigerLean





