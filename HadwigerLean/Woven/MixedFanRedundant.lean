import HadwigerLean.Woven.MixedFanGraph
import HadwigerLean.Woven.DoubleFan
import Mathlib.Tactic

/-!
# The two redundant fans in the paired-source graph
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {Z H : Finset V} {a : ℕ}

/-- The double fan lifted to old vertices of the enlarged graph. -/
noncomputable def DoubleFan.toPairedRedundantFan
    (F : DoubleFan G Z H) (source : Fin a × Fin 2 → V) :
    RedundantFan (pairedFanGraph G source)
      (pairedFanLeftSet (a := a) Z)
      (pairedFanLeftSet (a := a) H)
      (pairedFanRightSet (V := V) (a := a)) := by
  classical
  let dec := pairedFanSlotDecode (a := a) Z
  let finish (slot : pairedFanLeftSet (a := a) Z × Fin 2) :
      PairedFanVertex V a := .inl (F.finish (dec slot))
  let p (slot : pairedFanLeftSet (a := a) Z × Fin 2) :
      (pairedFanGraph G source).Path slot.1.1 (finish slot) :=
    pairedFanLiftPath G source Z slot.1 (F.path (dec slot))
  have hp (slot : pairedFanLeftSet (a := a) Z × Fin 2) :
      pathVertexSet (p slot) =
        Sum.inl '' pathVertexSet (F.path (dec slot)) :=
    pairedFanLiftPath_support G source Z slot.1 (F.path (dec slot))
  exact {
    finish := finish
    path := p
    finish_mem := by
      intro slot
      exact Finset.mem_image.mpr
        ⟨F.finish (dec slot), F.finish_mem (dec slot), rfl⟩
    source_only := by
      intro slot v hv hvZ
      rw [hp] at hv
      obtain ⟨u, hu, huv⟩ := hv
      change v ∈ Z.image Sum.inl at hvZ
      obtain ⟨z, hz, hzv⟩ := Finset.mem_image.mp hvZ
      have huz : u = z := Sum.inl_injective (huv.trans hzv.symm)
      have hsource : u = (dec slot).1.1 :=
        F.source_only (dec slot) u hu (huz ▸ hz)
      calc
        v = Sum.inl u := huv.symm
        _ = Sum.inl (dec slot).1.1 := by rw [hsource]
        _ = slot.1.1 := pairedFanLeftDecode_spec Z slot.1
    avoids_other := by
      intro slot v hv hvR
      rw [hp] at hv
      obtain ⟨u, -, rfl⟩ := hv
      change Sum.inl u ∈ (Finset.univ : Finset (Fin a)).image Sum.inr at hvR
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hvR
      cases hi
    disjoint_outside := by
      intro slot₁ slot₂ hne
      have hdec : dec slot₁ ≠ dec slot₂ := fun h =>
        hne ((pairedFanSlotDecode_injective Z) h)
      have hdis := Set.disjoint_left.mp (F.disjoint_outside hdec)
      apply Set.disjoint_left.mpr
      intro v hv₁ hv₂
      rw [hp] at hv₁ hv₂
      obtain ⟨u₁, hu₁, huv₁⟩ := hv₁.1
      obtain ⟨u₂, hu₂, huv₂⟩ := hv₂.1
      have heq : u₁ = u₂ := Sum.inl_injective (huv₁.trans huv₂.symm)
      subst u₂
      have hnot : u₁ ∉ (Z : Set V) := by
        intro hz
        exact hv₁.2 (huv₁ ▸ ((mem_pairedFanLeftSet Z u₁).2 hz))
      exact hdis ⟨hu₁,hnot⟩ ⟨hu₂,hnot⟩
  }


/-- The two paths from each auxiliary pair source, obtained by attaching
its two spokes to the prescribed disjoint original paths. -/
noncomputable def pairedLinkageToRedundantFan
    (P : IndexedPairs (Fin a × Fin 2) V) (L : IndexedLinkage G P)
    (hfinish : ∀ slot, P.finish slot ∈ H)
    (havoidZ : ∀ slot v, v ∈ pathVertexSet (L.path slot) → v ∉ Z) :
    RedundantFan (pairedFanGraph G P.start)
      (pairedFanRightSet (V := V) (a := a))
      (pairedFanLeftSet (a := a) H)
      (pairedFanLeftSet (a := a) Z) := by
  classical
  let dec := pairedFanRightSlotDecode (V := V) (a := a)
  let finish (slot : pairedFanRightSet (V := V) (a := a) × Fin 2) :
      PairedFanVertex V a := .inl (P.finish (dec slot))
  let p (slot : pairedFanRightSet (V := V) (a := a) × Fin 2) :
      (pairedFanGraph G P.start).Path slot.1.1 (finish slot) :=
    pairedFanRightSpokePath G P.start slot (L.path (dec slot))
  have hp (slot : pairedFanRightSet (V := V) (a := a) × Fin 2) :
      pathVertexSet (p slot) =
        {slot.1.1} ∪ Sum.inl '' pathVertexSet (L.path (dec slot)) :=
    pairedFanRightSpokePath_support G P.start slot (L.path (dec slot))
  exact {
    finish := finish
    path := p
    finish_mem := by
      intro slot
      exact Finset.mem_image.mpr
        ⟨P.finish (dec slot), hfinish (dec slot), rfl⟩
    source_only := by
      intro slot v hv hvR
      rw [hp] at hv
      rcases hv with h | ⟨u, -, hu⟩
      · exact h
      · change v ∈ (Finset.univ : Finset (Fin a)).image Sum.inr at hvR
        obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hvR
        cases hu.trans hi.symm
    avoids_other := by
      intro slot v hv hvZ
      rw [hp] at hv
      rcases hv with h | ⟨u, hu, huv⟩
      · have hmem : slot.1.1 ∈ pairedFanLeftSet (a := a) Z := h ▸ hvZ
        change slot.1.1 ∈ Z.image Sum.inl at hmem
        obtain ⟨z, -, hz⟩ := Finset.mem_image.mp hmem
        have hr := pairedFanRightDecode_spec slot.1
        cases hr.trans hz.symm
      · change v ∈ Z.image Sum.inl at hvZ
        obtain ⟨z, hz, hzv⟩ := Finset.mem_image.mp hvZ
        have huz : u = z := Sum.inl_injective (huv.trans hzv.symm)
        exact havoidZ (dec slot) u hu (huz ▸ hz)
    disjoint_outside := by
      intro slot₁ slot₂ hne
      have hdec : dec slot₁ ≠ dec slot₂ := fun h =>
        hne (pairedFanRightSlotDecode_injective h)
      have hdis := Set.disjoint_left.mp (L.disjoint hdec)
      apply Set.disjoint_left.mpr
      intro v hv₁ hv₂
      rw [hp] at hv₁ hv₂
      have hget (slot : pairedFanRightSet (V := V) (a := a) × Fin 2)
          (hv : v ∈ ({slot.1.1} ∪
            Sum.inl '' pathVertexSet (L.path (dec slot))) \
              (pairedFanRightSet (V := V) (a := a) : Set _)) :
          ∃ u, u ∈ pathVertexSet (L.path (dec slot)) ∧ Sum.inl u = v := by
        rcases hv.1 with h | h
        · exact False.elim (hv.2 (h ▸ slot.1.2))
        · exact h
      obtain ⟨u₁, hu₁, huv₁⟩ := hget slot₁ hv₁
      obtain ⟨u₂, hu₂, huv₂⟩ := hget slot₂ hv₂
      have heq : u₁ = u₂ := Sum.inl_injective (huv₁.trans huv₂.symm)
      subst u₂
      exact hdis hu₁ hu₂
  }

/-- Mixed Menger in the enlarged graph saturates every proxy and every
paired auxiliary source. -/
theorem exists_paired_mixed_linkage
    (F : DoubleFan G Z H)
    (P : IndexedPairs (Fin a × Fin 2) V) (L : IndexedLinkage G P)
    (hfinish : ∀ slot, P.finish slot ∈ H)
    (havoidZ : ∀ slot v, v ∈ pathVertexSet (L.path slot) → v ∉ Z) :
    ∃ (Q : IndexedPairs (Fin ((pairedFanLeftSet (a := a) Z).card +
        (pairedFanRightSet (V := V) (a := a)).card)) (PairedFanVertex V a))
      (M : IndexedLinkage (pairedFanGraph G P.start) Q),
      SetMenger.IsABLinkage M
        (pairedFanLeftSet (a := a) Z ∪
          pairedFanRightSet (V := V) (a := a))
        (pairedFanLeftSet (a := a) H) := by
  classical
  let A₁ := pairedFanLeftSet (a := a) Z
  let A₂ := pairedFanRightSet (V := V) (a := a)
  let B := pairedFanLeftSet (a := a) H
  have hdis : Disjoint A₁ A₂ := pairedFanLeftRight_disjoint Z
  let F₁ : RedundantFan (pairedFanGraph G P.start) A₁ B A₂ :=
    F.toPairedRedundantFan P.start
  let F₂ : RedundantFan (pairedFanGraph G P.start) A₂ B A₁ :=
    pairedLinkageToRedundantFan P L hfinish havoidZ
  obtain ⟨Q,M,hM⟩ :=
    exists_linkage_of_two_redundant_fans
      (pairedFanGraph G P.start) A₁ A₂ B hdis F₁ F₂
  exact ⟨Q,M,hM⟩
end Woven
end HadwigerLean
