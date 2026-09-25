import HadwigerLean.Woven.DoubleFanLift
import Mathlib.Tactic

/-!
# Separators in the double-clone graph
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Lift a target outside the source set to the original side of
the clone graph. -/
def doubleCloneTarget (Z : Finset V) (v : V) (hv : v ∉ Z) :
    DoubleCloneVertex V Z := .inl ⟨v,hv⟩

/-- Exterior original vertices represented in a clone separator. -/
noncomputable def doubleCloneOriginalCut (Z : Finset V)
    (Q : Finset (DoubleCloneVertex V Z)) : Finset V := by
  classical
  exact (Q.image (doubleCloneCollapse Z)) \ Z

theorem doubleCloneOriginalCut_card_le
    (Z : Finset V) (Q : Finset (DoubleCloneVertex V Z)) :
    (doubleCloneOriginalCut Z Q).card ≤ Q.card := by
  classical
  unfold doubleCloneOriginalCut
  exact (Finset.card_le_card Finset.sdiff_subset).trans Finset.card_image_le

theorem doubleCloneTarget_mem_cut_iff
    (Z : Finset V) (Q : Finset (DoubleCloneVertex V Z))
    (v : V) (hv : v ∉ Z) :
    doubleCloneTarget Z v hv ∈ Q ↔
      v ∈ doubleCloneOriginalCut Z Q := by
  classical
  constructor
  · intro h
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_image.mpr
        ⟨doubleCloneTarget Z v hv,h,rfl⟩,hv⟩
  · intro h
    obtain ⟨w,hw,hvw⟩ :=
      Finset.mem_image.mp (Finset.mem_sdiff.mp h).1
    cases w with
    | inl u =>
      have huv : u.1 = v := hvw
      have hu : (Sum.inl u : DoubleCloneVertex V Z) =
          doubleCloneTarget Z v hv := by
        apply congrArg Sum.inl
        exact Subtype.ext huv
      exact hu ▸ hw
    | inr slot =>
      have hslot : slot.1.1 = v := hvw
      exact False.elim (hv (hslot ▸ slot.1.2))

/-- The lifted target set for a set disjoint from the cloned sources. -/
noncomputable def doubleCloneTargets (Z H : Finset V)
    (hdis : Disjoint Z H) :
    Finset (DoubleCloneVertex V Z) := by
  classical
  exact (Finset.univ : Finset H).image (fun v : H =>
    doubleCloneTarget Z v.1
      (fun hv => (Finset.disjoint_left.mp hdis) hv v.2))

theorem doubleCloneTargets_card
    (Z H : Finset V) (hdis : Disjoint Z H) :
    (doubleCloneTargets Z H hdis).card = H.card := by
  classical
  unfold doubleCloneTargets
  rw [Finset.card_image_of_injective]
  · simp
  · intro x y h
    apply Subtype.ext
    have hc := congrArg (doubleCloneCollapse Z) h
    simpa [doubleCloneTarget, doubleCloneCollapse] using hc


@[simp] theorem doubleCloneTarget_mem_targets
    (Z H : Finset V) (hdis : Disjoint Z H)
    (h : H) :
    doubleCloneTarget Z h.1
      (fun hv => (Finset.disjoint_left.mp hdis) hv h.2) ∈
      doubleCloneTargets Z H hdis := by
  classical
  unfold doubleCloneTargets
  exact Finset.mem_image.mpr ⟨h, Finset.mem_univ _, rfl⟩

/-- The lifted copy of the deleted original graph avoids the clone
separator when its chosen source clone survives. -/
theorem doubleCloneLiftVertex_not_mem_cut
    (Z : Finset V) (Q : Finset (DoubleCloneVertex V Z))
    (D : Finset V) (z : Z) (i : Fin 2)
    (hclone : doubleClone Z z i ∉ Q)
    (hZ : Z.erase z.1 ⊆ D)
    (hcut : doubleCloneOriginalCut Z Q ⊆ D)
    (v : {x : V | x ∉ D}) :
    doubleCloneLiftVertex Z D z i hZ v ∉ Q := by
  classical
  by_cases hvz : v.1 = z.1
  · simpa [doubleCloneLiftVertex, hvz] using hclone
  · have hvZ : v.1 ∉ Z := by
      intro hz
      exact v.2 (hZ (Finset.mem_erase.mpr ⟨hvz,hz⟩))
    have hlift : doubleCloneLiftVertex Z D z i hZ v =
        doubleCloneTarget Z v.1 hvZ := by
      simp [doubleCloneLiftVertex, hvz, doubleCloneTarget]
    intro hmem
    have hq : v.1 ∈ doubleCloneOriginalCut Z Q :=
      (doubleCloneTarget_mem_cut_iff Z Q v.1 hvZ).mp
        (hlift ▸ hmem)
    exact v.2 (hcut hq)

/-- Connectedness after deleting the original cut and all other
sources supplies a clone-to-target path avoiding the clone cut. -/
theorem doubleClone_path_avoiding_cut
    (G : SimpleGraph V) (Z : Finset V)
    (Q : Finset (DoubleCloneVertex V Z))
    (D : Finset V) (z : Z) (i : Fin 2)
    (hclone : doubleClone Z z i ∉ Q)
    (hZ : Z.erase z.1 ⊆ D)
    (hcut : doubleCloneOriginalCut Z Q ⊆ D)
    (hzD : z.1 ∉ D)
    (h : V) (hhD : h ∉ D) (hhZ : h ∉ Z)
    (hconn : (G.induce (D : Set V)ᶜ).Connected) :
    ∃ p : (doubleCloneGraph G Z).Path
        (doubleClone Z z i) (doubleCloneTarget Z h hhZ),
      ∀ x ∈ pathVertexSet p, x ∉ Q := by
  classical
  let R : Set V := (D : Set V)ᶜ
  let zz : R := ⟨z.1,hzD⟩
  let hh : R := ⟨h,hhD⟩
  let p : (G.induce (D : Set V)ᶜ).Path zz hh :=
    (hconn.preconnected zz hh).some.toPath
  let f := doubleCloneLiftHom G Z D z i hZ
  let w : (doubleCloneGraph G Z).Walk (f zz) (f hh) :=
    (p : (G.induce (D : Set V)ᶜ).Walk zz hh).map f
  have hstart : f zz = doubleClone Z z i := by
    simp [f, doubleCloneLiftHom, doubleCloneLiftVertex, zz]
  have hne : h ≠ z.1 := by
    intro heq
    exact hhZ (heq ▸ z.2)
  have hend : f hh = doubleCloneTarget Z h hhZ := by
    simp [f, doubleCloneLiftHom, doubleCloneLiftVertex,
      doubleCloneTarget, hh, hne]
  let q : (doubleCloneGraph G Z).Path
      (doubleClone Z z i) (doubleCloneTarget Z h hhZ) :=
    (w.copy hstart hend).toPath
  refine ⟨q, ?_⟩
  intro x hxq
  have hxcopy : x ∈ (w.copy hstart hend).support :=
    (w.copy hstart hend).support_toPath_subset_support hxq
  have hxw : x ∈ w.support := by
    simpa [SimpleGraph.Walk.support_copy] using hxcopy
  change x ∈
    ((p : (G.induce (D : Set V)ᶜ).Walk zz hh).map f).support at hxw
  rw [SimpleGraph.Walk.support_map] at hxw
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hxw
  exact doubleCloneLiftVertex_not_mem_cut Z Q D z i
    hclone hZ hcut v

/-- The connectivity slack rules out every clone-to-hub separator
smaller than the full set of source clones. -/
theorem doubleClone_separator_card_ge
    (G : SimpleGraph V) (Z H : Finset V) (r : ℕ)
    (hconn : VertexConnected G r)
    (hr : 3 * Z.card ≤ r)
    (hH : 2 * Z.card ≤ H.card)
    (hdis : Disjoint Z H)
    (Q : Finset (DoubleCloneVertex V Z))
    (hsep : SetMenger.IsABSeparator (doubleCloneGraph G Z)
      (doubleCloneSources Z) (doubleCloneTargets Z H hdis) Q) :
    2 * Z.card ≤ Q.card := by
  classical
  by_contra hsmall
  have hQsmall : Q.card < 2 * Z.card := by omega
  have hsourceNotSubset : ¬ doubleCloneSources Z ⊆ Q := by
    intro hsub
    have hcard := Finset.card_le_card hsub
    rw [doubleCloneSources_card] at hcard
    omega
  obtain ⟨c,hcA,hcQ⟩ := Finset.not_subset.mp hsourceNotSubset
  unfold doubleCloneSources at hcA
  obtain ⟨slot, -, hslot⟩ := Finset.mem_image.mp hcA
  have hclone0 : doubleClone Z slot.1 slot.2 ∉ Q := by
    simpa [hslot] using hcQ
  let z : Z := slot.1
  let i : Fin 2 := slot.2
  have hclone : doubleClone Z z i ∉ Q := hclone0
  let O : Finset V := doubleCloneOriginalCut Z Q
  let D : Finset V := O ∪ Z.erase z.1
  have hOcard : O.card ≤ Q.card :=
    doubleCloneOriginalCut_card_le Z Q
  have hnotH : ¬ H ⊆ O := by
    intro hsub
    have hc := Finset.card_le_card hsub
    omega
  obtain ⟨h,hhH,hhO⟩ := Finset.not_subset.mp hnotH
  have hhZ : h ∉ Z := by
    intro hz
    exact (Finset.disjoint_left.mp hdis) hz hhH
  have hDcard : D.card < r := by
    have hunion : D.card ≤ O.card + (Z.erase z.1).card := by
      simpa [D] using Finset.card_union_le O (Z.erase z.1)
    have hzerase : (Z.erase z.1).card + 1 = Z.card := by
      simpa using Finset.card_erase_add_one z.2
    omega
  have hZ : Z.erase z.1 ⊆ D := Finset.subset_union_right
  have hcut : O ⊆ D := Finset.subset_union_left
  have hzD : z.1 ∉ D := by
    intro hz
    rcases Finset.mem_union.mp hz with hzO | hze
    · exact (Finset.mem_sdiff.mp hzO).2 z.2
    · exact (Finset.mem_erase.mp hze).1 rfl
  have hhD : h ∉ D := by
    intro hh
    rcases Finset.mem_union.mp hh with hhOmem | hhe
    · exact hhO hhOmem
    · exact hhZ (Finset.mem_of_mem_erase hhe)
  have hconnD := hconn.connected_delete D hDcard
  obtain ⟨p,havoid⟩ :=
    doubleClone_path_avoiding_cut G Z Q D z i hclone
      hZ hcut hzD h hhD hhZ hconnD
  have hsource : doubleClone Z z i ∈ doubleCloneSources Z :=
    doubleClone_mem_sources Z z i
  have htarget : doubleCloneTarget Z h hhZ ∈
      doubleCloneTargets Z H hdis := by
    let hh : H := ⟨h,hhH⟩
    simpa [hh] using doubleCloneTarget_mem_targets Z H hdis hh
  obtain ⟨q,hqQ,hqp⟩ :=
    hsep (doubleClone Z z i) hsource
      (doubleCloneTarget Z h hhZ) htarget p
  exact havoid q hqp hqQ
end Woven
end HadwigerLean
