import HadwigerLean.Graph.Linkedness.CoreFanSplice
import HadwigerLean.Graph.RootedCliqueMinor.InducedLinkage
import Mathlib.Tactic

/-!
# Lifting a rooted-linked core through a trimmed fan
-/

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The arrival vertices of a fan, as vertices of its induced core. -/
noncomputable def fanArrivalFinset
    {r : ℕ} (P : IndexedPairs (Fin r) V) (J : Finset V)
    (hfinish : ∀ t, P.finish t ∈ J) : Finset (J : Set V) := by
  classical
  exact Finset.univ.image (fun t : Fin r => ⟨P.finish t, hfinish t⟩)

/-- There are at most as many arrival vertices as fan paths. -/
theorem fanArrivalFinset_card_le
    {r : ℕ} (P : IndexedPairs (Fin r) V) (J : Finset V)
    (hfinish : ∀ t, P.finish t ∈ J) :
    (fanArrivalFinset P J hfinish).card ≤ r := by
  classical
  unfold fanArrivalFinset
  simpa using (Finset.card_image_le
    (s := (Finset.univ : Finset (Fin r)))
    (f := fun t : Fin r => (⟨P.finish t, hfinish t⟩ : (J : Set V))))
/-- Given a chosen injective assignment of the prescribed terminal
occurrences to fan paths, rooted linkedness of the core supplies the inner
linkage and the fan splice supplies the outer rooted linkage. -/
theorem rooted_linkage_of_core_fan_slots
    {G : SimpleGraph V} {r n : ℕ}
    (P : IndexedPairs (Fin r) V) (F : IndexedLinkage G P)
    (J : Finset V)
    (hfinish : ∀ t, P.finish t ∈ J)
    (hfirst : ∀ t x, x ∈ pathVertexSet (F.path t) →
      x ∈ J → x = P.finish t)
    (hcore : RootedLinked (G.induce (J : Set V))
      (fanArrivalFinset P J hfinish))
    (slot : Fin n × Fin 2 → Fin r) (hslot : Function.Injective slot)
    (Q : IndexedPairs (Fin n) V)
    (hQstart : ∀ i, Q.start i = P.start (slot (i,0)))
    (hQfinish : ∀ i, Q.finish i = P.start (slot (i,1))) :
    ∃ L : IndexedLinkage G Q,
      InteriorsAvoid L (Finset.univ.image P.start) := by
  classical
  let Y : Finset V := Finset.univ.image P.finish
  let Ysub : Finset (J : Set V) := fanArrivalFinset P J hfinish
  have hY (t : Fin r) : P.finish t ∈ Y :=
    Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
  have hYsub (u : (J : Set V)) : u ∈ Ysub ↔ (u : V) ∈ Y := by
    simp only [Ysub, fanArrivalFinset, Y, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, congrArg Subtype.val ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, Subtype.ext ht⟩
  let PC : IndexedPairs (Fin n) (J : Set V) := {
    start := fun i => ⟨P.finish (slot (i,0)), hfinish _⟩
    finish := fun i => ⟨P.finish (slot (i,1)), hfinish _⟩
  }
  have hslotne {i j : Fin n} (hij : i ≠ j) (d e : Fin 2) :
      slot (i,d) ≠ slot (j,e) := by
    intro heq
    exact hij (congrArg Prod.fst (hslot heq))
  have hPCdisj : PC.DisjointTerminals := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    rcases hxi with (hi0 | hi1) <;> rcases hxj with (hj0 | hj1)
    · exact hslotne hij 0 0 (F.finish_injective
        (congrArg Subtype.val (hi0.symm.trans hj0)))
    · exact hslotne hij 0 1 (F.finish_injective
        (congrArg Subtype.val (hi0.symm.trans hj1)))
    · exact hslotne hij 1 0 (F.finish_injective
        (congrArg Subtype.val (hi1.symm.trans hj0)))
    · exact hslotne hij 1 1 (F.finish_injective
        (congrArg Subtype.val (hi1.symm.trans hj1)))
  have hPCne : ∀ i, PC.start i ≠ PC.finish i := by
    intro i heq
    have h := F.finish_injective (congrArg Subtype.val heq)
    exact (show (0 : Fin 2) ≠ 1 by decide)
      (congrArg Prod.snd (hslot h))
  have hPCY : ∀ i, PC.terminals i ⊆ (Ysub : Set (J : Set V)) := by
    intro i x hx
    rcases hx with hi | hi
    · rw [hi]
      exact Finset.mem_image.mpr ⟨slot (i,0), Finset.mem_univ _, rfl⟩
    · rw [hi]
      exact Finset.mem_image.mpr ⟨slot (i,1), Finset.mem_univ _, rfl⟩
  obtain ⟨LC, hLCavoid⟩ := hcore n PC hPCdisj hPCne hPCY
  let C : IndexedPairs (Fin n) V :=
    ⟨fun i => P.finish (slot (i,0)), fun i => P.finish (slot (i,1))⟩
  let I : IndexedLinkage G C := LC.mapInduce
  have hsupport (i : Fin n) (v : V) :
      v ∈ pathVertexSet (I.path i) ↔
        ∃ u : (J : Set V), u ∈ pathVertexSet (LC.path i) ∧ (u : V) = v := by
    change v ∈ ((LC.path i : (G.induce (J : Set V)).Walk
      (PC.start i) (PC.finish i)).map
      (SimpleGraph.Embedding.induce (J : Set V)).toHom).support ↔
      ∃ u : (J : Set V), u ∈
        (LC.path i : (G.induce (J : Set V)).Walk (PC.start i) (PC.finish i)).support ∧
        (u : V) = v
    rw [SimpleGraph.Walk.support_map]
    simp only [List.mem_map]
    constructor
    · rintro ⟨u, hu, huv⟩
      exact ⟨u, hu, huv⟩
    · rintro ⟨u, hu, huv⟩
      exact ⟨u, hu, huv⟩
  have hIinside : ∀ i, pathVertexSet (I.path i) ⊆ (J : Set V) := by
    intro i v hv
    obtain ⟨u, _, rfl⟩ := (hsupport i v).mp hv
    exact u.property
  have hIavoid : ∀ i x, x ∈ pathVertexSet (I.path i) →
      x ∈ Y → x ∈ C.terminals i := by
    intro i x hx hxY
    obtain ⟨u, hu, rfl⟩ := (hsupport i x).mp hx
    have huY : u ∈ Ysub := (hYsub u).mpr hxY
    have huTerm := hLCavoid i u hu huY
    rcases huTerm with hu0 | hu1
    · left
      exact congrArg Subtype.val hu0
    · right
      exact congrArg Subtype.val hu1
  obtain ⟨L, hLavoid, _⟩ :=
    exists_spliced_linkage P F J Y hfinish hfirst hY slot hslot Q
      hQstart hQfinish C (fun _ => rfl) (fun _ => rfl) I
      hIinside hIavoid
  exact ⟨L, hLavoid⟩

end Linkedness
end HadwigerLean
