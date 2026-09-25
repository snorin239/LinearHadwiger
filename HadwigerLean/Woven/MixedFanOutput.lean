import HadwigerLean.Woven.MixedFanTail
import Mathlib.Tactic

/-!
# Reindexing and projecting the mixed Menger linkage
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {Z H : Finset V} {a : ℕ}
  {P : IndexedPairs (Fin a × Fin 2) V}

/-- The canonical auxiliary source represented by a proxy or a pair. -/
def pairedMixedSource : Z ⊕ Fin a → PairedFanVertex V a
  | .inl z => .inl z.1
  | .inr i => .inr i

theorem pairedMixedSource_injective :
    Function.Injective (pairedMixedSource (Z := Z) (a := a)) := by
  intro x y h
  cases x with
  | inl z =>
      cases y with
      | inl w =>
          change Sum.inl z.1 = Sum.inl w.1 at h
          exact congrArg Sum.inl (Subtype.ext (Sum.inl_injective h))
      | inr j => cases h
  | inr i =>
      cases y with
      | inl w => cases h
      | inr j =>
          change Sum.inr i = Sum.inr j at h
          exact congrArg Sum.inr (Sum.inr_injective h)
theorem pairedMixedSource_mem (x : Z ⊕ Fin a) :
    pairedMixedSource x ∈
      pairedFanLeftSet (a := a) Z ∪
        pairedFanRightSet (V := V) (a := a) := by
  cases x with
  | inl z =>
      exact Finset.mem_union_left _ ((mem_pairedFanLeftSet Z z.1).2 z.2)
  | inr i =>
      exact Finset.mem_union_right _ (mem_pairedFanRightSet i)

/-- A full mixed linkage has a distinct path assigned to every proxy and
every auxiliary pair source. -/
theorem pairedMixed_slot_index
    (Q : IndexedPairs (Fin ((pairedFanLeftSet (a := a) Z).card +
        (pairedFanRightSet (V := V) (a := a)).card))
      (PairedFanVertex V a))
    (M : IndexedLinkage (pairedFanGraph G P.start) Q)
    (hAB : SetMenger.IsABLinkage M
      (pairedFanLeftSet (a := a) Z ∪
        pairedFanRightSet (V := V) (a := a))
      (pairedFanLeftSet (a := a) H)) :
    ∃ f : Z ⊕ Fin a → Fin ((pairedFanLeftSet (a := a) Z).card +
        (pairedFanRightSet (V := V) (a := a)).card),
      Function.Injective f ∧
      ∀ x, Q.start (f x) = pairedMixedSource x := by
  classical
  let f (x : Z ⊕ Fin a) := Classical.choose
    (pairedMixed_start_surjective Q M hAB
      (pairedMixedSource x) (pairedMixedSource_mem x))
  have hf (x : Z ⊕ Fin a) :
      Q.start (f x) = pairedMixedSource x :=
    Classical.choose_spec
      (pairedMixed_start_surjective Q M hAB
        (pairedMixedSource x) (pairedMixedSource_mem x))
  refine ⟨f, ?_, hf⟩
  intro x y hxy
  apply pairedMixedSource_injective
  calc
    pairedMixedSource x = Q.start (f x) := (hf x).symm
    _ = Q.start (f y) := by rw [hxy]
    _ = pairedMixedSource y := hf y


/-- Decode the hub endpoint of a saturated auxiliary path. -/
noncomputable def pairedMixedFinish
    {ι : Type*} (Q : IndexedPairs ι (PairedFanVertex V a))
    (hfinish : ∀ j, Q.finish j ∈ pairedFanLeftSet (a := a) H)
    (j : ι) : H :=
  pairedFanLeftDecode H ⟨Q.finish j, hfinish j⟩

/-- Copy an auxiliary path to its canonical proxy or pair source and
its decoded old-vertex hub endpoint. -/
noncomputable def pairedMixedCanonicalPath
    {ι : Type*} (Q : IndexedPairs ι (PairedFanVertex V a))
    (M : IndexedLinkage (pairedFanGraph G P.start) Q)
    (hfinish : ∀ j, Q.finish j ∈ pairedFanLeftSet (a := a) H)
    (j : ι) (x : Z ⊕ Fin a)
    (hstart : Q.start j = pairedMixedSource x) :
    (pairedFanGraph G P.start).Path
      (pairedMixedSource x) (.inl (pairedMixedFinish Q hfinish j).1) := by
  have hend : Q.finish j =
      Sum.inl (pairedMixedFinish Q hfinish j).1 :=
    (pairedFanLeftDecode_spec H ⟨Q.finish j, hfinish j⟩).symm
  exact ⟨((M.path j : (pairedFanGraph G P.start).Walk
      (Q.start j) (Q.finish j)).copy hstart hend),
    by simpa using (M.path j).property⟩

@[simp] theorem pairedMixedCanonicalPath_support
    {ι : Type*} (Q : IndexedPairs ι (PairedFanVertex V a))
    (M : IndexedLinkage (pairedFanGraph G P.start) Q)
    (hfinish : ∀ j, Q.finish j ∈ pairedFanLeftSet (a := a) H)
    (j : ι) (x : Z ⊕ Fin a)
    (hstart : Q.start j = pairedMixedSource x) :
    pathVertexSet (pairedMixedCanonicalPath Q M hfinish j x hstart) =
      pathVertexSet (M.path j) := by
  ext v
  simp [pairedMixedCanonicalPath, pathVertexSet,
    SimpleGraph.Walk.support_copy]

/-- In a saturated mixed linkage, each canonical path meets the
proxy-plus-auxiliary source set only at its own start. -/
theorem pairedMixedCanonicalPath_source_only
    {ι : Type*} [Fintype ι] (Q : IndexedPairs ι (PairedFanVertex V a))
    (M : IndexedLinkage (pairedFanGraph G P.start) Q)
    (hfinish : ∀ j, Q.finish j ∈ pairedFanLeftSet (a := a) H)
    (hsurj : ∀ v ∈ pairedFanLeftSet (a := a) Z ∪
      pairedFanRightSet (V := V) (a := a), ∃ j, Q.start j = v)
    (j : ι) (x : Z ⊕ Fin a)
    (hstart : Q.start j = pairedMixedSource x)
    (v : PairedFanVertex V a)
    (hv : v ∈ pathVertexSet
      (pairedMixedCanonicalPath Q M hfinish j x hstart))
    (hvA : v ∈ pairedFanLeftSet (a := a) Z ∪
      pairedFanRightSet (V := V) (a := a)) :
    v = pairedMixedSource x := by
  have hvM : v ∈ pathVertexSet (M.path j) := by
    rw [pairedMixedCanonicalPath_support] at hv
    exact hv
  have heq := HadwigerLean.Woven.IndexedLinkage.source_only_of_start_surjective
    M _ hsurj j v hvM hvA
  exact heq.trans hstart

/-- A canonical proxy path has no auxiliary vertices and can therefore
be projected in its entirety. -/
theorem pairedMixedCanonicalProxy_old
    {ι : Type*} [Fintype ι] (Q : IndexedPairs ι (PairedFanVertex V a))
    (M : IndexedLinkage (pairedFanGraph G P.start) Q)
    (hfinish : ∀ j, Q.finish j ∈ pairedFanLeftSet (a := a) H)
    (hsurj : ∀ v ∈ pairedFanLeftSet (a := a) Z ∪
      pairedFanRightSet (V := V) (a := a), ∃ j, Q.start j = v)
    (j : ι) (z : Z)
    (hstart : Q.start j = pairedMixedSource (.inl z)) :
    ∀ v ∈ pathVertexSet
      (pairedMixedCanonicalPath Q M hfinish j (.inl z) hstart),
      v ∈ pairedFanOldSet (V := V) (a := a) := by
  intro v hv
  cases v with
  | inl u => exact ⟨u,rfl⟩
  | inr i =>
      have hvA : (Sum.inr i : PairedFanVertex V a) ∈
          pairedFanLeftSet (a := a) Z ∪
            pairedFanRightSet (V := V) (a := a) :=
        Finset.mem_union_right _ (mem_pairedFanRightSet i)
      have heq := pairedMixedCanonicalPath_source_only Q M hfinish hsurj
        j (.inl z) hstart (.inr i) hv hvA
      cases heq

/-- An auxiliary-source path contains no second auxiliary vertex. -/
theorem pairedMixedCanonicalRight_only
    {ι : Type*} [Fintype ι] (Q : IndexedPairs ι (PairedFanVertex V a))
    (M : IndexedLinkage (pairedFanGraph G P.start) Q)
    (hfinish : ∀ j, Q.finish j ∈ pairedFanLeftSet (a := a) H)
    (hsurj : ∀ v ∈ pairedFanLeftSet (a := a) Z ∪
      pairedFanRightSet (V := V) (a := a), ∃ j, Q.start j = v)
    (j : ι) (i k : Fin a)
    (hstart : Q.start j = pairedMixedSource (Z := Z) (.inr i : Z ⊕ Fin a))
    (hv : (Sum.inr k : PairedFanVertex V a) ∈ pathVertexSet
      (pairedMixedCanonicalPath (Z := Z) Q M hfinish j (.inr i : Z ⊕ Fin a) hstart)) :
    k = i := by
  have hvA : (Sum.inr k : PairedFanVertex V a) ∈
      pairedFanLeftSet (a := a) Z ∪
        pairedFanRightSet (V := V) (a := a) :=
    Finset.mem_union_right _ (mem_pairedFanRightSet k)
  exact Sum.inr_injective
    (pairedMixedCanonicalPath_source_only Q M hfinish hsurj
      j (.inr i : Z ⊕ Fin a) hstart (.inr k) hv hvA)
end Woven
end HadwigerLean
