import HadwigerLean.Woven.MixedFanOutput
import Mathlib.Tactic

/-!
# The projected mixed fan: all proxies and one residual start per pair
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V] {a : ℕ}

/-- Data obtained after removing an auxiliary pair vertex from one path. -/
structure RightProjectedPath (G : SimpleGraph V)
    (source : Fin a × Fin 2 → V) (i : Fin a) (t : V)
    (p : (pairedFanGraph G source).Path (.inr i) (.inl t)) where
  bit : Fin 2
  start : V
  path : G.Path start t
  source_eq : source (i,bit) = start
  support_subset : ∀ v ∈ pathVertexSet path,
    Sum.inl v ∈ pathVertexSet p

noncomputable def chooseRightProjectedPath
    (G : SimpleGraph V) (source : Fin a × Fin 2 → V)
    (i : Fin a) (t : V)
    (p : (pairedFanGraph G source).Path (.inr i) (.inl t))
    (hright : ∀ j : Fin a,
      (Sum.inr j : PairedFanVertex V a) ∈ pathVertexSet p → j = i) :
    RightProjectedPath G source i t p := by
  classical
  apply Classical.choice
  obtain ⟨b,u,q,hb,hq⟩ :=
    exists_pairedFanProjectRightPath G source i t p hright
  exact ⟨⟨b,u,q,hb,hq⟩⟩


variable {G : SimpleGraph V} {Z U H : Finset V}
  {P : IndexedPairs (Fin a × Fin 2) V}

/-- A saturated auxiliary mixed linkage projects to one path from every
proxy and one path from a distinct residual start for each pair. -/
theorem project_paired_mixed_linkage
    (Q : IndexedPairs (Fin ((pairedFanLeftSet (a := a) Z).card +
        (pairedFanRightSet (V := V) (a := a)).card))
      (PairedFanVertex V a))
    (M : IndexedLinkage (pairedFanGraph G P.start) Q)
    (hAB : SetMenger.IsABLinkage M
      (pairedFanLeftSet (a := a) Z ∪
        pairedFanRightSet (V := V) (a := a))
      (pairedFanLeftSet (a := a) H))
    (hU : ∀ slot, P.start slot ∈ U) :
    ∃ (R : IndexedPairs (Z ⊕ Fin a) V) (N : IndexedLinkage G R),
      (∀ z : Z, R.start (.inl z) = z.1) ∧
      (∀ i : Fin a, ∃ b : Fin 2, R.start (.inr i) = P.start (i,b)) ∧
      SetMenger.IsABLinkage N (Z ∪ U) H := by
  classical
  obtain ⟨f,hfinj,hf⟩ := pairedMixed_slot_index Q M hAB
  let hs : ∀ v ∈ pairedFanLeftSet (a := a) Z ∪
      pairedFanRightSet (V := V) (a := a), ∃ j, Q.start j = v :=
    pairedMixed_start_surjective Q M hAB
  let endH (x : Z ⊕ Fin a) : H :=
    pairedMixedFinish Q hAB.2 (f x)
  let aux (x : Z ⊕ Fin a) :
      (pairedFanGraph G P.start).Path
        (pairedMixedSource x) (.inl (endH x).1) :=
    pairedMixedCanonicalPath Q M hAB.2 (f x) x (hf x)
  have haux (x : Z ⊕ Fin a) :
      pathVertexSet (aux x) = pathVertexSet (M.path (f x)) := by
    exact pairedMixedCanonicalPath_support Q M hAB.2 (f x) x (hf x)
  let auxz (z : Z) : (pairedFanGraph G P.start).Path
      (.inl z.1) (.inl (endH (.inl z)).1) := by
    change (pairedFanGraph G P.start).Path
      (pairedMixedSource (Z := Z) (.inl z)) (.inl (endH (.inl z)).1)
    exact aux (.inl z)
  have hleft (z : Z) :
      ∀ v ∈ (auxz z : (pairedFanGraph G P.start).Walk
        (.inl z.1) (.inl (endH (.inl z)).1)).support,
        v ∈ pairedFanOldSet (V := V) (a := a) := by
    exact pairedMixedCanonicalProxy_old Q M hAB.2 hs
      (f (.inl z)) z (hf (.inl z))
  let pz (z : Z) : G.Path z.1 (endH (.inl z)).1 :=
    pairedFanProjectOldPath G P.start (auxz z) (hleft z)
  have hright (i j : Fin a) :
      (Sum.inr j : PairedFanVertex V a) ∈ pathVertexSet (aux (.inr i)) →
        j = i := by
    exact pairedMixedCanonicalRight_only Q M hAB.2 hs
      (f (.inr i)) i j (hf (.inr i))
  let rd (i : Fin a) : RightProjectedPath G P.start i
      (endH (.inr i)).1 (aux (.inr i)) :=
    chooseRightProjectedPath G P.start i (endH (.inr i)).1
      (aux (.inr i)) (hright i)
  let start : Z ⊕ Fin a → V
    | .inl z => z.1
    | .inr i => (rd i).start
  let finish (x : Z ⊕ Fin a) : V := (endH x).1
  let R : IndexedPairs (Z ⊕ Fin a) V := ⟨start,finish⟩
  let path (x : Z ⊕ Fin a) : G.Path (R.start x) (R.finish x) := by
    cases x with
    | inl z => exact pz z
    | inr i => exact (rd i).path
  have hlift (x : Z ⊕ Fin a) (v : V)
      (hv : v ∈ pathVertexSet (path x)) :
      Sum.inl v ∈ pathVertexSet (M.path (f x)) := by
    cases x with
    | inl z =>
        have h := pairedFanProjectOldPath_support G P.start
          (auxz z) (hleft z) hv
        rw [← haux]
        exact h
    | inr i =>
        have h := (rd i).support_subset v hv
        rw [← haux]
        exact h
  let N : IndexedLinkage G R := {
    path := path
    disjoint := by
      intro x y hne
      apply Set.disjoint_left.mpr
      intro v hvx hvy
      exact (Set.disjoint_left.mp (M.disjoint (fun h => hne (hfinj h))))
        (hlift x v hvx) (hlift y v hvy)
  }
  refine ⟨R,N,?_,?_,?_⟩
  · intro z
    rfl
  · intro i
    exact ⟨(rd i).bit, (rd i).source_eq.symm⟩
  · constructor
    · intro x
      cases x with
      | inl z => exact Finset.mem_union_left U z.2
      | inr i =>
          have hu : (rd i).start ∈ U := by
            rw [← (rd i).source_eq]
            exact hU (i,(rd i).bit)
          exact Finset.mem_union_right Z hu
    · intro x
      exact (endH x).2
end Woven
end HadwigerLean
