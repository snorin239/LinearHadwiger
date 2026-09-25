import HadwigerLean.Woven.MixedFanSaturation
import Mathlib.Tactic

/-!
# Removing a synthetic paired source and projecting the remaining path
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V] {a : ℕ}

/-- A simple path starting at an auxiliary pair vertex and meeting no
other auxiliary vertex projects, after its first spoke, to an old path. -/
theorem exists_pairedFanProjectRightPath
    (G : SimpleGraph V) (source : Fin a × Fin 2 → V)
    (i : Fin a) (t : V)
    (p : (pairedFanGraph G source).Path (.inr i) (.inl t))
    (hright : ∀ j : Fin a,
      (Sum.inr j : PairedFanVertex V a) ∈ pathVertexSet p → j = i) :
    ∃ (b : Fin 2) (u : V) (q : G.Path u t),
      source (i,b) = u ∧
      ∀ v ∈ pathVertexSet q, Sum.inl v ∈ pathVertexSet p := by
  rcases p with ⟨w,hw⟩
  cases w with
  | cons hadj tail =>
      rename_i v
      cases v with
      | inl u =>
          have hb : ∃ b, source (i,b) = u := hadj
          obtain ⟨b,hb⟩ := hb
          have htpath : tail.IsPath ∧
              (Sum.inr i : PairedFanVertex V a) ∉ tail.support :=
            (SimpleGraph.Walk.cons_isPath_iff hadj tail).mp hw
          have hleft : ∀ x ∈ tail.support,
              x ∈ pairedFanOldSet (V := V) (a := a) := by
            intro x hx
            cases x with
            | inl v => exact ⟨v,rfl⟩
            | inr j =>
                have hj : j = i := hright j (by
                  change (Sum.inr j : PairedFanVertex V a) ∈
                    (SimpleGraph.Walk.cons hadj tail).support
                  simp [hx])
                subst j
                exact False.elim (htpath.2 hx)
          let qaux : (pairedFanGraph G source).Path (.inl u) (.inl t) :=
            ⟨tail, htpath.1⟩
          let q := pairedFanProjectOldPath G source qaux hleft
          refine ⟨b,u,q,hb,?_⟩
          intro v hv
          have hv' := pairedFanProjectOldPath_support G source qaux hleft hv
          change Sum.inl v ∈ tail.support at hv'
          change Sum.inl v ∈ (SimpleGraph.Walk.cons hadj tail).support
          simp [hv']
      | inr j => exact False.elim hadj

end Woven
end HadwigerLean
