import HadwigerLean.Graph.RootedDensity.UniversalIso
import Mathlib.Tactic

/-! Universality of an ambient induced core inside a larger induced shore. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- An induced H-universal core remains universal when viewed within any
larger induced region containing all of its vertices. -/
theorem Universal.nested_of_ambient
    {V : Type u} {W : Type v} [Fintype V] [Fintype W] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (R : Set V) (J : Finset V)
    (hJR : ∀ x ∈ J, x ∈ R)
    (h : Universal (G.induce (J : Set V)) H) :
    let T : Finset R := @Finset.subtype V R (Classical.decPred R) J
    Universal ((G.induce R).induce (T : Set R)) H := by
  classical
  intro T
  have hJset : (J : Set V) = Subtype.val '' (T : Set R) := by
    ext x
    constructor
    · intro hx
      refine ⟨⟨x, hJR x hx⟩, ?_, rfl⟩
      exact (Finset.mem_subtype).2 hx
    · rintro ⟨y, hy, rfl⟩
      exact (Finset.mem_subtype).1 hy
  let e : (G.induce R).induce (T : Set R) ≃g G.induce (J : Set V) := {
    toEquiv := (Equiv.Set.image (fun x : R => (x : V)) (T : Set R)
      Subtype.val_injective).trans (Equiv.setCongr hJset.symm)
    map_rel_iff' := by intro x y; rfl
  }
  exact Universal.of_iso e.symm h

end HadwigerLean.RootedDensity
