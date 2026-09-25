import HadwigerLean.Graph.RootedDensity.UniversalIso
import Mathlib.Tactic

/-! Transport of target universality through nested induced subgraphs. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- Universality of a graph induced inside an induced graph transfers to
the corresponding ambient induced graph. -/
theorem Universal.induce_image_of_nested
    {V : Type u} {W : Type v} [Fintype V] [Fintype W] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (R : Set V) (S : Finset R)
    (h : Universal ((G.induce R).induce (S : Set R)) H) :
    Universal (G.induce (S.image Subtype.val : Set V)) H := by
  classical
  let f : ↥(S : Set R) → ↥(S.image Subtype.val : Set V) :=
    fun x => ⟨(x.1.1 : V), Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩
  have hfInj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(S.image Subtype.val : Set V) => (z : V)) hxy
  have hfSurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp y.property
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  let e : (G.induce R).induce (S : Set R) ≃g
      G.induce (S.image Subtype.val : Set V) := {
    toEquiv := Equiv.ofBijective f ⟨hfInj, hfSurj⟩
    map_rel_iff' := by intro a b; rfl
  }
  exact Universal.of_iso e h

/-- Either universality of the whole graph or of one induced subgraph
produces a universal induced subgraph. -/
theorem exists_universal_induced_of_universal_or_induced
    {V : Type u} {W : Type v} [Fintype V] [Fintype W] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (h : Universal G H ∨
      ∃ N : Finset V, Universal (G.induce (N : Set V)) H) :
    ∃ S : Finset V, Universal (G.induce (S : Set V)) H := by
  classical
  rcases h with hwhole | ⟨N, hN⟩
  · refine ⟨Finset.univ, ?_⟩
    let e : G ≃g G.induce ((Finset.univ : Finset V) : Set V) := {
      toEquiv := {
        toFun := fun x => ⟨x, by simp⟩
        invFun := Subtype.val
        left_inv := by intro x; rfl
        right_inv := by intro x; apply Subtype.ext; rfl
      }
      map_rel_iff' := by intro a b; rfl
    }
    exact Universal.of_iso e hwhole
  · exact ⟨N, hN⟩

/-- Flatten a universal induced subgraph of an induced graph into the
ambient vertex set. -/
theorem exists_ambient_universal_induced_of_nested
    {V : Type u} {W : Type v} [Fintype V] [Fintype W] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (R : Set V)
    (h : ∃ N : Finset R,
      Universal ((G.induce R).induce (N : Set R)) H) :
    ∃ S : Finset V, Universal (G.induce (S : Set V)) H := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N.image Subtype.val,
    Universal.induce_image_of_nested G H R N hN⟩

end HadwigerLean.RootedDensity


