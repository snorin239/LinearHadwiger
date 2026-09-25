import HadwigerLean.Woven.DoubleFanClone

/-!
# Lifting a path after deleting all other sources to one private clone
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Replace a single surviving source vertex by one chosen clone. -/
def doubleCloneLiftVertex (Z D : Finset V) (z : Z) (i : Fin 2)
    (hD : Z.erase z.1 ⊆ D)
    (v : {x : V | x ∉ D}) : DoubleCloneVertex V Z :=
  if hv : v.1 = z.1 then doubleClone Z z i
  else .inl ⟨v.1, by
    intro hz
    exact v.2 (hD (Finset.mem_erase.mpr ⟨hv,hz⟩))⟩

@[simp] theorem doubleCloneCollapse_liftVertex
    (Z D : Finset V) (z : Z) (i : Fin 2)
    (hD : Z.erase z.1 ⊆ D)
    (v : {x : V | x ∉ D}) :
    doubleCloneCollapse Z (doubleCloneLiftVertex Z D z i hD v) = v.1 := by
  classical
  by_cases hv : v.1 = z.1
  · simp [doubleCloneLiftVertex, hv, doubleClone, doubleCloneCollapse]
  · simp [doubleCloneLiftVertex, hv, doubleCloneCollapse]

/-- The chosen clone and all surviving exterior vertices form a
homomorphic copy of the deleted original graph. -/
def doubleCloneLiftHom
    (G : SimpleGraph V) (Z D : Finset V) (z : Z) (i : Fin 2)
    (hD : Z.erase z.1 ⊆ D) :
    G.induce (D : Set V)ᶜ →g doubleCloneGraph G Z where
  toFun := doubleCloneLiftVertex Z D z i hD
  map_rel' := by
    intro x y hxy
    have hxy0 : G.Adj x.1 y.1 := hxy
    have hne : x.1 ≠ z.1 ∨ y.1 ≠ z.1 := by
      by_contra h
      push Not at h
      exact G.irrefl (h.1.symm ▸ h.2.symm ▸ hxy0)
    change G.Adj
        (doubleCloneCollapse Z (doubleCloneLiftVertex Z D z i hD x))
        (doubleCloneCollapse Z (doubleCloneLiftVertex Z D z i hD y)) ∧
      (doubleCloneOriginal Z (doubleCloneLiftVertex Z D z i hD x) ∨
        doubleCloneOriginal Z (doubleCloneLiftVertex Z D z i hD y))
    constructor
    · simpa using hxy0
    · rcases hne with hx | hy
      · left
        simp [doubleCloneLiftVertex, hx, doubleCloneOriginal]
      · right
        simp [doubleCloneLiftVertex, hy, doubleCloneOriginal]

/-- The lift preserves the underlying original vertex of every
vertex in a walk, and therefore is injective. -/
theorem doubleCloneLiftVertex_injective
    (Z D : Finset V) (z : Z) (i : Fin 2)
    (hD : Z.erase z.1 ⊆ D) :
    Function.Injective (doubleCloneLiftVertex Z D z i hD) := by
  intro x y hxy
  apply Subtype.ext
  have h := congrArg (doubleCloneCollapse Z) hxy
  simpa using h

end Woven
end HadwigerLean
