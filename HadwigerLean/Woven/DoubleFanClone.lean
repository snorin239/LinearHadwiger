import HadwigerLean.Woven.RedundantMenger
import HadwigerLean.Woven.ConnectorMenger
import Mathlib.Tactic

/-!
# Doubling prescribed source vertices

We delete a source set, then introduce two private clones for each source.
Original exterior vertices are shared between the two clone paths.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exterior vertices and two clones per source. -/
abbrev DoubleCloneVertex (V : Type*) (Z : Finset V) :=
  {v : V // v ∉ Z} ⊕ (Z × Fin 2)

/-- Forget a clone's private copy. -/
def doubleCloneCollapse (Z : Finset V) :
    DoubleCloneVertex V Z → V
  | .inl v => v.1
  | .inr slot => slot.1.1

/-- Mark the original exterior vertices. -/
def doubleCloneOriginal (Z : Finset V) :
    DoubleCloneVertex V Z → Prop
  | .inl _ => True
  | .inr _ => False

/-- The graph obtained by replacing each vertex of Z with two
nonadjacent clones. All old edges incident with Z are copied
to both clones; edges within Z are omitted. -/
def doubleCloneGraph (G : SimpleGraph V) (Z : Finset V) :
    SimpleGraph (DoubleCloneVertex V Z) where
  Adj x y :=
    G.Adj (doubleCloneCollapse Z x) (doubleCloneCollapse Z y) ∧
      (doubleCloneOriginal Z x ∨ doubleCloneOriginal Z y)
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    constructor
    intro x h
    exact G.irrefl h.1

/-- Collapsing the private clones preserves every edge. -/
def doubleCloneCollapseHom (G : SimpleGraph V) (Z : Finset V) :
    doubleCloneGraph G Z →g G where
  toFun := doubleCloneCollapse Z
  map_rel' := by
    intro x y h
    exact h.1

/-- The two private copies of a source. -/
def doubleClone (Z : Finset V) (z : Z) (i : Fin 2) :
    DoubleCloneVertex V Z :=
  .inr (z,i)

/-- The full clone source set. -/
noncomputable def doubleCloneSources (Z : Finset V) :
    Finset (DoubleCloneVertex V Z) := by
  classical
  exact Finset.univ.image (fun slot : Z × Fin 2 => doubleClone Z slot.1 slot.2)

theorem doubleCloneSources_card (Z : Finset V) :
    (doubleCloneSources Z).card = 2 * Z.card := by
  classical
  unfold doubleCloneSources
  rw [Finset.card_image_of_injective]
  · simp [Fintype.card_prod]
    omega
  · intro x y h
    exact Sum.inr_injective h

@[simp] theorem doubleClone_mem_sources (Z : Finset V) (z : Z) (i : Fin 2) :
    doubleClone Z z i ∈ doubleCloneSources Z := by
  classical
  unfold doubleCloneSources
  exact Finset.mem_image.mpr ⟨(z,i), Finset.mem_univ _, rfl⟩

end Woven
end HadwigerLean
