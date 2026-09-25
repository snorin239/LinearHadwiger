import HadwigerLean.Graph.TouchingQuotient

/-!
# Rooted branch-set models

A rooted model assigns a prescribed vertex to each branch set.  The
disjointness condition of `MinorModel` then ensures that no branch contains
another prescribed root.  This is the interface used by the rooted clique
minor and woven arguments.
-/

namespace HadwigerLean

universe u v w

/-- A graph-minor model whose branch indexed by `i` contains `root i`. -/
structure RootedMinorModel {W : Type u} {V : Type v}
    (H : SimpleGraph W) (G : SimpleGraph V) (root : W → V)
    extends MinorModel H G where
  root_mem : ∀ i, root i ∈ branch i

namespace RootedMinorModel

variable {W : Type u} {V : Type v} {H : SimpleGraph W}
  {G : SimpleGraph V} {root : W → V}

/-- Prescribed roots of a rooted model are distinct. -/
theorem root_injective (M : RootedMinorModel H G root) :
    Function.Injective root := by
  intro i j hij
  by_contra hne
  exact (Set.disjoint_left.mp (M.disjoint hne)) (M.root_mem i)
    (hij ▸ M.root_mem j)

/-- A branch cannot contain the root of a different branch. -/
theorem other_root_not_mem (M : RootedMinorModel H G root)
    {i j : W} (hij : i ≠ j) : root j ∉ M.branch i := by
  intro hmem
  exact (Set.disjoint_left.mp (M.disjoint hij)) hmem (M.root_mem j)

/-- Adding host edges preserves a rooted model. -/
def mono {G' : SimpleGraph V} (M : RootedMinorModel H G root)
    (h : G ≤ G') : RootedMinorModel H G' root where
  toMinorModel := M.toMinorModel.mono h
  root_mem := M.root_mem

/-- An injective graph homomorphism carries rooted models forward. -/
def map {X : Type w} {J : SimpleGraph X}
    (M : RootedMinorModel H G root) (f : G →g J)
    (hf : Function.Injective f) :
    RootedMinorModel H J (f ∘ root) where
  toMinorModel := M.toMinorModel.map f hf
  root_mem := fun i => ⟨root i, M.root_mem i, rfl⟩

/-- The singleton-branch model of a graph is rooted at the identity map. -/
def refl (G : SimpleGraph V) : RootedMinorModel G G id where
  toMinorModel := MinorModel.refl G
  root_mem := by
    intro i
    change i ∈ ({i} : Set V)
    simp

end RootedMinorModel

/-- A complete graph of order
`, rooted at prescribed vertices, is a minor. -/
def HasRootedCliqueMinor {V : Type v} (G : SimpleGraph V)
    {n : ℕ} (root : Fin n → V) : Prop :=
  Nonempty (RootedMinorModel (SimpleGraph.completeGraph (Fin n)) G root)

/-- Forgetting the roots gives an ordinary clique minor. -/
theorem HasRootedCliqueMinor.toCliqueMinor {V : Type v}
    {G : SimpleGraph V} {n : ℕ} {root : Fin n → V}
    (h : HasRootedCliqueMinor G root) : HasCliqueMinor G n := by
  obtain ⟨M⟩ := h
  exact ⟨M.toMinorModel⟩

end HadwigerLean
namespace HadwigerLean.RootedMinorModel

universe u v w

variable {W : Type u} {V : Type v} {I : Type w}
  {H : SimpleGraph W} {G : SimpleGraph V}
  {r : W → I}

/-- Lift a rooted model in a connected touching quotient to the original
graph, provided each prescribed original root lies in its quotient block. -/
def liftThroughPartition (P : ConnectedPartition G I)
    (M : RootedMinorModel H P.touchingQuotient r)
    (root : W → V) (hroot : ∀ i, root i ∈ P.block (r i)) :
    RootedMinorModel H G root where
  toMinorModel := M.toMinorModel.comp P.toMinorModel
  root_mem := by
    intro i
    change ∃ j ∈ M.branch i, root i ∈ P.block j
    exact ⟨r i, M.root_mem i, hroot i⟩

end HadwigerLean.RootedMinorModel
