import HadwigerLean.Graph.MassedPair
import HadwigerLean.Graph.RootedMinor

/-!
# Rooted models of arbitrary finite targets

The target graph is induced on the labels assigned to a chosen root set.
Using a root map from the induced vertex type avoids choosing an inverse to
an arbitrary injection of the roots into the target.
-/

namespace HadwigerLean
namespace RootedDensity

universe u v w

/-- Every injective assignment of distinct labels in `H` to exactly the
vertices of `X` extends to a rooted model of that induced target. -/
def UniversalAt {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (X : Finset V) : Prop :=
  ∀ (Y : Finset W) (root : ↥(Y : Set W) → V),
    Function.Injective root → Set.range root = (X : Set V) →
      Nonempty (RootedMinorModel (H.induce (Y : Set W)) G root)

/-- The graph is universal for the target at every full-size root set. -/
def Universal {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  Fintype.card W ≤ Fintype.card V ∧
    ∀ X : Finset V, X.card = Fintype.card W → UniversalAt G H X

/-- An unrooted density threshold for a fixed finite target graph. -/
def DensityForcesMinor {W : Type v} [Fintype W]
    (H : SimpleGraph W) (c : ℝ) : Prop :=
  ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
    0 < Fintype.card V →
    c * (Fintype.card V : ℝ) ≤ (edgeCount G : ℝ) →
    Nonempty (MinorModel H G)

/-- The rooted-density conclusion of Appendix F, with a real edge budget
written without division by the graph order. -/
def RootedDensityConclusion {W : Type v} [Fintype W]
    (H : SimpleGraph W) (α : ℝ) : Prop :=
  ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (X : Finset V),
    X.card = Fintype.card W →
    VertexConnected G (Fintype.card W) →
    α * (Fintype.card V : ℝ) ≤ (edgeCount G : ℝ) →
    UniversalAt G H X

end RootedDensity
end HadwigerLean

