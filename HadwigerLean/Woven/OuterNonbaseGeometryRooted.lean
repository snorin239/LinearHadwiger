import HadwigerLean.Woven.OuterNonbaseGeometryMenger
import HadwigerLean.Woven.ThreeChildResidualTransport

/-!
# Nonbase normalized geometry from residual rooted minors

The three-child argument supplies a rooted clique minor for every distinct
root map in the residual induced graph. This theorem connects that input to
the mixed-fan/hub construction and lifts the proxy solution to the original
roles.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Construct the original woven solution from uniform residual rooted
clique minors and the normalized hub/fan configuration. -/
theorem exists_original_solution_of_normalized_hub_geometry_of_residual_minors
    (G : SimpleGraph V) [DecidableRel G.Adj] {a j κ : ℕ}
    (root : Fin a → V) (P : IndexedPairs (Fin j) V)
    [Fintype (normalizedSet root P)]
    (hroot : Function.Injective root)
    (hP : P.DisjointTerminals)
    (role : Fin (a + 2 * j) → normalizedSet root P)
    (hrole : Function.Injective role)
    (hadj : ∀ i, G.Adj (originalRoleFin root P i) (role i).1)
    (U H : Finset (normalizedSet root P))
    (F : DoubleFan (G.induce (normalizedSet root P))
      (Finset.univ.image (hubRoleFin role)) H)
    (hfanU : ∀ slot v, v ∈ pathVertexSet (F.path slot) → v ∉ U)
    (hZU : Disjoint (Finset.univ.image (hubRoleFin role)) U)
    (hHU : Disjoint H U)
    (hZH : Disjoint (Finset.univ.image (hubRoleFin role)) H)
    (hrooted : ∀ (r : Fin a → (U : Set (normalizedSet root P))),
      Function.Injective r →
      HasRootedCliqueMinor
        ((G.induce (normalizedSet root P)).induce
          (U : Set (normalizedSet root P))) r)
    (hconn : VertexConnected (G.induce (normalizedSet root P)) κ)
    (hκ : (Finset.univ.image (hubRoleFin role)).card + 2 * a ≤ κ)
    (hUcard : 2 * a ≤ U.card)
    (hlinked : Linkedness.KLinked
      ((G.induce (normalizedSet root P)).induce (H : Set _)) (a+j))
    (horder : 2 * (a+j) ≤ H.card) :
    Nonempty (WovenSolution G root P) := by
  classical
  have hresidual (r : Fin a → normalizedSet root P)
      (hr : Function.Injective r) (hrU : ∀ i, r i ∈ U) :
      ∃ M : RootedMinorModel (SimpleGraph.completeGraph (Fin a))
        (G.induce (normalizedSet root P)) r,
        ∀ i, M.branch i ⊆ (U : Set (normalizedSet root P)) :=
    residual_rooted_model_of_induced_minor_for_every_root
      hrooted r hr hrU
  exact exists_original_solution_of_normalized_hub_geometry
    G root P hroot hP role hrole hadj U H F hfanU
    hZU hHU hZH hresidual hconn hκ hUcard hlinked horder

end Woven
end HadwigerLean
