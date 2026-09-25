import HadwigerLean.Woven.OuterProxyLift
import HadwigerLean.Woven.OuterConnector

/-!
# Geometric normalized nonbase woven assembly

The normalized graph contains distinct proxy roles. A double fan from
those proxies, a paired residual-to-hub connector linkage, a linked hub,
and rooted models in the residual set assemble into a proxy woven solution.
The normalized solution is then lifted to the original, possibly
coincident, root and terminal roles.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Assemble and lift a normalized nonbase woven solution when the paired
residual-to-hub connectors have already been supplied. -/
theorem exists_original_solution_of_normalized_hub_geometry_of_connectors
    (G : SimpleGraph V) {a j : ℕ}
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
    (Q : IndexedPairs (Fin a × Fin 2) (normalizedSet root P))
    (C : IndexedLinkage (G.induce (normalizedSet root P)) Q)
    (hU : ∀ slot, Q.start slot ∈ U)
    (hfinish : ∀ slot, Q.finish slot ∈ H)
    (havoidZ : ∀ slot v, v ∈ pathVertexSet (C.path slot) →
      v ∉ Finset.univ.image (hubRoleFin role))
    (hfanU : ∀ slot v, v ∈ pathVertexSet (F.path slot) → v ∉ U)
    (hZU : Disjoint (Finset.univ.image (hubRoleFin role)) U)
    (hHU : Disjoint H U)
    (hZH : Disjoint (Finset.univ.image (hubRoleFin role)) H)
    (hresidual : ∀ (r : Fin a → normalizedSet root P),
      Function.Injective r → (∀ i, r i ∈ U) →
      ∃ M : RootedMinorModel (SimpleGraph.completeGraph (Fin a))
        (G.induce (normalizedSet root P)) r,
        ∀ i, M.branch i ⊆ (U : Set (normalizedSet root P)))
    (hlinked : Linkedness.KLinked
      ((G.induce (normalizedSet root P)).induce (H : Set _)) (a+j))
    (horder : 2 * (a+j) ≤ H.card) :
    Nonempty (WovenSolution G root P) := by
  classical
  let Z : Finset (normalizedSet root P) :=
    Finset.univ.image (hubRoleFin role)
  let proxy : HubProxyRole a j ≃ Z := hubProxyEquiv role hrole
  obtain ⟨T⟩ := exists_proxy_woven_of_mixed_fan F C hU hfinish
    havoidZ hfanU hZU hHU hZH proxy hresidual hlinked (by simpa using horder)
  exact exists_original_solution_of_normalized_hub_proxy G root P
    hroot hP role hrole hadj T

end Woven
end HadwigerLean
