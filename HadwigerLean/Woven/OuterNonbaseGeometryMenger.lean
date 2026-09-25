import HadwigerLean.Woven.OuterNonbaseGeometry

/-!
# Geometric normalized nonbase assembly with Menger connectors
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The normalized nonbase geometric assembly, including construction of
the `2a` residual-to-hub connectors by vertex Menger. -/
theorem exists_original_solution_of_normalized_hub_geometry
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
    (hresidual : ∀ (r : Fin a → normalizedSet root P),
      Function.Injective r → (∀ i, r i ∈ U) →
      ∃ M : RootedMinorModel (SimpleGraph.completeGraph (Fin a))
        (G.induce (normalizedSet root P)) r,
        ∀ i, M.branch i ⊆ (U : Set (normalizedSet root P)))
    (hconn : VertexConnected (G.induce (normalizedSet root P)) κ)
    (hκ : (Finset.univ.image (hubRoleFin role)).card + 2 * a ≤ κ)
    (hUcard : 2 * a ≤ U.card)
    (hlinked : Linkedness.KLinked
      ((G.induce (normalizedSet root P)).induce (H : Set _)) (a+j))
    (horder : 2 * (a+j) ≤ H.card) :
    Nonempty (WovenSolution G root P) := by
  classical
  let Z : Finset (normalizedSet root P) :=
    Finset.univ.image (hubRoleFin role)
  have hHcard : 2 * a ≤ H.card := by omega
  obtain ⟨Q,C,hU,hfinish,havoidZ⟩ :=
    exists_paired_connectors_avoiding
      (G.induce (normalizedSet root P)) Z U H a κ
      hconn hκ hZU.symm hZH.symm hUcard hHcard
  exact exists_original_solution_of_normalized_hub_geometry_of_connectors
    G root P hroot hP role hrole hadj U H F Q C
    hU hfinish havoidZ hfanU hZU hHU hZH hresidual
    hlinked horder

end Woven
end HadwigerLean
