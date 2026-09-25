import HadwigerLean.Woven.ConnectorMenger
import HadwigerLean.Graph.RootedCliqueMinor.InducedLinkage
import HadwigerLean.Graph.ConnectivityMenger
import Mathlib.Tactic

/-!
# Connectors from a residual set to a hub avoiding proxy vertices
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

private def complementEmbedding (Z A : Finset V)
    (hAZ : Disjoint A Z) : A ↪ ↥((Z : Set V)ᶜ) where
  toFun := fun x => ⟨x.1,
    fun hxZ => (Finset.disjoint_left.mp hAZ) x.2 hxZ⟩
  inj' := by
    intro x y h
    have hv : (x : V) = (y : V) := congrArg (fun z : ↥((Z : Set V)ᶜ) => (z : V)) h
    exact Subtype.ext hv

/-- Regard a finite set disjoint from Z as a finite set of vertices of
the graph induced outside Z. -/
noncomputable def finsetIntoComplement (Z A : Finset V)
    (hAZ : Disjoint A Z) : Finset ↥((Z : Set V)ᶜ) := by
  classical
  exact A.attach.image (complementEmbedding Z A hAZ)

@[simp] theorem finsetIntoComplement_card (Z A : Finset V)
    (hAZ : Disjoint A Z) :
    (finsetIntoComplement Z A hAZ).card = A.card := by
  classical
  unfold finsetIntoComplement
  rw [Finset.card_image_of_injective _ (complementEmbedding Z A hAZ).injective]
  simp

theorem finsetIntoComplement_mem (Z A : Finset V)
    (hAZ : Disjoint A Z)
    {x : ↥((Z : Set V)ᶜ)}
    (hx : x ∈ finsetIntoComplement Z A hAZ) :
    (x : V) ∈ A := by
  classical
  obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hx
  have hval := congrArg Subtype.val hy
  exact hval ▸ y.property


/-- A sufficiently connected graph has 2a disjoint residual-to-hub
connectors that avoid all proxy vertices. -/
theorem exists_paired_connectors_avoiding
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z U H : Finset V) (a κ : ℕ)
    (hconn : VertexConnected G κ)
    (hκ : Z.card + 2 * a ≤ κ)
    (hUZ : Disjoint U Z) (hHZ : Disjoint H Z)
    (hUcard : 2 * a ≤ U.card)
    (hHcard : 2 * a ≤ H.card) :
    ∃ (P : IndexedPairs (Fin a × Fin 2) V)
      (L : IndexedLinkage G P),
      (∀ slot, P.start slot ∈ U) ∧
      (∀ slot, P.finish slot ∈ H) ∧
      (∀ slot v, v ∈ pathVertexSet (L.path slot) → v ∉ Z) := by
  classical
  let D : Set V := (Z : Set V)ᶜ
  let U' : Finset D := finsetIntoComplement Z U hUZ
  let H' : Finset D := finsetIntoComplement Z H hHZ
  have hU' : 2 * a ≤ U'.card := by
    change 2 * a ≤ (finsetIntoComplement Z U hUZ).card
    rw [finsetIntoComplement_card]
    exact hUcard
  have hH' : 2 * a ≤ H'.card := by
    change 2 * a ≤ (finsetIntoComplement Z H hHZ).card
    rw [finsetIntoComplement_card]
    exact hHcard
  have hconnD : VertexConnected (G.induce D) (2 * a) := by
    exact hconn.induce_compl Z (2 * a) hκ
  obtain ⟨P₀,L₀,hAB⟩ :=
    hconnD.exists_AB_linkage U' H' hU' hH'
  let e : Fin a × Fin 2 ≃ Fin (2 * a) :=
    finProdFinEquiv.trans (finCongr (by omega : a * 2 = 2 * a))
  let P : IndexedPairs (Fin a × Fin 2) V :=
    ⟨fun slot => (P₀.start (e slot) : V),
      fun slot => (P₀.finish (e slot) : V)⟩
  let L₁ : IndexedLinkage (G.induce D) (P₀.reindex e.toEmbedding) :=
    L₀.reindex e.toEmbedding
  let L : IndexedLinkage G P := L₁.mapInduce
  refine ⟨P,L,?_,?_,?_⟩
  · intro slot
    exact finsetIntoComplement_mem Z U hUZ (hAB.1 (e slot))
  · intro slot
    exact finsetIntoComplement_mem Z H hHZ (hAB.2 (e slot))
  · intro slot v hv hvZ
    let E : (G.induce D) ↪g G := SimpleGraph.Embedding.induce D
    have hv' : v ∈ ((L₁.path slot : (G.induce D).Walk
        ((P₀.reindex e.toEmbedding).start slot)
        ((P₀.reindex e.toEmbedding).finish slot)).map E.toHom).support := by
      change v ∈ ((L₁.path slot : (G.induce D).Walk
        ((P₀.reindex e.toEmbedding).start slot)
        ((P₀.reindex e.toEmbedding).finish slot)).map E.toHom).support at hv
      exact hv
    rw [SimpleGraph.Walk.support_map] at hv'
    obtain ⟨u, -, hu⟩ := List.mem_map.mp hv'
    change (u : V) = v at hu
    exact u.property (hu.symm ▸ hvZ)

end Woven
end HadwigerLean