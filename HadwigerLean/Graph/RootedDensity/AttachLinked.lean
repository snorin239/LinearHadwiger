import HadwigerLean.Graph.RootedDensity.AttachInduced
import HadwigerLean.Graph.Linkedness.Final
import Mathlib.Data.Fintype.EquivFin

/-! A linked complement attaches an induced target minor to arbitrary roots. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- If the complement of an unrooted target model is linked, distinct
root/proxy pairs can be attached while retaining all target edges. -/
theorem rootedMinor_of_induced_minor_and_linked_complement
    {W : Type u} {V : Type v} [Fintype W] [Fintype V]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (S : Set V) [Fintype ↥(Sᶜ : Set V)]
    (M : MinorModel H (G.induce S))
    (r p : W → ↥(Sᶜ : Set V))
    (hr : Function.Injective r) (hp : Function.Injective p)
    (hrp : Disjoint (Set.range r) (Set.range p))
    (hattach : ∀ i, ∃ x ∈ M.branch i, G.Adj (x : V) (p i : V))
    (hlinked : Linkedness.KLinked (G.induce Sᶜ) (Fintype.card W)) :
    Nonempty (RootedMinorModel H G (fun i => (r i : V))) := by
  classical
  let e : W ≃ Fin (Fintype.card W) := Fintype.equivFin W
  let Q : IndexedPairs (Fin (Fintype.card W)) ↥(Sᶜ : Set V) := {
    start := fun i => r (e.symm i)
    finish := fun i => p (e.symm i)
  }
  have hcross (i j : W) : r i ≠ p j := by
    intro h
    exact (Set.disjoint_left.mp hrp) ⟨i, rfl⟩ ⟨j, h.symm⟩
  have hQdisj : Q.DisjointTerminals := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    change x = r (e.symm i) ∨ x = p (e.symm i) at hxi
    change x = r (e.symm j) ∨ x = p (e.symm j) at hxj
    rcases hxi with hxi | hxi <;> rcases hxj with hxj | hxj
    · exact hij (e.symm.injective (hr (hxi.symm.trans hxj)))
    · exact hcross _ _ (hxi.symm.trans hxj)
    · exact hcross _ _ (hxj.symm.trans hxi)
    · exact hij (e.symm.injective (hp (hxi.symm.trans hxj)))
  have hQne : ∀ i, Q.start i ≠ Q.finish i := by
    intro i
    exact hcross _ _
  obtain ⟨LQ⟩ := hlinked Q hQdisj hQne
  let P := Q.reindex e.toEmbedding
  let L : IndexedLinkage (G.induce Sᶜ) P := LQ.reindex e.toEmbedding
  have hstart (i : W) : (P.start i : V) = (r i : V) := by
    simp [P, Q, IndexedPairs.reindex]
  have hattach' (i : W) : ∃ x ∈ M.branch i,
      G.Adj (x : V) (P.finish i : V) := by
    simpa [P, Q, IndexedPairs.reindex] using hattach i
  exact rootedMinor_of_induced_minor_and_complement_linkage S M P L
    (fun i => (r i : V)) hstart hattach'

end HadwigerLean.RootedDensity
