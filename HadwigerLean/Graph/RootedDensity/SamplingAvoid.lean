import HadwigerLean.Graph.RootedDensity.Sampling
import HadwigerLean.Graph.InducedFinsetLift

/-! Sampling a dense induced complement while preserving excluded roots. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- The induced-density sample can be taken disjoint from an arbitrary
forbidden vertex set, with its minor model returned in the ambient graph. -/
theorem exists_induced_minor_avoiding_of_sampling_budget
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (c : ℝ) (hc : 0 ≤ c) (hforces : DensityForcesMinor.{u,v} H c)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X : Finset V)
    (hn : 2 ≤ Fintype.card ↥((X : Set V)ᶜ))
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hbudget : c * (p * (Fintype.card ↥((X : Set V)ᶜ) : ℝ) + 2) <
      p ^ 2 * (edgeCount (G.induce (X : Set V)ᶜ) : ℝ)) :
    ∃ S : Finset V,
      Disjoint X S ∧
      (S.card : ℝ) ≤ p * (Fintype.card ↥((X : Set V)ᶜ) : ℝ) + 2 ∧
      Nonempty (MinorModel H (G.induce (S : Set V))) := by
  classical
  obtain ⟨s, hs, ⟨M⟩⟩ :=
    exists_induced_minor_of_sampling_budget H c hc hforces
      (G.induce (X : Set V)ᶜ) hn p hp hp1 hbudget
  let S : Finset V := s.image Subtype.val
  have hXS : Disjoint X S :=
    (disjoint_induced_compl_finset_image X s).symm
  have hS : (S.card : ℝ) ≤
      p * (Fintype.card ↥((X : Set V)ᶜ) : ℝ) + 2 := by
    rw [show S.card = s.card from card_induced_finset_image _ s]
    exact hs
  let φ : ((G.induce (X : Set V)ᶜ).induce (s : Set ↥((X : Set V)ᶜ))) →g
      G.induce (S : Set V) := {
    toFun := fun x => ⟨x.1.1, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩
    map_rel' := by intro x y hxy; exact hxy
  }
  have hφ : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(S : Set V) => (z : V)) hxy
  exact ⟨S, hXS, hS, ⟨M.map φ hφ⟩⟩

end HadwigerLean.RootedDensity

