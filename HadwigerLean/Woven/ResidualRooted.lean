import HadwigerLean.Woven.MixedFanWoven

/-!
# Rooted residual models supplied by the child woven property
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {a b j : ℕ}
  {Z U H : Finset V}
  {P : IndexedPairs (Fin a × Fin 2) V}

/-- Wovenness of an induced residual graph supplies an ambient rooted
clique model on any distinct residual roots, with all branches still in
the residual set. -/
theorem residual_rooted_model_of_woven
    (hW : Woven (G.induce (U : Set V)) a b)
    (r : Fin a → V) (hr : Function.Injective r)
    (hrU : ∀ i, r i ∈ U) :
    ∃ M : RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G r,
      ∀ i, M.branch i ⊆ (U : Set V) := by
  let r' : Fin a → (U : Set V) := fun i => ⟨r i, hrU i⟩
  have hr'inj : Function.Injective r' := by
    intro i k h
    exact hr (congrArg Subtype.val h)
  obtain ⟨M⟩ := hW.rooted_minor r' hr'inj
  let e : (G.induce (U : Set V)) ↪g G :=
    SimpleGraph.Embedding.induce (U : Set V)
  let N := M.map e.toHom e.injective
  have hN : ∀ i, N.branch i ⊆ (U : Set V) := by
    intro i x hx
    rcases hx with ⟨y,_,rfl⟩
    exact y.property
  have hroot : (e.toHom ∘ r') = r := by
    funext i
    rfl
  exact ⟨hroot ▸ N, by
    cases hroot
    exact hN⟩

/-- The residual Woven hypothesis can be fed directly into the mixed-fan
proxy construction. -/
theorem exists_proxy_woven_of_mixed_fan_and_woven_residual
    (F : DoubleFan G Z H) (C : IndexedLinkage G P)
    (hU : ∀ slot, P.start slot ∈ U)
    (hfinish : ∀ slot, P.finish slot ∈ H)
    (havoidZ : ∀ slot v, v ∈ pathVertexSet (C.path slot) → v ∉ Z)
    (hfanU : ∀ slot v, v ∈ pathVertexSet (F.path slot) → v ∉ U)
    (hZU : Disjoint Z U) (hHU : Disjoint H U)
    (hZH : Disjoint Z H)
    (proxy : HubProxyRole a j ≃ Z)
    (hW : Woven (G.induce (U : Set V)) a b)
    (hlinked : Linkedness.KLinked (G.induce (H : Set V)) (a+j))
    (horder : 2 * (a+j) ≤ Fintype.card (↥(H : Set V))) :
    Nonempty (WovenSolution G (hubProxyRoots proxy)
      (hubProxyPairs proxy)) := by
  exact exists_proxy_woven_of_mixed_fan F C hU hfinish havoidZ hfanU
    hZU hHU hZH proxy
    (fun r hr hrU => residual_rooted_model_of_woven hW r hr hrU)
    hlinked horder

end Woven
end HadwigerLean
