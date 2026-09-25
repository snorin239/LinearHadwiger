import HadwigerLean.Woven.ThreeChildRootedBridge
import HadwigerLean.Woven.MixedFanWoven

/-!
# Transport a rooted model from the residual graph

The three-child construction works inside the residual induced graph. This
lemma maps the resulting rooted clique model back to the ambient graph while
keeping every branch in the residual vertex set. Its conclusion is the exact
model contract required by the mixed-fan woven construction.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {a : ℕ} {U : Finset V}

/-- An induced rooted clique minor becomes an ambient model with every branch
supported in the inducing set. -/
theorem residual_rooted_model_of_induced_minor
    (r : Fin a → V) (hrU : ∀ i, r i ∈ U)
    (hminor : HasRootedCliqueMinor (G.induce (U : Set V))
      (fun i => (⟨r i, hrU i⟩ : (U : Set V)))) :
    ∃ M : RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G r,
      ∀ i, M.branch i ⊆ (U : Set V) := by
  obtain ⟨M⟩ := hminor
  let e : (G.induce (U : Set V)) ↪g G :=
    SimpleGraph.Embedding.induce (U : Set V)
  let N := M.map e.toHom e.injective
  have hN : ∀ i, N.branch i ⊆ (U : Set V) := by
    intro i x hx
    rcases hx with ⟨y,_,rfl⟩
    exact y.property
  have hroot : (e.toHom ∘ fun i => (⟨r i, hrU i⟩ : (U : Set V))) = r := by
    funext i
    rfl
  exact ⟨hroot ▸ N, by
    cases hroot
    exact hN⟩

/-- A uniform geometric construction in the residual induced graph gives
precisely the supported-rooted-model premise of `exists_proxy_woven_of_mixed_fan`.
In particular, the geometry may be supplied by
`rooted_minor_of_three_woven_children_linked_complement` for each root map. -/
theorem residual_rooted_model_of_induced_minor_for_every_root
    (hminor : ∀ (r : Fin a → (U : Set V)), Function.Injective r →
      HasRootedCliqueMinor (G.induce (U : Set V)) r)
    (r : Fin a → V) (hr : Function.Injective r)
    (hrU : ∀ i, r i ∈ U) :
    ∃ M : RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G r,
      ∀ i, M.branch i ⊆ (U : Set V) := by
  let r' : Fin a → (U : Set V) := fun i => ⟨r i, hrU i⟩
  have hr'inj : Function.Injective r' := by
    intro i k h
    exact hr (congrArg Subtype.val h)
  exact residual_rooted_model_of_induced_minor r hrU (hminor r' hr'inj)

end Woven
end HadwigerLean
