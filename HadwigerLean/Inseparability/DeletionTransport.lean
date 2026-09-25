import HadwigerLean.Graph.VertexConnectivity

/-!
# Transport deletion through an induced graph

Deleting a finite set of subtype vertices from an induced graph is naturally
isomorphic to inducing the ambient graph on the corresponding set difference.
This lets connectivity statements from `VertexConnected` be used on ambient
vertex sets when two connected regions are glued.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def deletionIso (G : SimpleGraph V)
    (S : Finset V) (D : Finset (↥(S : Set V))) :
    ((G.induce (S : Set V)).induce (D : Set ↥(S : Set V))ᶜ) ≃g
      G.induce ((S \ D.image Subtype.val : Finset V) : Set V) := by
  classical
  let e : (↥((D : Set ↥(S : Set V))ᶜ)) ≃
      ↥((S \ D.image Subtype.val : Finset V) : Set V) := {
    toFun := fun z => by
      have hzS : (z.1.1 : V) ∈ S := z.1.2
      have hzD : (z.1.1 : V) ∉ D.image Subtype.val := by
        intro hv
        obtain ⟨w,hw,hval⟩ := Finset.mem_image.mp hv
        have heq : w = z.1 := Subtype.ext hval
        exact z.2 (heq ▸ hw)
      exact ⟨z.1.1, Finset.mem_sdiff.mpr ⟨hzS,hzD⟩⟩
    invFun := fun z => by
      have hzS : z.1 ∈ S := (Finset.mem_sdiff.mp z.2).1
      have hzD : (⟨z.1,hzS⟩ : ↥(S : Set V)) ∉ D := by
        intro hv
        exact (Finset.mem_sdiff.mp z.2).2
          (Finset.mem_image.mpr ⟨⟨z.1,hzS⟩,hv,rfl⟩)
      exact ⟨⟨z.1,hzS⟩,hzD⟩
    left_inv := by intro z; apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := by intro z; apply Subtype.ext; rfl
  }
  exact {
    toEquiv := e
    map_rel_iff' := by intro x y; rfl
  }

end Inseparability
end HadwigerLean
