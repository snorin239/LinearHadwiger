import HadwigerLean.Inseparability.RawModelTangency
import HadwigerLean.Woven.Knitting
import Mathlib.Tactic

/-!
# Knitting the CI terminal groups inside the central connected piece

The paths have (4p+1)x distinct ends in D. Their owner map is a
surjective partition into (p+1)x groups. The knitting theorem is
applied inside the induced graph on D, and its connected patches are
transported back to the ambient graph.
-/

namespace HadwigerLean.Inseparability

private theorem connected_induce_subtype_image
    {V : Type*} (G : SimpleGraph V) (D : Set V)
    (A : Set D)
    (hconn : ((G.induce D).induce A).Connected) :
    (G.induce (Subtype.val '' A)).Connected := by
  let f : ((G.induce D).induce A) →g
      (G.induce (Subtype.val '' A)) := {
    toFun := fun v => ⟨v.1.1,⟨v.1,v.2,rfl⟩⟩
    map_rel' := by
      intro a b hab
      exact hab
  }
  apply hconn.map f
  rintro ⟨v,hv⟩
  obtain ⟨a,ha,rfl⟩ := hv
  exact ⟨⟨a,ha⟩,rfl⟩

theorem ci_knitting_inside
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (p x : ℕ)
    (D : Finset V)
    (u : CIPathIndex p x → V)
    (huD : ∀ k, u k ∈ D)
    (huinj : Function.Injective u)
    (hconn : VertexConnected (G.induce (D : Set V))
      (33 * ((4 * p + 1) * x))) :
    ∃ C : CIRawIndex p x → Set V,
      (∀ z, (G.induce (C z)).Connected) ∧
      (∀ z w, z ≠ w → Disjoint (C z) (C w)) ∧
      (∀ k, u k ∈ C (pathOwner p x k)) ∧
      (∀ z, C z ⊆ (D : Set V)) := by
  classical
  let e := ciStageIndexEquiv p x
  let v : CIPathIndex p x ↪ (D : Set V) := {
    toFun := fun k => ⟨u k,huD k⟩
    inj' := by
      intro a b hab
      exact huinj (congrArg Subtype.val hab)
  }
  let group : CIPathIndex p x → Fin ((p + 1) * x) :=
    fun k => e.symm (pathOwner p x k)
  have hsurj : Function.Surjective group := by
    intro z
    refine ⟨ciFinalIndex p x (e z), ?_⟩
    simp [group,pathOwner_finalIndex,e]
  obtain ⟨C₀,hCconn,hCdis,hcover⟩ :=
    Woven.exists_knitting_of_vertexConnected
      (G.induce (D : Set V)) ((4 * p + 1) * x)
      ((p + 1) * x) v group hsurj hconn
  let C : CIRawIndex p x → Set V :=
    fun z => Subtype.val '' C₀ (e.symm z)
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · intro z
    exact connected_induce_subtype_image G (D : Set V)
      (C₀ (e.symm z)) (hCconn (e.symm z))
  · intro z w hzw
    have he : e.symm z ≠ e.symm w :=
      fun h => hzw (e.symm.injective h)
    apply Set.disjoint_left.mpr
    intro y hyz hyw
    obtain ⟨a,ha,rfl⟩ := hyz
    obtain ⟨b,hb,hba⟩ := hyw
    have hab : a = b := Subtype.ext hba.symm
    subst b
    exact (Set.disjoint_left.mp (hCdis he)) ha hb
  · intro k
    change u k ∈ Subtype.val '' C₀ (e.symm (pathOwner p x k))
    exact ⟨v k,hcover k,rfl⟩
  · intro z y hy
    obtain ⟨a,_,rfl⟩ := hy
    exact a.property

end HadwigerLean.Inseparability
