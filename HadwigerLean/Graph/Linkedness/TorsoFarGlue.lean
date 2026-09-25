import HadwigerLean.Graph.Linkedness.TorsoLinkageGlue
import HadwigerLean.Graph.Linkedness.NestedRootedReverse
import HadwigerLean.Graph.Linkedness.CoreFarFan
import Mathlib.Tactic

namespace HadwigerLean
namespace Linkedness

/-- The adhesion of a torso far-shore glue is exactly the image of the
torso adhesion. -/
theorem glueTorsoFar_separator_set
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    (T : VertexSeparation (torsoGraph G S))
    (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right) :
    (glueTorsoFar S T hBoundary).separator = Subtype.val '' T.separator := by
  ext x
  constructor
  · intro hx
    rw [VertexSeparation.separator] at hx
    obtain ⟨u,huL,hux⟩ := (glueTorsoFar_left S T hBoundary).symm ▸ hx.1
    subst x
    have huR : u ∈ T.right := by
      rcases (glueTorsoFar_right S T hBoundary).symm ▸ hx.2 with hSR | ⟨w,hwR,hwu⟩
      · exact hBoundary u hSR
      · exact Subtype.val_injective hwu ▸ hwR
    exact ⟨u,⟨huL,huR⟩,rfl⟩
  · rintro ⟨u,hu,hux⟩
    subst x
    constructor
    · rw [glueTorsoFar_left S T hBoundary]
      exact ⟨u,hu.1,rfl⟩
    · rw [glueTorsoFar_right S T hBoundary]
      exact Or.inr ⟨u,hu.2,rfl⟩


/-- Restrict the original separation to the far side of a torso-shore glue. -/
def glueTorsoFarRestricted
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    (T : VertexSeparation (torsoGraph G S))
    (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right) :
    VertexSeparation (G.induce (glueTorsoFar S T hBoundary).right) where
  left := {x | (x : V) ∈ S.left}
  right := {x | (x : V) ∈ S.right}
  cover := by
    ext x
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have hx : (x : V) ∈ S.right ∪ Subtype.val '' T.right := by
      have hq := x.property
      change (x : V) ∈ (glueTorsoFar S T hBoundary).right at hq
      simpa only [glueTorsoFar_right] using hq
    rcases hx with hxR | ⟨u,huT,hux⟩
    · exact Or.inr hxR
    · exact Or.inl (hux ▸ u.property)
  no_cross := by
    intro x y hxL hxNotR hyR hyNotL hxy
    exact S.no_cross hxL hxNotR hyR hyNotL hxy

/-- The near side of the restricted separation is the torso far side. -/
theorem glueTorsoFarRestricted_near_image
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    (T : VertexSeparation (torsoGraph G S))
    (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right) :
    let Q := glueTorsoFar S T hBoundary
    let R := glueTorsoFarRestricted S T hBoundary
    (Subtype.val : Q.right → V) '' (R.left : Set Q.right) =
      (Subtype.val : S.left → V) '' (T.right : Set S.left) := by
  intro Q R
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    have hxS : (x : V) ∈ S.left := hx
    have hxQ : (x : V) ∈ S.right ∪ Subtype.val '' T.right := by
      have hq := x.property
      change (x : V) ∈ (glueTorsoFar S T hBoundary).right at hq
      simpa only [glueTorsoFar_right] using hq
    rcases hxQ with hxR | ⟨u,huT,hux⟩
    · exact ⟨⟨x,hxS⟩,hBoundary ⟨x,hxS⟩ hxR,rfl⟩
    · exact ⟨u,huT,hux⟩
  · rintro ⟨u,huT,rfl⟩
    have huQ : (u : V) ∈ Q.right := by
      rw [glueTorsoFar_right]
      exact Or.inr ⟨u,huT,rfl⟩
    exact ⟨⟨(u : V),huQ⟩,u.property,rfl⟩

/-- The far side of the restricted separation is the original far side. -/
theorem glueTorsoFarRestricted_far_image
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    (T : VertexSeparation (torsoGraph G S))
    (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right) :
    let Q := glueTorsoFar S T hBoundary
    let R := glueTorsoFarRestricted S T hBoundary
    (Subtype.val : Q.right → V) '' (R.right : Set Q.right) = S.right := by
  intro Q R
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hx
  · intro hz
    have hzQ : z ∈ Q.right := by
      rw [glueTorsoFar_right]
      exact Or.inl hz
    exact ⟨⟨z,hzQ⟩,hz,rfl⟩

/-- The completed near side of the restricted glue is the induced torso
far shore. -/
noncomputable def glueTorsoFar_nearIso
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    (T : VertexSeparation (torsoGraph G S))
    (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right) :
    let Q := glueTorsoFar S T hBoundary
    let R := glueTorsoFarRestricted S T hBoundary
    torsoGraph (G.induce Q.right) R ≃g (torsoGraph G S).induce T.right := by
  intro Q R
  let hset := glueTorsoFarRestricted_near_image S T hBoundary
  let e1 : R.left ≃ (Subtype.val '' (R.left : Set Q.right) : Set V) :=
    Equiv.Set.image (fun x : Q.right => (x : V)) (R.left : Set Q.right)
      Subtype.val_injective
  let e2 : T.right ≃ (Subtype.val '' (T.right : Set S.left) : Set V) :=
    Equiv.Set.image (fun x : S.left => (x : V)) (T.right : Set S.left)
      Subtype.val_injective
  let e : R.left ≃ T.right := (e1.trans (Equiv.setCongr hset)).trans e2.symm
  refine { toEquiv := e, map_rel_iff' := ?_ }
  intro x y
  have he (z : R.left) : (((e z : T.right) : S.left) : V) = ((z : Q.right) : V) := by
    have hh := e2.apply_symm_apply ((e1.trans (Equiv.setCongr hset)) z)
    exact congrArg Subtype.val hh
  simp only [torsoGraph, SimpleGraph.induce_adj]
  rw [he x, he y]
  constructor
  · intro h
    rcases h with hG | ⟨hx,hy,hne⟩
    · exact Or.inl hG
    · right
      exact ⟨hx,hy,fun hxy => hne (congrArg Subtype.val (congrArg e hxy))⟩
  · intro h
    rcases h with hG | ⟨hx,hy,hne⟩
    · exact Or.inl hG
    · right
      exact ⟨hx,hy,fun hxy => hne (e.injective (Subtype.ext hxy))⟩
/-- The restricted far shore is isomorphic to the original induced far shore. -/
noncomputable def glueTorsoFar_farIso
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    (T : VertexSeparation (torsoGraph G S))
    (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right) :
    let Q := glueTorsoFar S T hBoundary
    let R := glueTorsoFarRestricted S T hBoundary
    (G.induce Q.right).induce R.right ≃g G.induce S.right := by
  intro Q R
  let hset := glueTorsoFarRestricted_far_image S T hBoundary
  refine {
    toEquiv := (Equiv.Set.image (fun x : Q.right => (x : V))
      (R.right : Set Q.right) Subtype.val_injective).trans
        (Equiv.setCongr hset)
    map_rel_iff' := ?_
  }
  intro x y
  rfl

/-- The near-side torso isomorphism preserves the underlying original vertex. -/
theorem glueTorsoFar_nearIso_val
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    (T : VertexSeparation (torsoGraph G S))
    (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right)
    (z : (glueTorsoFarRestricted S T hBoundary).left) :
    ((((glueTorsoFar_nearIso S T hBoundary) z : T.right) : S.left) : V) =
      ((z : (glueTorsoFar S T hBoundary).right) : V) := by
  let Q := glueTorsoFar S T hBoundary
  let R := glueTorsoFarRestricted S T hBoundary
  let hset := glueTorsoFarRestricted_near_image S T hBoundary
  let e1 : R.left ≃ (Subtype.val '' (R.left : Set Q.right) : Set V) :=
    Equiv.Set.image (fun x : Q.right => (x : V)) (R.left : Set Q.right)
      Subtype.val_injective
  let e2 : T.right ≃ (Subtype.val '' (T.right : Set S.left) : Set V) :=
    Equiv.Set.image (fun x : S.left => (x : V)) (T.right : Set S.left)
      Subtype.val_injective
  have hh := e2.apply_symm_apply ((e1.trans (Equiv.setCongr hset)) z)
  exact congrArg Subtype.val hh

/-- The far-side isomorphism preserves the underlying original vertex. -/
theorem glueTorsoFar_farIso_val
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    (T : VertexSeparation (torsoGraph G S))
    (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right)
    (z : (glueTorsoFarRestricted S T hBoundary).right) :
    ((glueTorsoFar_farIso S T hBoundary) z : V) =
      ((z : (glueTorsoFar S T hBoundary).right) : V) := by
  rfl

/-- Linkedness of a dense torso far shore glues through a linked original
far shore to give linkedness of the larger induced far shore. -/
theorem rootedLinked_glueTorsoFar
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : VertexSeparation G) [Fintype S.left]
    (T : VertexSeparation (torsoGraph G S))
    (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right)
    (hfar : RootedLinked (G.induce S.right)
      (separationBoundaryFinset S))
    (hT : RootedLinked ((torsoGraph G S).induce T.right)
      (separationBoundaryFinset T)) :
    RootedLinked (G.induce (glueTorsoFar S T hBoundary).right)
      (separationBoundaryFinset (glueTorsoFar S T hBoundary)) := by
  classical
  let Q := glueTorsoFar S T hBoundary
  let H := G.induce Q.right
  let R := glueTorsoFarRestricted S T hBoundary
  letI : Fintype Q.right := Fintype.ofFinite Q.right
  letI : DecidableEq Q.right := Classical.decEq _
  let X : Finset Q.right := separationBoundaryFinset Q
  have hX : (X : Set Q.right) ⊆ R.left := by
    intro x hx
    have hxL : (x : V) ∈ Q.left :=
      (mem_separationBoundaryFinset Q x).mp hx
    have hImg : (x : V) ∈ Subtype.val '' T.left := by
      simpa only [Q, glueTorsoFar_left] using hxL
    obtain ⟨u,huL,hux⟩ := hImg
    change (x : V) ∈ S.left
    exact hux ▸ u.property
  let Y : Finset R.left := @Finset.subtype Q.right R.left
    (Classical.decPred R.left) X
  have hY (z : R.left) : z ∈ Y ↔ (z : Q.right) ∈ X := by
    exact Finset.mem_subtype
  let eN := glueTorsoFar_nearIso S T hBoundary
  have hmemN (z : R.left) :
      z ∈ Y ↔ eN z ∈ separationBoundaryFinset T := by
    rw [hY]
    constructor
    · intro hz
      have hzL : ((z : Q.right) : V) ∈ Q.left :=
        (mem_separationBoundaryFinset Q (z : Q.right)).mp hz
      have hzImg : ((z : Q.right) : V) ∈ Subtype.val '' T.left := by
        simpa only [Q, glueTorsoFar_left] using hzL
      obtain ⟨u,huL,huz⟩ := hzImg
      have he : (u : V) = (((eN z : T.right) : S.left) : V) := by
        exact huz.trans (glueTorsoFar_nearIso_val S T hBoundary z).symm
      have hue : u = ((eN z : T.right) : S.left) := Subtype.val_injective he
      exact (mem_separationBoundaryFinset T (eN z)).mpr (hue ▸ huL)
    · intro hz
      have huL : ((eN z : T.right) : S.left) ∈ T.left :=
        (mem_separationBoundaryFinset T (eN z)).mp hz
      have hzL : ((z : Q.right) : V) ∈ Q.left := by
        change ((z : Q.right) : V) ∈
          (glueTorsoFar S T hBoundary).left
        rw [glueTorsoFar_left]
        exact ⟨((eN z : T.right) : S.left),huL,
          glueTorsoFar_nearIso_val S T hBoundary z⟩
      exact (mem_separationBoundaryFinset Q (z : Q.right)).mpr hzL
  have hKN : RootedLinked (torsoGraph H R) Y := by
    have hmem : ∀ z : T.right,
        z ∈ separationBoundaryFinset T ↔ eN.symm z ∈ Y := by
      intro z
      simpa only [eN.apply_symm_apply] using (hmemN (eN.symm z)).symm
    exact rootedLinked_of_iso eN.symm (separationBoundaryFinset T) Y hmem hT
  let eF := glueTorsoFar_farIso S T hBoundary
  have hmemF (z : R.right) :
      z ∈ separationBoundaryFinset R ↔
        eF z ∈ separationBoundaryFinset S := by
    rw [mem_separationBoundaryFinset, mem_separationBoundaryFinset]
    exact (glueTorsoFar_farIso_val S T hBoundary z).symm ▸ Iff.rfl
  have hfarR : RootedLinked (H.induce R.right)
      (separationBoundaryFinset R) := by
    have hmem : ∀ z : S.right,
        z ∈ separationBoundaryFinset S ↔
          eF.symm z ∈ separationBoundaryFinset R := by
      intro z
      simpa only [eF.apply_symm_apply] using (hmemF (eF.symm z)).symm
    exact rootedLinked_of_iso eF.symm (separationBoundaryFinset S)
      (separationBoundaryFinset R) hmem hfar
  exact rootedLinked_of_torso_and_far H R X Y hX hY hKN hfarR
end Linkedness
end HadwigerLean
