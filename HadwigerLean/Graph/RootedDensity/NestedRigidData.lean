import HadwigerLean.Graph.Linkedness.TorsoFarGlue
import HadwigerLean.Graph.RootedDensity.UniversalIso
import HadwigerLean.Graph.RootedDensity.MassedStructure
import Mathlib.Tactic

/-! Transport the two H-universal pieces of a nested rigid shore through
the canonical near and far graph isomorphisms. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- Inside the far side of a torso-shore glue, the restricted separation
has a universal near torso and a universal far shore, rooted at the new
glued adhesion. -/
theorem nested_rigid_universal_data
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W]
    {G : SimpleGraph V} (S : VertexSeparation G) [Fintype S.left]
    (T : VertexSeparation (Linkedness.torsoGraph G S))
    (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right)
    [Fintype (Linkedness.glueTorsoFar S T hBoundary).right]
    [DecidableEq (Linkedness.glueTorsoFar S T hBoundary).right]
    [Fintype (Linkedness.glueTorsoFarRestricted S T hBoundary).left]
    (H : SimpleGraph W)
    (hfar : UniversalAtRightShore H S)
    (hT : UniversalAtRightShore H T) :
    let Q := Linkedness.glueTorsoFar S T hBoundary
    let R := Linkedness.glueTorsoFarRestricted S T hBoundary
    let X : Finset Q.right := Linkedness.separationBoundaryFinset Q
    let Y : Finset R.left :=
      @Finset.subtype Q.right R.left (Classical.decPred R.left) X
    (X : Set Q.right) ⊆ R.left ∧
      (∀ z : R.left, z ∈ Y ↔ (z : Q.right) ∈ X) ∧
      UniversalAt (Linkedness.torsoGraph (G.induce Q.right) R) H Y ∧
      (Linkedness.separationBoundaryFinset R).card =
        (Linkedness.separationBoundaryFinset S).card ∧
      UniversalAtRightShore H R := by
  classical
  intro Q R X Y
  have hX : (X : Set Q.right) ⊆ R.left := by
    intro x hx
    have hxL : (x : V) ∈ Q.left :=
      (Linkedness.mem_separationBoundaryFinset Q x).mp hx
    have hImg : (x : V) ∈ Subtype.val '' T.left := by
      simpa only [Q, Linkedness.glueTorsoFar_left] using hxL
    obtain ⟨u,huL,hux⟩ := hImg
    change (x : V) ∈ S.left
    exact hux ▸ u.property
  have hY (z : R.left) : z ∈ Y ↔ (z : Q.right) ∈ X := by
    exact Finset.mem_subtype
  let eN := Linkedness.glueTorsoFar_nearIso S T hBoundary
  have hmemN (z : R.left) :
      z ∈ Y ↔ eN z ∈ Linkedness.separationBoundaryFinset T := by
    rw [hY]
    constructor
    · intro hz
      have hzL : ((z : Q.right) : V) ∈ Q.left :=
        (Linkedness.mem_separationBoundaryFinset Q (z : Q.right)).mp hz
      have hzImg : ((z : Q.right) : V) ∈ Subtype.val '' T.left := by
        simpa only [Q, Linkedness.glueTorsoFar_left] using hzL
      obtain ⟨u,huL,huz⟩ := hzImg
      have he : (u : V) = (((eN z : T.right) : S.left) : V) := by
        exact huz.trans (Linkedness.glueTorsoFar_nearIso_val S T hBoundary z).symm
      have hue : u = ((eN z : T.right) : S.left) := Subtype.val_injective he
      exact (Linkedness.mem_separationBoundaryFinset T (eN z)).mpr (hue ▸ huL)
    · intro hz
      have huL : ((eN z : T.right) : S.left) ∈ T.left :=
        (Linkedness.mem_separationBoundaryFinset T (eN z)).mp hz
      have hzL : ((z : Q.right) : V) ∈ Q.left := by
        change ((z : Q.right) : V) ∈
          (Linkedness.glueTorsoFar S T hBoundary).left
        rw [Linkedness.glueTorsoFar_left]
        exact ⟨((eN z : T.right) : S.left),huL,
          Linkedness.glueTorsoFar_nearIso_val S T hBoundary z⟩
      exact (Linkedness.mem_separationBoundaryFinset Q (z : Q.right)).mpr hzL
  have hnearImage :
      (Linkedness.separationBoundaryFinset T).image eN.symm = Y := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      exact (hmemN (eN.symm w)).2 (by simpa using hw)
    · intro hz
      apply Finset.mem_image.mpr
      exact ⟨eN z, (hmemN z).1 hz, by simp⟩
  have hKN : UniversalAt
      (Linkedness.torsoGraph (G.induce Q.right) R) H Y := by
    rw [← hnearImage]
    exact UniversalAt.of_iso eN.symm
      (Linkedness.separationBoundaryFinset T) hT
  let eF := Linkedness.glueTorsoFar_farIso S T hBoundary
  have hmemF (z : R.right) :
      z ∈ Linkedness.separationBoundaryFinset R ↔
        eF z ∈ Linkedness.separationBoundaryFinset S := by
    rw [Linkedness.mem_separationBoundaryFinset,
      Linkedness.mem_separationBoundaryFinset]
    exact (Linkedness.glueTorsoFar_farIso_val S T hBoundary z).symm ▸ Iff.rfl
  have hfarImage :
      (Linkedness.separationBoundaryFinset S).image eF.symm =
        Linkedness.separationBoundaryFinset R := by
    ext z
    constructor
    · intro hz
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
      apply (hmemF (eF.symm w)).2
      rw [eF.apply_symm_apply]
      exact hw
    · intro hz
      apply Finset.mem_image.mpr
      exact ⟨eF z,(hmemF z).1 hz, eF.symm_apply_apply z⟩
  have hfarCard : (Linkedness.separationBoundaryFinset R).card =
      (Linkedness.separationBoundaryFinset S).card := by
    rw [← hfarImage, Finset.card_image_of_injective _ eF.symm.injective]
  have hfarR : UniversalAtRightShore H R := by
    change UniversalAt ((G.induce Q.right).induce R.right) H
      (Linkedness.separationBoundaryFinset R)
    rw [← hfarImage]
    change UniversalAt (G.induce S.right) H
      (Linkedness.separationBoundaryFinset S) at hfar
    exact UniversalAt.of_iso eF.symm
      (Linkedness.separationBoundaryFinset S) hfar
  exact ⟨hX,hY,hKN,hfarCard,hfarR⟩

end HadwigerLean.RootedDensity
