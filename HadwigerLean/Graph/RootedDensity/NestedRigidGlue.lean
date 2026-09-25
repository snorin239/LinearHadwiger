import HadwigerLean.Graph.RootedDensity.NestedRigidData

/-! The nested F.a torso-shore glue, factored through one reverse rigid
model transport in the induced far region. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- Universal far shores of two nested rigid separations glue once the
ambient-target reverse rigid transport is available in the induced region.
The inner target label set may be smaller than the outer adhesion. -/
theorem universalAtRightShore_glueTorsoFar_of_reverse
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
    (hsize : (Linkedness.separationBoundaryFinset S).card ≤ Fintype.card W)
    (hT : UniversalAtRightShore H T)
    (hreverse :
      let Q := Linkedness.glueTorsoFar S T hBoundary
      let R := Linkedness.glueTorsoFarRestricted S T hBoundary
      let X := Linkedness.separationBoundaryFinset Q
      (X : Set Q.right) ⊆ R.left →
      (Linkedness.separationBoundaryFinset R).card ≤ Fintype.card W →
      UniversalAtRightShore H R →
      UniversalAt (Linkedness.torsoGraph (G.induce Q.right) R) H
        (Linkedness.torsoRootFinset R X) →
      UniversalAt (G.induce Q.right) H X) :
    UniversalAtRightShore H (Linkedness.glueTorsoFar S T hBoundary) := by
  classical
  let Q := Linkedness.glueTorsoFar S T hBoundary
  let R := Linkedness.glueTorsoFarRestricted S T hBoundary
  let X : Finset Q.right := Linkedness.separationBoundaryFinset Q
  let Y : Finset R.left :=
    @Finset.subtype Q.right R.left (Classical.decPred R.left) X
  obtain ⟨hX,hY,hnear,hcard,hfarR⟩ :=
    nested_rigid_universal_data S T hBoundary H hfar hT
  have hYeq : Linkedness.torsoRootFinset R X = Y := by
    ext z
    rw [Linkedness.mem_torsoRootFinset]
    exact (hY z).symm
  have hnear' : UniversalAt (Linkedness.torsoGraph (G.induce Q.right) R) H
      (Linkedness.torsoRootFinset R X) := by
    rw [hYeq]
    exact hnear
  change UniversalAt (G.induce Q.right) H X
  exact hreverse hX (hcard ▸ hsize) hfarR hnear'

end HadwigerLean.RootedDensity
