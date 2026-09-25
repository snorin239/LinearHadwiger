import HadwigerLean.Graph.RootedDensity.UniversalTargetInduce
import HadwigerLean.Graph.RootedDensity.MassedStructure

/-! Restriction of rigid-shore universality to an induced target. -/

namespace HadwigerLean.RootedDensity

universe u v

theorem UniversalAtRightShore.target_induce
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {G : SimpleGraph V} (S : VertexSeparation G)
    (H : SimpleGraph W) (h : UniversalAtRightShore H S)
    (Y : Set W) [Fintype Y] :
    UniversalAtRightShore (H.induce Y) S := by
  classical
  letI : Fintype S.right := Fintype.ofFinite S.right
  change UniversalAt (G.induce S.right) H
    (Linkedness.separationBoundaryFinset S) at h
  change UniversalAt (G.induce S.right) (H.induce Y)
    (Linkedness.separationBoundaryFinset S)
  exact h.target_induce Y

end HadwigerLean.RootedDensity
