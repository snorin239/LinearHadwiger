import HadwigerLean.Graph.RootedDensity.TorsoHangerInjection
import HadwigerLean.Graph.RootedDensity.ColoredMatching
import Mathlib.Tactic

/-!
# The colored matching on all torso hanging pieces

The hanger boundary map embeds the dependent global hanger type into
the finite torso vertex type. This supplies the finite instances for
the two-color matching theorem.
-/

namespace HadwigerLean.RootedDensity

universe u v

theorem exists_torso_hanger_matching
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    [DecidableEq (TorsoHangerIndex G S H root M hmin)]
    [DecidableEq (TorsoFreeIndex S M)] :
    Nonempty (TwoColorMatching
      (TorsoHangerRel G S H root M hmin)) := by
  classical
  haveI : Finite (TorsoHangerIndex G S H root M hmin) :=
    Finite.of_injective
      (torsoHangerBoundary G S H root M hmin)
      (torsoHangerBoundary_injective G S H root M hmin)
  haveI : Finite (TorsoFreeIndex S M) :=
    Finite.of_injective
      (fun j : TorsoFreeIndex S M => j.1)
      (fun _ _ h => Subtype.ext h)
  letI : Fintype (TorsoHangerIndex G S H root M hmin) :=
    Fintype.ofFinite _
  letI : Fintype (TorsoFreeIndex S M) := Fintype.ofFinite _
  exact exists_twoColorMatching
    (TorsoHangerRel G S H root M hmin)

end HadwigerLean.RootedDensity
