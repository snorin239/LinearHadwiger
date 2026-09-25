import HadwigerLean.Graph.RootedDensity.TorsoHangerIndex
import Mathlib.Tactic

/-!
# Distinct adhesion vertices for global torso pieces

Different touching branches have different center vertices. Hanging
indices have distinct boundary vertices, and no hanger boundary is a
center boundary. These are the embeddings used by the colored
adhesion-label assignment.
-/

namespace HadwigerLean.RootedDensity

universe u v

noncomputable def torsoCenterBoundary
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (t : TorsoTouchIndex S M) : S.left :=
  (chosenTorsoStar G S H root M hmin t).center.1

theorem torsoCenterBoundary_injective
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N) :
    Function.Injective (torsoCenterBoundary G S H root M hmin) := by
  intro a b hab
  apply Subtype.ext
  by_contra hne
  have ha : torsoCenterBoundary G S H root M hmin a ∈ M.branch a.1 :=
    (chosenTorsoStar G S H root M hmin a).center.2
  have hb : torsoCenterBoundary G S H root M hmin b ∈ M.branch b.1 :=
    (chosenTorsoStar G S H root M hmin b).center.2
  exact (Set.disjoint_left.mp (M.disjoint hne)) ha (hab ▸ hb)

theorem torsoHangerBoundary_injective
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N) :
    Function.Injective (torsoHangerBoundary G S H root M hmin) := by
  intro a b hab
  rcases a with ⟨ta,za⟩
  rcases b with ⟨tb,zb⟩
  have howner : ta.1 = tb.1 := by
    by_contra hne
    have ha : za.1.1 ∈ M.branch ta.1 := za.1.2
    have hb : zb.1.1 ∈ M.branch tb.1 := zb.1.2
    have heq : za.1.1 = zb.1.1 := hab
    exact (Set.disjoint_left.mp (M.disjoint hne))
      ha (heq.symm ▸ hb)
  have ht : ta = tb := Subtype.ext howner
  subst tb
  have hz : za.1 = zb.1 := Subtype.ext hab
  have hzz : za = zb := Subtype.ext hz
  subst zb
  rfl

theorem torsoCenter_ne_hangerBoundary
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (t : TorsoTouchIndex S M)
    (w : TorsoHangerIndex G S H root M hmin) :
    torsoCenterBoundary G S H root M hmin t ≠
      torsoHangerBoundary G S H root M hmin w := by
  intro heq
  by_cases howner : t.1 = w.1.1
  · have ht : t = w.1 := Subtype.ext howner
    subst t
    have hceq : (chosenTorsoStar G S H root M hmin w.1).center =
        w.2.1 := Subtype.ext heq
    exact w.2.2.2 hceq.symm
  · have hc : torsoCenterBoundary G S H root M hmin t ∈ M.branch t.1 :=
      (chosenTorsoStar G S H root M hmin t).center.2
    have hw : torsoHangerBoundary G S H root M hmin w ∈ M.branch w.1.1 :=
      w.2.1.2
    exact (Set.disjoint_left.mp (M.disjoint howner))
      hc (heq ▸ hw)

end HadwigerLean.RootedDensity
