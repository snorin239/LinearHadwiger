import HadwigerLean.Graph.RootedDensity.TorsoStarChoice
import HadwigerLean.Graph.RootedDensity.ColoredMatching
import Mathlib.Tactic

/-!
# Global indices for the star pieces of a rooted torso model

Touching branches form one subtype of target labels. A hanging piece
is a touching branch together with a non-center adhesion vertex in
that branch. The defining subtype keeps the owner and distinguished
adhesion vertex available without any choice of inverses.
-/

namespace HadwigerLean.RootedDensity

universe u v

def TorsoTouchIndex
    {V : Type u} {I : Type v} [Fintype V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    {H : SimpleGraph I} {root : I → S.left}
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root) : Type v :=
  {i : I // ModelTouchesBoundary S M i}

def TorsoFreeIndex
    {V : Type u} {I : Type v} [Fintype V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    {H : SimpleGraph I} {root : I → S.left}
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root) : Type v :=
  {i : I // ¬ ModelTouchesBoundary S M i}

noncomputable def chosenTorsoStar
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (t : TorsoTouchIndex S M) :
    TorsoBranchStarData G S M t.1 :=
  chooseTorsoBranchStar G S H root M hmin t.1 t.2

def TorsoHangerIndex
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N) : Type (max u v) :=
  Σ t : TorsoTouchIndex S M,
    {z : M.branch t.1 //
      ((z.1 : S.left) : V) ∈ S.right ∧
        z ≠ (chosenTorsoStar G S H root M hmin t).center}

def torsoHangerOwner
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (w : TorsoHangerIndex G S H root M hmin) : I :=
  w.1.1

def torsoHangerBoundary
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (w : TorsoHangerIndex G S H root M hmin) : S.left :=
  w.2.1.1

def torsoHangerPiece
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (w : TorsoHangerIndex G S H root M hmin) : Set S.left :=
  Subtype.val '' starPiece
    (chosenTorsoStar G S H root M hmin w.1).forest w.2.1


def TorsoHangerRel
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (w : TorsoHangerIndex G S H root M hmin)
    (j : TorsoFreeIndex S M) : Prop :=
  H.Adj (torsoHangerOwner G S H root M hmin w) j.1 ∧
    ∃ x ∈ torsoHangerPiece G S H root M hmin w,
      ∃ y ∈ M.branch j.1, G.Adj (x : V) (y : V)

theorem torsoHangerRel_total
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (w : TorsoHangerIndex G S H root M hmin) :
    ∃ j : TorsoFreeIndex S M,
      TorsoHangerRel G S H root M hmin w j := by
  obtain ⟨j,hij,hfree,x,hx,y,hy,hxy⟩ :=
    (chosenTorsoStar G S H root M hmin w.1).hanger_witness
      w.2.1 w.2.2.1 w.2.2.2
  have hjFree : ¬ ModelTouchesBoundary S M j := by
    rintro ⟨v,hv,hvS⟩
    exact hfree v hv hvS
  exact ⟨⟨j,hjFree⟩,hij,x,hx,y,hy,hxy⟩

end HadwigerLean.RootedDensity
