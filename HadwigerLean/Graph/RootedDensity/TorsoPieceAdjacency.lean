import HadwigerLean.Graph.RootedDensity.TorsoPieceDisjoint
import HadwigerLean.Graph.RootedDensity.RigidTruncation
import Mathlib.Tactic

/-!
# Real torso adjacencies and their star-piece locations

An edge to a boundary-free branch is real. Its endpoint in a touching
branch belongs either to the retained center piece or to one of that
branch's indexed hangers. This is the exact adjacency dichotomy used
by colored reverse gluing.
-/

namespace HadwigerLean.RootedDensity

universe u v

theorem torso_free_free_edge_real
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (j k : TorsoFreeIndex S M)
    (hjk : H.Adj j.1 k.1) :
    ∃ x ∈ M.branch j.1, ∃ y ∈ M.branch k.1,
      G.Adj (x : V) (y : V) := by
  rcases torso_model_edge_real_or_boundary G S M hjk with
    hreal | ⟨x,hx,y,hy,hxS,_⟩
  · exact hreal
  · exact (j.2 ⟨x,hx,hxS⟩).elim

theorem torso_touch_free_edge_center_or_hanger
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (t : TorsoTouchIndex S M) (j : TorsoFreeIndex S M)
    (hij : H.Adj t.1 j.1) :
    (∃ x ∈ torsoCenterPiece G S H root M hmin t,
      ∃ y ∈ M.branch j.1, G.Adj (x : V) (y : V)) ∨
    (∃ w : TorsoHangerIndex G S H root M hmin,
      torsoHangerOwner G S H root M hmin w = t.1 ∧
      TorsoHangerRel G S H root M hmin w j) := by
  obtain ⟨x,hx,y,hy,hxy⟩ :=
    (torso_model_edge_real_or_boundary G S M hij).resolve_right
      (by
        rintro ⟨a,ha,b,hb,_,hbS⟩
        exact j.2 ⟨b,hb,hbS⟩)
  rcases torsoTouchBranch_piece_cover G S H root M hmin t hx with
    hcenter | ⟨w,howner,hpiece⟩
  · exact Or.inl ⟨x,hcenter,y,hy,hxy⟩
  · exact Or.inr ⟨w,howner,by
      rw [howner]
      exact hij,
      x,hpiece,y,hy,hxy⟩

end HadwigerLean.RootedDensity
