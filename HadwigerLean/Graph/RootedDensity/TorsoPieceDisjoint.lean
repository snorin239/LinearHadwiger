import HadwigerLean.Graph.RootedDensity.TorsoPiecePartition
import Mathlib.Tactic

/-!
# Disjointness of selected center and hanger pieces

The forest components are disjoint within a touching branch; the
original torso model separates components owned by different branches.
-/

namespace HadwigerLean.RootedDensity

universe u v

theorem disjoint_of_branch_subsets
    {V : Type u} {I : Type v}
    {K : SimpleGraph V} {H : SimpleGraph I} {root : I → V}
    (M : RootedMinorModel H K root)
    {i j : I} (hij : i ≠ j)
    {A B : Set V} (hA : A ⊆ M.branch i)
    (hB : B ⊆ M.branch j) :
    Disjoint A B := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact (Set.disjoint_left.mp (M.disjoint hij))
    (hA hx) (hB hy)

theorem image_starPieces_disjoint
    {V : Type u} (S : Set V) (F : SimpleGraph S)
    (Z : Set S)
    (hUnique : ∀ v, ∃! z, z ∈ Z ∧ F.Reachable v z)
    {z w : S} (hz : z ∈ Z) (hw : w ∈ Z)
    (hzw : z ≠ w) :
    Disjoint
      (Subtype.val '' starPiece F z : Set V)
      (Subtype.val '' starPiece F w : Set V) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,heq⟩ := hy
  have hab : a = b := Subtype.ext heq.symm
  subst b
  exact (Set.disjoint_left.mp
    (starPiece_pairwise_disjoint F Z hUnique hz hw hzw))
      ha hb

theorem torsoCenterPieces_disjoint
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    {t u : TorsoTouchIndex S M} (htu : t ≠ u) :
    Disjoint (torsoCenterPiece G S H root M hmin t)
      (torsoCenterPiece G S H root M hmin u) := by
  have hlabel : t.1 ≠ u.1 := by
    intro heq
    exact htu (Subtype.ext heq)
  exact disjoint_of_branch_subsets M hlabel
    (torsoCenterPiece_subset_branch G S H root M hmin t)
    (torsoCenterPiece_subset_branch G S H root M hmin u)

theorem torsoCenterHanger_disjoint
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
    Disjoint (torsoCenterPiece G S H root M hmin t)
      (torsoHangerPiece G S H root M hmin w) := by
  by_cases htw : t = w.1
  · subst t
    let A := chosenTorsoStar G S H root M hmin w.1
    exact image_starPieces_disjoint (M.branch w.1.1) A.forest
      {z : M.branch w.1.1 | ((z.1 : S.left) : V) ∈ S.right}
      A.unique_boundary A.center_boundary w.2.2.1
      (Ne.symm w.2.2.2)
  · have hlabel : t.1 ≠ w.1.1 := by
      intro heq
      exact htw (Subtype.ext heq)
    exact disjoint_of_branch_subsets M hlabel
      (torsoCenterPiece_subset_branch G S H root M hmin t)
      (torsoHangerPiece_subset_branch G S H root M hmin w)

theorem torsoHangerPieces_disjoint
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    {a b : TorsoHangerIndex G S H root M hmin}
    (hab : a ≠ b) :
    Disjoint (torsoHangerPiece G S H root M hmin a)
      (torsoHangerPiece G S H root M hmin b) := by
  rcases a with ⟨ta,za⟩
  rcases b with ⟨tb,zb⟩
  by_cases ht : ta = tb
  · subst tb
    have hzw : za.1 ≠ zb.1 := by
      intro heq
      have hzz : za = zb := Subtype.ext heq
      exact hab (congrArg (Sigma.mk ta) hzz)
    let A := chosenTorsoStar G S H root M hmin ta
    exact image_starPieces_disjoint (M.branch ta.1) A.forest
      {z : M.branch ta.1 | ((z.1 : S.left) : V) ∈ S.right}
      A.unique_boundary za.2.1 zb.2.1 hzw
  · have hlabel : ta.1 ≠ tb.1 := by
      intro heq
      exact ht (Subtype.ext heq)
    exact disjoint_of_branch_subsets M hlabel
      (torsoHangerPiece_subset_branch G S H root M hmin ⟨ta,za⟩)
      (torsoHangerPiece_subset_branch G S H root M hmin ⟨tb,zb⟩)

end HadwigerLean.RootedDensity
