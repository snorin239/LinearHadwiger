import HadwigerLean.Graph.RootedDensity.TorsoColoredAtoms
import HadwigerLean.Graph.RootedDensity.TorsoPieceDisjoint

/-! Near-atom disjointness between distinct colored recipients. -/

namespace HadwigerLean.RootedDensity

universe u v

private theorem disjoint_subtype_images
    {V : Type u} {S : Set V} {A B : Set S}
    (h : Disjoint A B) :
    Disjoint (Subtype.val '' A : Set V) (Subtype.val '' B) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,heq⟩ := hy
  have hab : a = b := Subtype.val_injective heq.symm
  subst b
  exact (Set.disjoint_left.mp h) ha hb

/-- Atomic near pieces assigned to different final branches are disjoint.
The only same-origin cases are separate forest components of one touching
torso branch; the color-1 and color-2 matching endpoints cannot name the
same hanging component. -/
theorem nearAtoms_disjoint_of_recipient_ne
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G) [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N' : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N')
    [DecidableEq (TorsoHangerIndex G S H root M hmin)]
    [DecidableEq (TorsoFreeIndex S M)]
    (P : TwoColorMatching (TorsoHangerRel G S H root M hmin))
    (a b : TorsoNearAtom G S H root M hmin P)
    (hrec : torsoNearAtomRecipient G S H root M hmin P a ≠
      torsoNearAtomRecipient G S H root M hmin P b) :
    Disjoint (torsoNearAtomPiece G S H root M hmin P a)
      (torsoNearAtomPiece G S H root M hmin P b) := by
  classical
  have hbranch (i j : I) (A B : Set S.left)
      (hij : i ≠ j) (hA : A ⊆ M.branch i) (hB : B ⊆ M.branch j) :
      Disjoint (Subtype.val '' A : Set V) (Subtype.val '' B) :=
    disjoint_subtype_images (disjoint_of_branch_subsets M hij hA hB)
  have htouchfree (t : TorsoTouchIndex S M) (j : TorsoFreeIndex S M) :
      t.1 ≠ j.1 := by
    intro heq
    exact j.2 (heq ▸ t.2)
  have hcenterfree (t : TorsoTouchIndex S M) (j : TorsoFreeIndex S M) :
      Disjoint (Subtype.val '' torsoCenterPiece G S H root M hmin t : Set V)
        (torsoFreePiece G S H root M j) := by
    change Disjoint (Subtype.val '' torsoCenterPiece G S H root M hmin t : Set V)
      (Subtype.val '' M.branch j.1 : Set V)
    exact hbranch t.1 j.1 _ _ (htouchfree t j)
      (torsoCenterPiece_subset_branch G S H root M hmin t) Set.Subset.rfl
  have hfreehanger (j : TorsoFreeIndex S M)
      (w : TorsoHangerIndex G S H root M hmin) :
      Disjoint (torsoFreePiece G S H root M j)
        (Subtype.val '' torsoHangerPiece G S H root M hmin w : Set V) := by
    change Disjoint (Subtype.val '' M.branch j.1 : Set V)
      (Subtype.val '' torsoHangerPiece G S H root M hmin w : Set V)
    exact hbranch j.1 (torsoHangerOwner G S H root M hmin w) _ _
      (htouchfree w.1 j).symm Set.Subset.rfl
      (torsoHangerPiece_subset_branch G S H root M hmin w)
  have hfreefree (j k : TorsoFreeIndex S M) (hjk : j.1 ≠ k.1) :
      Disjoint (torsoFreePiece G S H root M j)
        (torsoFreePiece G S H root M k) := by
    change Disjoint (Subtype.val '' M.branch j.1 : Set V)
      (Subtype.val '' M.branch k.1 : Set V)
    exact hbranch j.1 k.1 _ _ hjk Set.Subset.rfl Set.Subset.rfl
  have hcenterhanger (t : TorsoTouchIndex S M)
      (w : TorsoHangerIndex G S H root M hmin) :
      Disjoint (Subtype.val '' torsoCenterPiece G S H root M hmin t : Set V)
        (Subtype.val '' torsoHangerPiece G S H root M hmin w : Set V) :=
    disjoint_subtype_images
      (torsoCenterHanger_disjoint G S H root M hmin t w)
  have hhangerhanger {w z : TorsoHangerIndex G S H root M hmin}
      (hwz : w ≠ z) :
      Disjoint (Subtype.val '' torsoHangerPiece G S H root M hmin w : Set V)
        (Subtype.val '' torsoHangerPiece G S H root M hmin z : Set V) :=
    disjoint_subtype_images
      (torsoHangerPieces_disjoint G S H root M hmin hwz)
  rcases a with t | a
  · rcases b with u | b
    · have htu : t ≠ u := by
        intro heq
        exact hrec (congrArg Subtype.val heq)
      simpa [torsoNearAtomPiece] using
        disjoint_subtype_images
          (torsoCenterPieces_disjoint G S H root M hmin htu)
    · rcases b with j | b
      · simpa [torsoNearAtomPiece] using hcenterfree t j
      · rcases b with z | j
        · simpa [torsoNearAtomPiece] using hcenterhanger t z.1
        · simpa [torsoNearAtomPiece] using hcenterhanger t (P.match1 j)
  · rcases a with j | a
    · rcases b with t | b
      · simpa [torsoNearAtomPiece] using (hcenterfree t j).symm
      · rcases b with k | b
        · have hjk : j.1 ≠ k.1 := hrec
          simpa [torsoNearAtomPiece] using hfreefree j k hjk
        · rcases b with z | k
          · simpa [torsoNearAtomPiece] using hfreehanger j z.1
          · simpa [torsoNearAtomPiece] using hfreehanger j (P.match1 k)
    · rcases a with z | j
      · rcases b with t | b
        · simpa [torsoNearAtomPiece] using (hcenterhanger t z.1).symm
        · rcases b with k | b
          · simpa [torsoNearAtomPiece] using (hfreehanger k z.1).symm
          · rcases b with w | k
            · have hzw : z.1 ≠ w.1 := by
                intro heq
                exact hrec (congrArg
                  (torsoHangerOwner G S H root M hmin) heq)
              simpa [torsoNearAtomPiece] using hhangerhanger hzw
            · have hzw : z.1 ≠ P.match1 k := by
                intro heq
                exact (P.match1_avoid_color2 k) (heq ▸ z.2)
              simpa [torsoNearAtomPiece] using hhangerhanger hzw
      · rcases b with t | b
        · simpa [torsoNearAtomPiece] using
            (hcenterhanger t (P.match1 j)).symm
        · rcases b with k | b
          · simpa [torsoNearAtomPiece] using
              (hfreehanger k (P.match1 j)).symm
          · rcases b with z | k
            · have hjz : P.match1 j ≠ z.1 := by
                intro heq
                exact (P.match1_avoid_color2 j) (heq.symm ▸ z.2)
              simpa [torsoNearAtomPiece] using hhangerhanger hjz
            · have hjk : j ≠ k := by
                intro heq
                exact hrec (congrArg (fun z : ↥P.color1Right => (z.1.1 : I)) heq)
              have hmatch : P.match1 j ≠ P.match1 k :=
                P.match1.injective.ne hjk
              simpa [torsoNearAtomPiece] using hhangerhanger hmatch

end HadwigerLean.RootedDensity
