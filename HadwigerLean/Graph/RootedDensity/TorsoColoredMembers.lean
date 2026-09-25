import HadwigerLean.Graph.RootedDensity.TorsoColoredConnected

/-! Membership of the pieces retained by the colored torso lift. -/

namespace HadwigerLean.RootedDensity

universe u v

variable {V : Type u} {I : Type v}
variable [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (G : SimpleGraph V) (S : VertexSeparation G) [Fintype S.left]
variable (H : SimpleGraph I) (root : I → S.left)
variable (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
variable (hmin : ∀ N' : RootedMinorModel H (Linkedness.torsoGraph G S) root,
  rootedModelOrder M ≤ rootedModelOrder N')
variable [DecidableEq (TorsoHangerIndex G S H root M hmin)]
variable [DecidableEq (TorsoFreeIndex S M)]
variable (P : TwoColorMatching (TorsoHangerRel G S H root M hmin))
variable (Y : Finset I) (q : ↥(Y : Set I) → S.right)
variable (N : RootedMinorModel (H.induce (Y : Set I)) (G.induce S.right) q)

theorem colored_free_eq (j : TorsoFreeIndex S M) :
    torsoColoredBranch G S H root M hmin P Y q N j.1 =
      torsoFreePiece G S H root M j ∪
        (if hj : j ∈ P.color1Right then
          (Subtype.val '' torsoHangerPiece G S H root M hmin
            (P.match1 ⟨j,hj⟩)) ∪ rigidFarBranchImage S Y N j.1
        else ∅) := by
  unfold torsoColoredBranch
  simp only [j.2, dite_false]
  rfl
theorem center_subset_colored (t : TorsoTouchIndex S M) :
    Subtype.val '' torsoCenterPiece G S H root M hmin t ⊆
      torsoColoredBranch G S H root M hmin P Y q N t.1 := by
  intro x hx
  unfold torsoColoredBranch
  simp only [dif_pos t.2]
  exact Or.inl (Or.inl hx)

theorem far_touch_subset_colored (t : TorsoTouchIndex S M) :
    rigidFarBranchImage S Y N t.1 ⊆
      torsoColoredBranch G S H root M hmin P Y q N t.1 := by
  intro x hx
  unfold torsoColoredBranch
  simp only [dif_pos t.2]
  exact Or.inl (Or.inr hx)

theorem hanger2_subset_colored (u : ↥P.color2Left) :
    Subtype.val '' torsoHangerPiece G S H root M hmin u.1 ⊆
      torsoColoredBranch G S H root M hmin P Y q N
        (torsoHangerOwner G S H root M hmin u.1) := by
  intro x hx
  have ht : ModelTouchesBoundary S M
      (torsoHangerOwner G S H root M hmin u.1) := u.1.1.2
  unfold torsoColoredBranch
  simp only [dif_pos ht]
  exact Or.inr (Set.mem_iUnion.mpr ⟨u, by simp only [dif_pos rfl]; exact Or.inl hx⟩)

theorem far2_subset_colored (u : ↥P.color2Left) :
    rigidFarBranchImage S Y N (P.match2 u).1 ⊆
      torsoColoredBranch G S H root M hmin P Y q N
        (torsoHangerOwner G S H root M hmin u.1) := by
  intro x hx
  have ht : ModelTouchesBoundary S M
      (torsoHangerOwner G S H root M hmin u.1) := u.1.1.2
  unfold torsoColoredBranch
  simp only [dif_pos ht]
  exact Or.inr (Set.mem_iUnion.mpr ⟨u, by simp only [dif_pos rfl]; exact Or.inr hx⟩)

theorem free_subset_colored (j : TorsoFreeIndex S M) :
    torsoFreePiece G S H root M j ⊆
      torsoColoredBranch G S H root M hmin P Y q N j.1 := by
  intro x hx
  unfold torsoColoredBranch
  simp only [dif_neg j.2]
  exact Or.inl hx

theorem hanger1_subset_colored (j : ↥P.color1Right) :
    Subtype.val '' torsoHangerPiece G S H root M hmin (P.match1 j) ⊆
      torsoColoredBranch G S H root M hmin P Y q N j.1.1 := by
  intro x hx
  rw [colored_free_eq G S H root M hmin P Y q N j.1]
  right
  have hIf : (if hj : j.1 ∈ P.color1Right then
        (Subtype.val '' torsoHangerPiece G S H root M hmin
          (P.match1 ⟨j.1,hj⟩)) ∪ rigidFarBranchImage S Y N j.1.1
      else ∅) =
      (Subtype.val '' torsoHangerPiece G S H root M hmin (P.match1 j)) ∪
        rigidFarBranchImage S Y N j.1.1 := dif_pos j.2
  rw [hIf]
  exact Or.inl hx

theorem far1_subset_colored (j : ↥P.color1Right) :
    rigidFarBranchImage S Y N j.1.1 ⊆
      torsoColoredBranch G S H root M hmin P Y q N j.1.1 := by
  intro x hx
  rw [colored_free_eq G S H root M hmin P Y q N j.1]
  right
  have hIf : (if hj : j.1 ∈ P.color1Right then
        (Subtype.val '' torsoHangerPiece G S H root M hmin
          (P.match1 ⟨j.1,hj⟩)) ∪ rigidFarBranchImage S Y N j.1.1
      else ∅) =
      (Subtype.val '' torsoHangerPiece G S H root M hmin (P.match1 j)) ∪
        rigidFarBranchImage S Y N j.1.1 := dif_pos j.2
  rw [hIf]
  exact Or.inr hx

end HadwigerLean.RootedDensity




