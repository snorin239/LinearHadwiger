import HadwigerLean.Graph.RootedDensity.TorsoColoredNearFar

/-! Every colored branch is the union of its assigned atomic pieces. -/

namespace HadwigerLean.RootedDensity

universe u v

theorem mem_torsoColoredBranch_iff_atoms
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
    (Y : Finset I) (q : ↥(Y : Set I) → S.right)
    (N : RootedMinorModel (H.induce (Y : Set I)) (G.induce S.right) q)
    (i : I) (x : V) :
    x ∈ torsoColoredBranch G S H root M hmin P Y q N i ↔
      (∃ a : TorsoNearAtom G S H root M hmin P,
        torsoNearAtomRecipient G S H root M hmin P a = i ∧
          x ∈ torsoNearAtomPiece G S H root M hmin P a) ∨
      (∃ b : TorsoFarAtom G S H root M hmin P,
        torsoFarAtomRecipient G S H root M hmin P b = i ∧
          x ∈ torsoFarAtomPiece G S H root M hmin P Y q N b) := by
  classical
  constructor
  · intro hx
    by_cases ht : ModelTouchesBoundary S M i
    · let t : TorsoTouchIndex S M := ⟨i,ht⟩
      unfold torsoColoredBranch at hx
      simp only [dif_pos ht] at hx
      rcases hx with (hcf | hrest)
      · rcases hcf with hc | hf
        · exact Or.inl ⟨.inl t,rfl,hc⟩
        · exact Or.inr ⟨.inl t,rfl,hf⟩
      · obtain ⟨u,hu⟩ := Set.mem_iUnion.mp hrest
        split_ifs at hu with hown
        · rcases hu with hn | hf
          · exact Or.inl ⟨.inr (.inr (.inl u)),hown,hn⟩
          · exact Or.inr ⟨.inr (.inl u),hown,hf⟩
        · exact False.elim (by simpa using hu)
    · let j : TorsoFreeIndex S M := ⟨i,ht⟩
      rw [colored_free_eq G S H root M hmin P Y q N j] at hx
      rcases hx with hfree | hrest
      · exact Or.inl ⟨.inr (.inl j),rfl,hfree⟩
      · by_cases hj : j ∈ P.color1Right
        · have hIf : (if hk : j ∈ P.color1Right then
              (Subtype.val '' torsoHangerPiece G S H root M hmin
                (P.match1 ⟨j,hk⟩)) ∪ rigidFarBranchImage S Y N i
            else ∅) =
            (Subtype.val '' torsoHangerPiece G S H root M hmin
              (P.match1 ⟨j,hj⟩)) ∪ rigidFarBranchImage S Y N i :=
          dif_pos hj
          rw [hIf] at hrest
          rcases hrest with hn | hf
          · exact Or.inl ⟨.inr (.inr (.inr ⟨j,hj⟩)),rfl,hn⟩
          · exact Or.inr ⟨.inr (.inr ⟨j,hj⟩),rfl,hf⟩
        · have hIf : (if hk : j ∈ P.color1Right then
              (Subtype.val '' torsoHangerPiece G S H root M hmin
                (P.match1 ⟨j,hk⟩)) ∪ rigidFarBranchImage S Y N i
            else ∅) = ∅ := dif_neg hj
          rw [hIf] at hrest
          exact False.elim hrest
  · rintro (⟨a,ha,hx⟩ | ⟨b,hb,hx⟩)
    · rw [← ha]
      exact nearAtom_subset_colored G S H root M hmin P Y q N a hx
    · rw [← hb]
      exact farAtom_subset_colored G S H root M hmin P Y q N b hx

end HadwigerLean.RootedDensity
