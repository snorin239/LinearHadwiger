import HadwigerLean.Graph.RootedDensity.TorsoColoredBranch

/-! Connectivity of every colored reverse-glue branch. -/

namespace HadwigerLean.RootedDensity

universe u v

theorem torsoColoredBranch_connected
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N' : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N')
    [DecidableEq (TorsoHangerIndex G S H root M hmin)]
    [DecidableEq (TorsoFreeIndex S M)]
    (P : TwoColorMatching (TorsoHangerRel G S H root M hmin))
    (Y : Finset I) (q : ↥(Y : Set I) → S.right)
    (N : RootedMinorModel (H.induce (Y : Set I)) (G.induce S.right) q)
    (hcenterRoot : ∀ t : TorsoTouchIndex S M,
      ∃ hi : t.1 ∈ Y,
        q ⟨t.1,hi⟩ = torsoCenterAdhesion G S H root M hmin t)
    (htwoRoot : ∀ u : ↥P.color2Left,
      ∃ hi : (P.match2 u).1 ∈ Y,
        q ⟨(P.match2 u).1,hi⟩ =
          torsoHangerAdhesion G S H root M hmin u.1)
    (honeRoot : ∀ j : ↥P.color1Right,
      ∃ hi : j.1.1 ∈ Y,
        q ⟨j.1.1,hi⟩ =
          torsoHangerAdhesion G S H root M hmin (P.match1 j))
    (i : I) :
    (G.induce (torsoColoredBranch G S H root M hmin P Y q N i)).Connected := by
  classical
  by_cases ht : ModelTouchesBoundary S M i
  · let t : TorsoTouchIndex S M := ⟨i,ht⟩
    let C : Set V := Subtype.val '' torsoCenterPiece G S H root M hmin t
    let F : Set V := rigidFarBranchImage S Y N i
    let A : Set V := C ∪ F
    obtain ⟨hi,hci⟩ := hcenterRoot t
    have hC : (G.induce C).Connected :=
      torsoCenterPiece_connected_real G S H root M hmin t
    have hF : (G.induce F).Connected :=
      rigidFarBranchImage_connected G S Y N ⟨i,hi⟩
    have hA : (G.induce A).Connected := by
      apply G.induce_union_connected hC.preconnected hF.preconnected
      refine ⟨(torsoCenterBoundary G S H root M hmin t : V), ?_, ?_⟩
      · exact ⟨torsoCenterBoundary G S H root M hmin t,
          torsoCenterBoundary_mem_piece G S H root M hmin t, rfl⟩
      · have hr := rigidFarBranchImage_root_mem S Y N ⟨i,hi⟩
        have hciV := congrArg (fun z : S.right => (z : V)) hci
        change (q ⟨i,hi⟩ : V) =
          (torsoCenterBoundary G S H root M hmin t : V) at hciV
        simpa only [hciV] using hr
    let U₂i := {u : ↥P.color2Left //
      torsoHangerOwner G S H root M hmin u.1 = i}
    let attach : U₂i → Set V := fun u =>
      (Subtype.val '' torsoHangerPiece G S H root M hmin u.1.1) ∪
        rigidFarBranchImage S Y N (P.match2 u.1).1
    have hAttach : ∀ u : U₂i, (G.induce (attach u)).Connected := by
      intro u
      obtain ⟨hj,hju⟩ := htwoRoot u.1
      have hHang := torsoHangerPiece_connected_real
        G S H root M hmin u.1.1
      have hFar := rigidFarBranchImage_connected G S Y N
        ⟨(P.match2 u.1).1,hj⟩
      apply G.induce_union_connected hHang.preconnected hFar.preconnected
      refine ⟨(torsoHangerBoundary G S H root M hmin u.1.1 : V), ?_, ?_⟩
      · exact ⟨torsoHangerBoundary G S H root M hmin u.1.1,
          torsoHangerBoundary_mem_piece G S H root M hmin u.1.1, rfl⟩
      · have hr := rigidFarBranchImage_root_mem S Y N
          ⟨(P.match2 u.1).1,hj⟩
        have hjuV := congrArg (fun z : S.right => (z : V)) hju
        change (q ⟨(P.match2 u.1).1,hj⟩ : V) =
          (torsoHangerBoundary G S H root M hmin u.1.1 : V) at hjuV
        simpa only [hjuV] using hr
    have hAnchor : ∀ u : U₂i, ∃ a ∈ A, ∃ p ∈ attach u, G.Adj a p := by
      intro u
      obtain ⟨hj,_⟩ := htwoRoot u.1
      have hrel := (P.match2_rel u.1).1
      have hown : torsoHangerOwner G S H root M hmin u.1.1 = i := u.2
      rw [hown] at hrel
      obtain ⟨a,ha,p,hp,hap⟩ := rigidFarBranchImage_edge
        S Y N ⟨i,hi⟩ ⟨(P.match2 u.1).1,hj⟩ hrel
      exact ⟨a,Or.inr ha,p,Or.inr hp,hap⟩
    have hConn := connected_induce_anchor_union_iUnion G A attach
      hA hAttach hAnchor
    have hset : torsoColoredBranch G S H root M hmin P Y q N i =
        A ∪ ⋃ u : U₂i, attach u := by
      unfold torsoColoredBranch
      simp only [dif_pos ht]
      ext x
      simp only [Set.mem_union, Set.mem_iUnion]
      constructor
      · rintro (hx | hx)
        · exact Or.inl hx
        · obtain ⟨u,hu⟩ := hx
          split_ifs at hu with hown
          · exact Or.inr ⟨⟨u,hown⟩,hu⟩
          · exact False.elim (by simpa using hu)
      · rintro (hx | ⟨u,hu⟩)
        · exact Or.inl hx
        · exact Or.inr ⟨u.1,by simpa [attach, u.2] using hu⟩
    rw [hset]
    exact hConn
  · let j : TorsoFreeIndex S M := ⟨i,ht⟩
    have hfreeEq : torsoColoredBranch G S H root M hmin P Y q N i =
        torsoFreePiece G S H root M j ∪
          (if hj : j ∈ P.color1Right then
            (Subtype.val '' torsoHangerPiece G S H root M hmin
              (P.match1 ⟨j,hj⟩)) ∪ rigidFarBranchImage S Y N i
          else ∅) := by
      unfold torsoColoredBranch
      simp only [ht, dite_false]
      rfl
    rw [hfreeEq]
    by_cases hj : j ∈ P.color1Right
    · have hIf : (if hk : j ∈ P.color1Right then
          (Subtype.val '' torsoHangerPiece G S H root M hmin (P.match1 ⟨j,hk⟩)) ∪
            rigidFarBranchImage S Y N i else ∅) =
            (Subtype.val '' torsoHangerPiece G S H root M hmin (P.match1 ⟨j,hj⟩)) ∪
              rigidFarBranchImage S Y N i := by
          exact dif_pos hj
      rw [hIf]
      let w : ↥P.color1Right := ⟨j,hj⟩
      obtain ⟨hi,hji⟩ := honeRoot w
      have hNear := torsoFreePiece_connected_real G S H root M j
      have hHang := torsoHangerPiece_connected_real G S H root M hmin
        (P.match1 w)
      have hFar := rigidFarBranchImage_connected G S Y N ⟨i,hi⟩
      have hrel := (P.match1_rel w).2
      obtain ⟨x,hx,y,hy,hxy⟩ := hrel
      have hWitness : ∃ a ∈ torsoFreePiece G S H root M j,
          ∃ b ∈ Subtype.val '' torsoHangerPiece G S H root M hmin (P.match1 w),
            G.Adj a b :=
        ⟨y.1,⟨y,hy,rfl⟩,x.1,⟨x,hx,rfl⟩,hxy.symm⟩
      have hRoot : ((Subtype.val '' torsoHangerPiece G S H root M hmin
          (P.match1 w)) ∩ rigidFarBranchImage S Y N i).Nonempty := by
        refine ⟨(torsoHangerBoundary G S H root M hmin (P.match1 w) : V),
          ?_, ?_⟩
        · exact ⟨torsoHangerBoundary G S H root M hmin (P.match1 w),
            torsoHangerBoundary_mem_piece G S H root M hmin (P.match1 w),rfl⟩
        · have hr := rigidFarBranchImage_root_mem S Y N ⟨i,hi⟩
          have hjiV := congrArg (fun z : S.right => (z : V)) hji
          change (q ⟨i,hi⟩ : V) =
            (torsoHangerBoundary G S H root M hmin (P.match1 w) : V) at hjiV
          simpa only [hjiV] using hr
      have hconn := connected_induce_color1_attachment G
        (torsoFreePiece G S H root M j)
        (Subtype.val '' torsoHangerPiece G S H root M hmin (P.match1 w))
        (rigidFarBranchImage S Y N i)
        hNear hHang hFar hWitness hRoot
      rw [← Set.union_assoc]
      exact hconn
    · have hIf : (if hk : j ∈ P.color1Right then
          (Subtype.val '' torsoHangerPiece G S H root M hmin (P.match1 ⟨j,hk⟩)) ∪
            rigidFarBranchImage S Y N i else ∅) = ∅ := by
        exact dif_neg hj
      rw [hIf, Set.union_empty]
      exact torsoFreePiece_connected_real G S H root M j

end HadwigerLean.RootedDensity


























