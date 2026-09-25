import HadwigerLean.Graph.RootedDensity.TorsoColoredMembers

/-! The colored reverse-glue branches retain every required target edge. -/

namespace HadwigerLean.RootedDensity

universe u v

theorem torsoColored_touch_free_edge
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
    (hcenterRoot : ∀ t : TorsoTouchIndex S M,
      ∃ hi : t.1 ∈ Y,
        q ⟨t.1,hi⟩ = torsoCenterAdhesion G S H root M hmin t)
    (honeRoot : ∀ j : ↥P.color1Right,
      ∃ hi : j.1.1 ∈ Y,
        q ⟨j.1.1,hi⟩ =
          torsoHangerAdhesion G S H root M hmin (P.match1 j))
    (t : TorsoTouchIndex S M) (j : TorsoFreeIndex S M)
    (htj : H.Adj t.1 j.1) :
    ∃ x ∈ torsoColoredBranch G S H root M hmin P Y q N t.1,
      ∃ y ∈ torsoColoredBranch G S H root M hmin P Y q N j.1,
        G.Adj x y := by
  classical
  rcases torso_touch_free_edge_center_or_hanger G S H root M hmin t j htj with
    ⟨x,hx,y,hy,hxy⟩ | ⟨w,hw,hrel⟩
  · exact ⟨x.1,
      center_subset_colored G S H root M hmin P Y q N t
        ⟨x,hx,rfl⟩,
      y.1,
      free_subset_colored G S H root M hmin P Y q N j
        ⟨y,hy,rfl⟩,hxy⟩
  · by_cases htwo : w ∈ P.color2Left
    · obtain ⟨x,hx,y,hy,hxy⟩ := hrel.2
      let u : ↥P.color2Left := ⟨w,htwo⟩
      have hxi := hanger2_subset_colored G S H root M hmin P Y q N u
        ⟨x,hx,rfl⟩
      rw [hw] at hxi
      exact ⟨x.1,hxi,y.1,
        free_subset_colored G S H root M hmin P Y q N j
          ⟨y,hy,rfl⟩,hxy⟩
    · have hj : j ∈ P.color1Right := P.cover w htwo j hrel
      let j₁ : ↥P.color1Right := ⟨j,hj⟩
      obtain ⟨hi,_⟩ := hcenterRoot t
      obtain ⟨hk,_⟩ := honeRoot j₁
      obtain ⟨x,hx,y,hy,hxy⟩ := rigidFarBranchImage_edge
        S Y N ⟨t.1,hi⟩ ⟨j.1,hk⟩ htj
      exact ⟨x,far_touch_subset_colored G S H root M hmin P Y q N t hx,
        y,far1_subset_colored G S H root M hmin P Y q N j₁ hy,hxy⟩

theorem torsoColoredBranch_adjacent
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
    (hcenterRoot : ∀ t : TorsoTouchIndex S M,
      ∃ hi : t.1 ∈ Y,
        q ⟨t.1,hi⟩ = torsoCenterAdhesion G S H root M hmin t)
    (honeRoot : ∀ j : ↥P.color1Right,
      ∃ hi : j.1.1 ∈ Y,
        q ⟨j.1.1,hi⟩ =
          torsoHangerAdhesion G S H root M hmin (P.match1 j))
    {i j : I} (hij : H.Adj i j) :
    ∃ x ∈ torsoColoredBranch G S H root M hmin P Y q N i,
      ∃ y ∈ torsoColoredBranch G S H root M hmin P Y q N j,
        G.Adj x y := by
  classical
  by_cases hi : ModelTouchesBoundary S M i
  · let t : TorsoTouchIndex S M := ⟨i,hi⟩
    by_cases hj : ModelTouchesBoundary S M j
    · let u : TorsoTouchIndex S M := ⟨j,hj⟩
      obtain ⟨hiY,_⟩ := hcenterRoot t
      obtain ⟨hjY,_⟩ := hcenterRoot u
      obtain ⟨x,hx,y,hy,hxy⟩ := rigidFarBranchImage_edge
        S Y N ⟨i,hiY⟩ ⟨j,hjY⟩ hij
      exact ⟨x,far_touch_subset_colored G S H root M hmin P Y q N t hx,
        y,far_touch_subset_colored G S H root M hmin P Y q N u hy,hxy⟩
    · exact torsoColored_touch_free_edge G S H root M hmin P Y q N
        hcenterRoot honeRoot t ⟨j,hj⟩ hij
  · let a : TorsoFreeIndex S M := ⟨i,hi⟩
    by_cases hj : ModelTouchesBoundary S M j
    · obtain ⟨x,hx,y,hy,hxy⟩ :=
        torsoColored_touch_free_edge G S H root M hmin P Y q N
          hcenterRoot honeRoot ⟨j,hj⟩ a hij.symm
      exact ⟨y,hy,x,hx,hxy.symm⟩
    · let b : TorsoFreeIndex S M := ⟨j,hj⟩
      obtain ⟨x,hx,y,hy,hxy⟩ :=
        torso_free_free_edge_real G S H root M a b hij
      exact ⟨x.1,
        free_subset_colored G S H root M hmin P Y q N a
          ⟨x,hx,rfl⟩,
        y.1,
        free_subset_colored G S H root M hmin P Y q N b
          ⟨y,hy,rfl⟩,hxy⟩

end HadwigerLean.RootedDensity
