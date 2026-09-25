import HadwigerLean.Graph.RootedDensity.TorsoColoredAtoms

/-! A retained near piece can meet a far branch only at its assigned root. -/

namespace HadwigerLean.RootedDensity

universe u v

theorem near_piece_far_label_of_root
    {V : Type u} {I : Type v}
    [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    (H : SimpleGraph I)
    (Y : Finset I) (q : ↥(Y : Set I) → S.right)
    (N : RootedMinorModel (H.induce (Y : Set I)) (G.induce S.right) q)
    (A : Set S.left) (z : S.left)
    (hzRight : (z : V) ∈ S.right)
    (hunique : ∀ a ∈ A, (a : V) ∈ S.right → a = z)
    (ℓ : I) (hℓ : ℓ ∈ Y)
    (hq : q ⟨ℓ,hℓ⟩ = ⟨(z : V), hzRight⟩)
    (k : I) (x : V)
    (hxNear : x ∈ Subtype.val '' A)
    (hxFar : x ∈ rigidFarBranchImage S Y N k) :
    k = ℓ := by
  obtain ⟨a,ha,rfl⟩ := hxNear
  obtain ⟨hk,b,hb,hba⟩ :=
    (mem_rigidFarBranchImage_iff S Y N k _).mp hxFar
  have haRight : (a : V) ∈ S.right := hba ▸ b.2
  have haz : a = z := hunique a ha haRight
  have hbz : b = ⟨(z : V),hzRight⟩ := by
    apply Subtype.ext
    exact hba.trans (congrArg Subtype.val haz)
  have hzFar : q ⟨ℓ,hℓ⟩ ∈ N.branch ⟨k,hk⟩ := by
    rw [hq]
    exact hbz ▸ hb
  by_contra hne
  have hneq : (⟨ℓ,hℓ⟩ : ↥(Y : Set I)) ≠ ⟨k,hk⟩ := by
    intro heq
    exact hne (congrArg Subtype.val heq).symm
  exact (N.other_root_not_mem hneq.symm) hzFar

theorem nearFarAtom_recipient_eq_of_overlap
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
    (htwoRoot : ∀ u : ↥P.color2Left,
      ∃ hi : (P.match2 u).1 ∈ Y,
        q ⟨(P.match2 u).1,hi⟩ =
          torsoHangerAdhesion G S H root M hmin u.1)
    (honeRoot : ∀ j : ↥P.color1Right,
      ∃ hi : j.1.1 ∈ Y,
        q ⟨j.1.1,hi⟩ =
          torsoHangerAdhesion G S H root M hmin (P.match1 j))
    (a : TorsoNearAtom G S H root M hmin P)
    (b : TorsoFarAtom G S H root M hmin P)
    (x : V)
    (hxa : x ∈ torsoNearAtomPiece G S H root M hmin P a)
    (hxb : x ∈ torsoFarAtomPiece G S H root M hmin P Y q N b) :
    torsoNearAtomRecipient G S H root M hmin P a =
      torsoFarAtomRecipient G S H root M hmin P b := by
  classical
  rcases a with t | a
  · obtain ⟨htY,hqt⟩ := hcenterRoot t
    have hlabel := near_piece_far_label_of_root G S H Y q N
      (torsoCenterPiece G S H root M hmin t)
      (torsoCenterBoundary G S H root M hmin t)
      (chosenTorsoStar G S H root M hmin t).center_boundary
      (by
        intro z hz hzR
        exact torsoCenterPiece_unique_adhesion G S H root M hmin t hz hzR)
      t.1 htY hqt
      (torsoFarAtomLabel G S H root M hmin P b) x hxa hxb
    exact (torsoFarAtom_recipient_eq_of_label_eq G S H root M hmin P
      (.inl t) b hlabel.symm)
  · rcases a with j | a
    · have hright := rigidFarBranchImage_subset_right S Y N
        (torsoFarAtomLabel G S H root M hmin P b) hxb
      exact False.elim ((Set.disjoint_left.mp
        (torsoFreePiece_avoids_right G S H root M j)) hxa hright)
    · rcases a with u | j
      · obtain ⟨huY,hqu⟩ := htwoRoot u
        have hlabel := near_piece_far_label_of_root G S H Y q N
          (torsoHangerPiece G S H root M hmin u.1)
          (torsoHangerBoundary G S H root M hmin u.1)
          u.1.2.2.1
          (by
            intro z hz hzR
            exact torsoHangerPiece_unique_adhesion
              G S H root M hmin u.1 hz hzR)
          (P.match2 u).1 huY hqu
          (torsoFarAtomLabel G S H root M hmin P b) x hxa hxb
        exact torsoFarAtom_recipient_eq_of_label_eq G S H root M hmin P
          (.inr (.inl u)) b hlabel.symm
      · obtain ⟨hjY,hqj⟩ := honeRoot j
        have hlabel := near_piece_far_label_of_root G S H Y q N
          (torsoHangerPiece G S H root M hmin (P.match1 j))
          (torsoHangerBoundary G S H root M hmin (P.match1 j))
          (P.match1 j).2.2.1
          (by
            intro z hz hzR
            exact torsoHangerPiece_unique_adhesion
              G S H root M hmin (P.match1 j) hz hzR)
          j.1.1 hjY hqj
          (torsoFarAtomLabel G S H root M hmin P b) x hxa hxb
        exact torsoFarAtom_recipient_eq_of_label_eq G S H root M hmin P
          (.inr (.inr j)) b hlabel.symm

theorem nearFarAtoms_disjoint_of_recipient_ne
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
    (htwoRoot : ∀ u : ↥P.color2Left,
      ∃ hi : (P.match2 u).1 ∈ Y,
        q ⟨(P.match2 u).1,hi⟩ =
          torsoHangerAdhesion G S H root M hmin u.1)
    (honeRoot : ∀ j : ↥P.color1Right,
      ∃ hi : j.1.1 ∈ Y,
        q ⟨j.1.1,hi⟩ =
          torsoHangerAdhesion G S H root M hmin (P.match1 j))
    (a : TorsoNearAtom G S H root M hmin P)
    (b : TorsoFarAtom G S H root M hmin P)
    (hrec : torsoNearAtomRecipient G S H root M hmin P a ≠
      torsoFarAtomRecipient G S H root M hmin P b) :
    Disjoint (torsoNearAtomPiece G S H root M hmin P a)
      (torsoFarAtomPiece G S H root M hmin P Y q N b) := by
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  exact hrec (nearFarAtom_recipient_eq_of_overlap G S H root M hmin P
    Y q N hcenterRoot htwoRoot honeRoot a b x hxa hxb)
end HadwigerLean.RootedDensity


