import HadwigerLean.Graph.RootedDensity.TorsoColoredFarControl

/-! Atomic near and far pieces of the colored torso lift. -/

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

def TorsoNearAtom :=
  TorsoTouchIndex S M ⊕
    (TorsoFreeIndex S M ⊕
      (↥P.color2Left ⊕ ↥P.color1Right))

def torsoNearAtomPiece :
    TorsoNearAtom G S H root M hmin P → Set V
  | .inl t => Subtype.val '' torsoCenterPiece G S H root M hmin t
  | .inr (.inl j) => torsoFreePiece G S H root M j
  | .inr (.inr (.inl u)) =>
      Subtype.val '' torsoHangerPiece G S H root M hmin u.1
  | .inr (.inr (.inr j)) =>
      Subtype.val '' torsoHangerPiece G S H root M hmin (P.match1 j)

def torsoNearAtomRecipient :
    TorsoNearAtom G S H root M hmin P → I
  | .inl t => t.1
  | .inr (.inl j) => j.1
  | .inr (.inr (.inl u)) => torsoHangerOwner G S H root M hmin u.1
  | .inr (.inr (.inr j)) => j.1.1

def torsoNearAtomOrigin :
    TorsoNearAtom G S H root M hmin P → I
  | .inl t => t.1
  | .inr (.inl j) => j.1
  | .inr (.inr (.inl u)) => torsoHangerOwner G S H root M hmin u.1
  | .inr (.inr (.inr j)) =>
      torsoHangerOwner G S H root M hmin (P.match1 j)

def torsoFarAtomPiece
    (b : TorsoFarAtom G S H root M hmin P) : Set V :=
  rigidFarBranchImage S Y N (torsoFarAtomLabel G S H root M hmin P b)

theorem nearAtom_subset_colored
    (a : TorsoNearAtom G S H root M hmin P) :
    torsoNearAtomPiece G S H root M hmin P a ⊆
      torsoColoredBranch G S H root M hmin P Y q N
        (torsoNearAtomRecipient G S H root M hmin P a) := by
  rcases a with t | a
  · exact center_subset_colored G S H root M hmin P Y q N t
  · rcases a with j | a
    · exact free_subset_colored G S H root M hmin P Y q N j
    · rcases a with u | j
      · exact hanger2_subset_colored G S H root M hmin P Y q N u
      · exact hanger1_subset_colored G S H root M hmin P Y q N j

theorem farAtom_subset_colored
    (b : TorsoFarAtom G S H root M hmin P) :
    torsoFarAtomPiece G S H root M hmin P Y q N b ⊆
      torsoColoredBranch G S H root M hmin P Y q N
        (torsoFarAtomRecipient G S H root M hmin P b) := by
  rcases b with t | b
  · exact far_touch_subset_colored G S H root M hmin P Y q N t
  · rcases b with u | j
    · exact far2_subset_colored G S H root M hmin P Y q N u
    · exact far1_subset_colored G S H root M hmin P Y q N j

theorem farAtoms_disjoint_of_recipient_ne
    (a b : TorsoFarAtom G S H root M hmin P)
    (hrec : torsoFarAtomRecipient G S H root M hmin P a ≠
      torsoFarAtomRecipient G S H root M hmin P b) :
    Disjoint (torsoFarAtomPiece G S H root M hmin P Y q N a)
      (torsoFarAtomPiece G S H root M hmin P Y q N b) := by
  have hlabel : torsoFarAtomLabel G S H root M hmin P a ≠
      torsoFarAtomLabel G S H root M hmin P b := by
    intro h
    exact hrec (torsoFarAtom_recipient_eq_of_label_eq
      G S H root M hmin P a b h)
  exact rigidFarBranchImage_pairwise_disjoint S Y N hlabel

end HadwigerLean.RootedDensity
