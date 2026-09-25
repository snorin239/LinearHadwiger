import HadwigerLean.Graph.RootedDensity.TorsoColoredAdjacency

/-! Far branch labels used by the colored reverse glue have unique recipients. -/

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

def TorsoFarAtom :=
  TorsoTouchIndex S M ⊕
    (↥P.color2Left ⊕ ↥P.color1Right)

def torsoFarAtomLabel :
    TorsoFarAtom G S H root M hmin P → I
  | .inl t => t.1
  | .inr (.inl u) => (P.match2 u).1
  | .inr (.inr j) => j.1.1

def torsoFarAtomRecipient :
    TorsoFarAtom G S H root M hmin P → I
  | .inl t => t.1
  | .inr (.inl u) => torsoHangerOwner G S H root M hmin u.1
  | .inr (.inr j) => j.1.1

theorem torsoFarAtom_recipient_eq_of_label_eq
    (a b : TorsoFarAtom G S H root M hmin P)
    (hab : torsoFarAtomLabel G S H root M hmin P a =
      torsoFarAtomLabel G S H root M hmin P b) :
    torsoFarAtomRecipient G S H root M hmin P a =
      torsoFarAtomRecipient G S H root M hmin P b := by
  rcases a with t | a
  · rcases b with s | b
    · exact hab
    · rcases b with u | j
      · change t.1 = (P.match2 u).1 at hab
        have h : ModelTouchesBoundary S M (P.match2 u).1 := hab ▸ t.2
        exact ((P.match2 u).2 h).elim
      · change t.1 = j.1.1 at hab
        have h : ModelTouchesBoundary S M j.1.1 := hab ▸ t.2
        exact (j.1.2 h).elim
  · rcases a with u | j
    · rcases b with t | b
      · change (P.match2 u).1 = t.1 at hab
        have h : ModelTouchesBoundary S M (P.match2 u).1 := hab.symm ▸ t.2
        exact ((P.match2 u).2 h).elim
      · rcases b with w | k
        · have huw : P.match2 u = P.match2 w := Subtype.ext hab
          have h : u = w := P.match2.injective huw
          simpa [h, torsoFarAtomRecipient]
        · have huk : P.match2 u = k.1 := Subtype.ext hab
          have hk : P.match2 u ∈ P.color1Right := huk ▸ k.2
          exact ((P.match2_avoid_color1 u) hk).elim
    · rcases b with t | b
      · change j.1.1 = t.1 at hab
        have h : ModelTouchesBoundary S M j.1.1 := hab.symm ▸ t.2
        exact (j.1.2 h).elim
      · rcases b with u | k
        · have hju : j.1 = P.match2 u := Subtype.ext hab
          have hj : P.match2 u ∈ P.color1Right := hju ▸ j.2
          exact ((P.match2_avoid_color1 u) hj).elim
        · exact hab

end HadwigerLean.RootedDensity

