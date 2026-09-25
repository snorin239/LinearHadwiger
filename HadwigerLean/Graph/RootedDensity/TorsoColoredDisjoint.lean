import HadwigerLean.Graph.RootedDensity.TorsoColoredDecompose
import HadwigerLean.Graph.RootedDensity.TorsoColoredNearDisjoint

/-! Pairwise disjointness of the colored reverse-glue branches. -/

namespace HadwigerLean.RootedDensity

universe u v

theorem torsoColoredBranch_pairwise_disjoint
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
          torsoHangerAdhesion G S H root M hmin (P.match1 j)) :
    Pairwise (fun i j =>
      Disjoint (torsoColoredBranch G S H root M hmin P Y q N i)
        (torsoColoredBranch G S H root M hmin P Y q N j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases (mem_torsoColoredBranch_iff_atoms G S H root M hmin P Y q N i x).mp
      hxi with ⟨a,ha,hxa⟩ | ⟨a,ha,hxa⟩
  · rcases (mem_torsoColoredBranch_iff_atoms G S H root M hmin P Y q N j x).mp
        hxj with ⟨b,hb,hxb⟩ | ⟨b,hb,hxb⟩
    · have hrec : torsoNearAtomRecipient G S H root M hmin P a ≠
          torsoNearAtomRecipient G S H root M hmin P b := by
        intro heq
        exact hij (ha.symm.trans (heq.trans hb))
      exact (Set.disjoint_left.mp
        (nearAtoms_disjoint_of_recipient_ne
          G S H root M hmin P a b hrec)) hxa hxb
    · have hrec : torsoNearAtomRecipient G S H root M hmin P a ≠
          torsoFarAtomRecipient G S H root M hmin P b := by
        intro heq
        exact hij (ha.symm.trans (heq.trans hb))
      exact (Set.disjoint_left.mp
        (nearFarAtoms_disjoint_of_recipient_ne
          G S H root M hmin P Y q N hcenterRoot htwoRoot honeRoot
          a b hrec)) hxa hxb
  · rcases (mem_torsoColoredBranch_iff_atoms G S H root M hmin P Y q N j x).mp
        hxj with ⟨b,hb,hxb⟩ | ⟨b,hb,hxb⟩
    · have hrec : torsoNearAtomRecipient G S H root M hmin P b ≠
          torsoFarAtomRecipient G S H root M hmin P a := by
        intro heq
        exact hij (ha.symm.trans (heq.symm.trans hb))
      exact (Set.disjoint_left.mp
        (nearFarAtoms_disjoint_of_recipient_ne
          G S H root M hmin P Y q N hcenterRoot htwoRoot honeRoot
          b a hrec)) hxb hxa
    · have hrec : torsoFarAtomRecipient G S H root M hmin P a ≠
          torsoFarAtomRecipient G S H root M hmin P b := by
        intro heq
        exact hij (ha.symm.trans (heq.trans hb))
      exact (Set.disjoint_left.mp
        (farAtoms_disjoint_of_recipient_ne
          G S H root M hmin P Y q N a b hrec)) hxa hxb

end HadwigerLean.RootedDensity
