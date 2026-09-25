import HadwigerLean.Graph.RootedDensity.TorsoColoredDisjoint
import HadwigerLean.Graph.RootedDensity.TorsoColoredAdjacency
import HadwigerLean.Graph.RootedDensity.TorsoColoredConnected

/-! The colored pieces form a rooted minor model in the original graph. -/

namespace HadwigerLean.RootedDensity

universe u v

def rooted_model_of_colored_far_model
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
    RootedMinorModel H G (Subtype.val ∘ root) := by
  classical
  exact {
    branch := torsoColoredBranch G S H root M hmin P Y q N
    connected := torsoColoredBranch_connected G S H root M hmin P
      Y q N hcenterRoot htwoRoot honeRoot
    disjoint := torsoColoredBranch_pairwise_disjoint G S H root M hmin P
      Y q N hcenterRoot htwoRoot honeRoot
    adjacent := by
      intro i j hij
      exact torsoColoredBranch_adjacent G S H root M hmin P
        Y q N hcenterRoot honeRoot hij
    root_mem := by
      intro i
      exact torsoColoredBranch_root_mem G S H root M hmin P Y q N i
  }

end HadwigerLean.RootedDensity

