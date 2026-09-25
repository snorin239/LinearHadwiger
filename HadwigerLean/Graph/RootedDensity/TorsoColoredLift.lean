import HadwigerLean.Graph.RootedDensity.TorsoColoredModel
import HadwigerLean.Graph.RootedDensity.TorsoColoredPartialLabels
import HadwigerLean.Graph.RootedDensity.RigidFarLabelPullback
import HadwigerLean.Graph.RootedDensity.TorsoHangerMatching

/-! Reverse transport of a rooted torso model through an H-universal rigid shore. -/

namespace HadwigerLean.RootedDensity

universe u v w

theorem rooted_model_lift_torso_colored
    {V : Type u} {I : Type v} {W : Type w}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype W]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph W) (e : I ↪ W) (root : I → S.left)
    (M : RootedMinorModel (H.comap e) (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N' : RootedMinorModel (H.comap e)
      (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N')
    (huni : UniversalAtRightShore H S)
    (hsize : (Linkedness.separationBoundaryFinset S).card ≤ Fintype.card W) :
    Nonempty (RootedMinorModel (H.comap e) G (Subtype.val ∘ root)) := by
  classical
  letI : DecidableEq
      (TorsoHangerIndex G S (H.comap e) root M hmin) := Classical.decEq _
  letI : DecidableEq (TorsoFreeIndex S M) := Classical.decEq _
  obtain ⟨P⟩ := exists_torso_hanger_matching G S (H.comap e) root M hmin
  obtain ⟨A,f,hAZ,hf,hcenter,htwo,hone⟩ :=
    exists_torso_colored_partial_labels G S (H.comap e) root M hmin P e
  obtain ⟨Z,q,⟨N⟩,hq⟩ :=
    rigid_shore_model_of_partial_labels G S H huni A hAZ f hf hsize
  let T : Finset I := Finset.univ.filter (fun i => e i ∈ Z)
  have hTZ : ∀ i ∈ T, e i ∈ Z := by
    intro i hi
    simpa [T] using hi
  let qT : ↥(T : Set I) → S.right :=
    fun i => q ⟨e i.1, hTZ i.1 i.2⟩
  let NT : RootedMinorModel ((H.comap e).induce (T : Set I))
      (G.induce S.right) qT :=
    rooted_model_pullback_induced_target H (G.induce S.right)
      e T Z hTZ q N
  have hcenterRoot : ∀ t : TorsoTouchIndex S M,
      ∃ hi : t.1 ∈ T,
        qT ⟨t.1,hi⟩ =
          torsoCenterAdhesion G S (H.comap e) root M hmin t := by
    intro t
    obtain ⟨ha,hfa⟩ := hcenter t
    obtain ⟨hz,hqz⟩ := hq
      ⟨torsoCenterAdhesion G S (H.comap e) root M hmin t,ha⟩
    have heZ : e t.1 ∈ Z := by
      rw [← hfa]
      exact hz
    have htT : t.1 ∈ T := by simp [T, heZ]
    refine ⟨htT, ?_⟩
    change q ⟨e t.1,hTZ t.1 htT⟩ =
      torsoCenterAdhesion G S (H.comap e) root M hmin t
    simpa only [hfa] using hqz
  have htwoRoot : ∀ u : ↥P.color2Left,
      ∃ hi : (P.match2 u).1 ∈ T,
        qT ⟨(P.match2 u).1,hi⟩ =
          torsoHangerAdhesion G S (H.comap e) root M hmin u.1 := by
    intro u
    obtain ⟨ha,hfa⟩ := htwo u
    obtain ⟨hz,hqz⟩ := hq
      ⟨torsoHangerAdhesion G S (H.comap e) root M hmin u.1,ha⟩
    have heZ : e (P.match2 u).1 ∈ Z := by
      rw [← hfa]
      exact hz
    have huT : (P.match2 u).1 ∈ T := by simp [T, heZ]
    refine ⟨huT, ?_⟩
    change q ⟨e (P.match2 u).1,hTZ (P.match2 u).1 huT⟩ =
      torsoHangerAdhesion G S (H.comap e) root M hmin u.1
    simpa only [hfa] using hqz
  have honeRoot : ∀ j : ↥P.color1Right,
      ∃ hi : j.1.1 ∈ T,
        qT ⟨j.1.1,hi⟩ =
          torsoHangerAdhesion G S (H.comap e) root M hmin (P.match1 j) := by
    intro j
    obtain ⟨ha,hfa⟩ := hone j
    obtain ⟨hz,hqz⟩ := hq
      ⟨torsoHangerAdhesion G S (H.comap e) root M hmin (P.match1 j),ha⟩
    have heZ : e j.1.1 ∈ Z := by
      rw [← hfa]
      exact hz
    have hjT : j.1.1 ∈ T := by simp [T, heZ]
    refine ⟨hjT, ?_⟩
    change q ⟨e j.1.1,hTZ j.1.1 hjT⟩ =
      torsoHangerAdhesion G S (H.comap e) root M hmin (P.match1 j)
    simpa only [hfa] using hqz
  exact ⟨rooted_model_of_colored_far_model G S (H.comap e) root
    M hmin P T qT NT hcenterRoot htwoRoot honeRoot⟩

end HadwigerLean.RootedDensity
