import HadwigerLean.Graph.Linkedness.RigidGluedFan
import HadwigerLean.Graph.Linkedness.RigidMinCut
import HadwigerLean.Graph.Linkedness.MinimalInduction
import Mathlib.Tactic

namespace HadwigerLean
namespace Linkedness

universe u

/-- D.1 no-rigid reduction, with the fan-assisted far-shore glue exposed
while its independent path transport proof is assembled. -/
theorem noRigid_of_smaller_order_and_glue
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (k : ℕ)
    (hXupper : X.card ≤ 2 * k)
    (hm : MassedPair G (X : Set V) ((8 * k : ℕ) : ℝ))
    (hbad : ¬ RootedLinked G X)
    (hsmall : SmallerOrderMassedLinked k V)
    (hFanGlue : ∀ (S : VertexSeparation G) [Fintype S.left]
      (T : VertexSeparation (G.induce S.left))
      (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right)
      (q : ℕ) (C : IndexedPairs (Fin q) S.left)
      (F : IndexedLinkage (G.induce S.left) C),
      RootedLinked (G.induce S.right) (separationBoundaryFinset S) →
      Finset.univ.image C.start = T.separatorFinset →
      (∀ i, (C.finish i : V) ∈ S.separator) →
      (∀ i x, x ∈ pathVertexSet (F.path i) → x ∈ T.right) →
      (∀ i x, x ∈ pathVertexSet (F.path i) →
        (x : V) ∈ S.right → x = C.finish i) →
      RootedLinked (G.induce (S.glueLeft T hBoundary).right)
        (separationBoundaryFinset (S.glueLeft T hBoundary))) :
    NoRigidSeparation G (X : Set V) := by
  classical
  intro S hroot hfar hsep hlinkedS
  have hXcard : Nat.card (X : Set V) = X.card := by simp
  by_cases hlt : Nat.card S.separator < X.card
  · exact hbad (rootedLinked_of_lower_rigid_of_smaller_order
      G X k hXupper hm hsmall ⟨S,hroot,hfar,hlt,hlinkedS⟩)
  have hSorder : S.separatorFinset.card = X.card := by
    have hSC : S.separatorFinset.card = Nat.card S.separator := by
      simp [VertexSeparation.separatorFinset]
    rw [hSC]
    omega
  letI : Fintype S.left := Fintype.ofFinite S.left
  obtain ⟨n,P,L,_,hstarts,hfinish⟩ |
      ⟨n,T,C,F,hTcard,hnlt,hrootT,hBoundary,hCstart,hCfinish,
        hFright,hFfirst⟩ :=
    rigid_full_fan_or_saturated_cut G S X hroot hSorder
  · exact hbad (rootedLinked_of_rigid_full_near_fan
      G S X hroot P L hstarts hfinish hlinkedS)
  · let Q := S.glueLeft T hBoundary
    have hrootQ : (X : Set V) ⊆ Q.left := by
      intro x hx
      change ∃ hxS : x ∈ S.left, (⟨x,hxS⟩ : S.left) ∈ T.left
      exact ⟨hroot hx, hrootT ((mem_torsoRootFinset S X _).mpr hx)⟩
    have hfarQ : Q.strictRight.Nonempty := by
      obtain ⟨x,hx⟩ := hfar
      exact ⟨x, S.strictRight_glueLeft T hBoundary hx⟩
    have hsepQ : Nat.card Q.separator < X.card := by
      have hQC : Nat.card Q.separator = Q.separatorFinset.card := by
        simp [VertexSeparation.separatorFinset]
      rw [hQC, S.glueLeft_separatorFinset_card T hBoundary, hTcard]
      exact hnlt
    have hlinkedQ : RootedLinked (G.induce Q.right)
        (separationBoundaryFinset Q) :=
      hFanGlue S T hBoundary n C F hlinkedS hCstart
        hCfinish hFright hFfirst
    exact hbad (rootedLinked_of_lower_rigid_of_smaller_order
      G X k hXupper hm hsmall ⟨Q,hrootQ,hfarQ,hsepQ,hlinkedQ⟩)

/-- D.1: graph-order minimality rules out every rigid shore of adhesion at
most the root order. -/
theorem noRigid_of_smaller_order
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (k : ℕ)
    (hXupper : X.card ≤ 2 * k)
    (hm : MassedPair G (X : Set V) ((8 * k : ℕ) : ℝ))
    (hbad : ¬ RootedLinked G X)
    (hsmall : SmallerOrderMassedLinked k V) :
    NoRigidSeparation G (X : Set V) := by
  apply noRigid_of_smaller_order_and_glue G X k hXupper hm hbad hsmall
  intro S _ T hBoundary q C F hfar hstarts hfinish hpathT hfirst
  exact rootedLinked_glueLeft_of_saturated_fan
    S T hBoundary C F hstarts hfinish hpathT hfirst hfar
/-- Every `8k`-massed pair with at most `2k` roots is rooted linked. -/
theorem rootedLinked_of_massed
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X : Finset V) (k : ℕ) (hk : 0 < k)
    (hX : X.card ≤ 2 * k)
    (hm : MassedPair G (X : Set V) ((8 * k : ℕ) : ℝ)) :
    RootedLinked G X := by
  classical
  apply rootedLinked_of_noRigidStep k hk ?_ G X hX hm
  intro W _ _ H Y hY hmY hbad hsmall
  exact noRigid_of_smaller_order H Y k hY hmY hbad hsmall
end Linkedness
end HadwigerLean
