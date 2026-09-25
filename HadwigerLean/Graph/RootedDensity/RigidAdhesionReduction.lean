import HadwigerLean.Graph.RootedDensity.RigidAdhesionCut
import HadwigerLean.Graph.RootedDensity.MassedStructure
import Mathlib.Tactic

/-! Reduction of every H-rigid shore to one with adhesion below the root
order, conditional only on the two independent fan model transports. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- If lower-adhesion rigid shores are excluded, the Menger dichotomy and
the two model transports exclude every rigid shore. -/
theorem no_rigid_of_lower_rigid_exclusion_and_fans
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (X : Finset V)
    (hbad : ¬ UniversalAt G H X)
    (hlower : ∀ S : VertexSeparation G,
      (X : Set V) ⊆ S.left →
      S.strictRight.Nonempty →
      Nat.card S.separator < X.card →
      UniversalAtRightShore H S → False)
    (hfull : ∀ (S : VertexSeparation G) [Fintype S.left],
      (X : Set V) ⊆ S.left →
      ∀ {n : ℕ} (P : IndexedPairs (Fin n) S.left)
        (_ : IndexedLinkage (G.induce S.left) P),
        Finset.univ.image P.start = Linkedness.torsoRootFinset S X →
        (∀ i, P.finish i ∈ Linkedness.torsoBoundaryFinset G S) →
        (Linkedness.separationBoundaryFinset S).card ≤ Fintype.card W →
        UniversalAtRightShore H S → UniversalAt G H X)
    (hsaturated : ∀ (S : VertexSeparation G) [Fintype S.left]
      (T : VertexSeparation (G.induce S.left))
      (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right)
      {q : ℕ} (C : IndexedPairs (Fin q) S.left)
      (F : IndexedLinkage (G.induce S.left) C),
      Finset.univ.image C.start = T.separatorFinset →
      (∀ i, (C.finish i : V) ∈ S.separator) →
      (∀ i x, x ∈ pathVertexSet (F.path i) → x ∈ T.right) →
      (∀ i x, x ∈ pathVertexSet (F.path i) →
        (x : V) ∈ S.right → x = C.finish i) →
      (Linkedness.separationBoundaryFinset S).card ≤ Fintype.card W →
      UniversalAtRightShore H S →
      UniversalAtRightShore H (S.glueLeft T hBoundary)) :
    ∀ S : VertexSeparation G,
      (X : Set V) ⊆ S.left →
      RigidSeparation H S → False := by
  classical
  intro S hroot hrigid
  obtain ⟨hfar, hsizeNat, huni⟩ := hrigid
  have hsize : (Linkedness.separationBoundaryFinset S).card ≤ Fintype.card W := by
    rw [Linkedness.separationBoundaryFinset_card_eq]
    exact hsizeNat
  by_cases hlt : Nat.card S.separator < X.card
  · exact hlower S hroot hfar hlt huni
  have horder : X.card ≤ S.separatorFinset.card := by
    have hSC : S.separatorFinset.card = Nat.card S.separator := by
      simp [VertexSeparation.separatorFinset]
    omega
  letI : Fintype S.left := Fintype.ofFinite S.left
  obtain ⟨n,P,L,_,hstarts,hfinish⟩ |
      ⟨n,T,C,F,hTcard,hnlt,hrootT,hBoundary,hCstart,hCfinish,
        hFright,hFfirst⟩ :=
    rigid_full_fan_or_saturated_cut_ge G S X hroot horder
  · exact hbad (hfull S hroot P L hstarts hfinish hsize huni)
  · let Q := S.glueLeft T hBoundary
    have hrootQ : (X : Set V) ⊆ Q.left := by
      intro x hx
      change ∃ hxS : x ∈ S.left, (⟨x,hxS⟩ : S.left) ∈ T.left
      exact ⟨hroot hx,
        hrootT ((Linkedness.mem_torsoRootFinset S X _).mpr hx)⟩
    have hfarQ : Q.strictRight.Nonempty := by
      obtain ⟨x,hx⟩ := hfar
      exact ⟨x, S.strictRight_glueLeft T hBoundary hx⟩
    have hsepQ : Nat.card Q.separator < X.card := by
      have hQC : Nat.card Q.separator = Q.separatorFinset.card := by
        simp [VertexSeparation.separatorFinset]
      rw [hQC, S.glueLeft_separatorFinset_card T hBoundary, hTcard]
      exact hnlt
    have huniQ : UniversalAtRightShore H Q :=
      hsaturated S T hBoundary C F hCstart hCfinish hFright hFfirst hsize huni
    exact hlower Q hrootQ hfarQ hsepQ huniQ

end HadwigerLean.RootedDensity
