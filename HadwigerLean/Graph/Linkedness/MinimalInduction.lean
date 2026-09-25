import HadwigerLean.Graph.Linkedness.MinimalCounterexample
import Mathlib.Tactic

namespace HadwigerLean
namespace Linkedness

universe u

/-- The massed-pair statement at all orders below the current graph. -/
def SmallerOrderMassedLinked (k : ℕ) (V : Type u) [Fintype V] : Prop :=
  ∀ {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (Y : Finset W),
    Fintype.card W < Fintype.card V →
    Y.card ≤ 2 * k →
    MassedPair H (Y : Set W) ((8 * k : ℕ) : ℝ) →
    RootedLinked H Y

/-- The order/incidence double induction. The only remaining input is the
D.1 no-rigid-separation step under smaller-order induction. -/
theorem rootedLinked_of_noRigidStep
    (k : ℕ) (hk : 0 < k)
    (hNoRigidStep : ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) (Y : Finset W),
      Y.card ≤ 2 * k →
      MassedPair H (Y : Set W) ((8 * k : ℕ) : ℝ) →
      ¬ RootedLinked H Y →
      SmallerOrderMassedLinked k W →
      NoRigidSeparation H (Y : Set W)) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (X : Finset V),
      X.card ≤ 2 * k →
      MassedPair G (X : Set V) ((8 * k : ℕ) : ℝ) →
      RootedLinked G X := by
  classical
  have hOrder : ∀ n : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (X : Finset V),
      Fintype.card V = n →
      X.card ≤ 2 * k →
      MassedPair G (X : Set V) ((8 * k : ℕ) : ℝ) →
      RootedLinked G X := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ _ G X hcard hX hm
      have hSmall : SmallerOrderMassedLinked k V := by
        intro W _ _ H Y hW hY hmY
        exact ih (Fintype.card W) (by omega) H Y rfl hY hmY
      have hInc : ∀ m : ℕ, ∀ (H : SimpleGraph V) (Y : Finset V),
          edgeIncidenceSetCount H (Y : Set V)ᶜ = m →
          Y.card ≤ 2 * k →
          MassedPair H (Y : Set V) ((8 * k : ℕ) : ℝ) →
          RootedLinked H Y := by
        intro m
        induction m using Nat.strong_induction_on with
        | h m ihInc =>
          intro H Y hρ hY hmY
          by_contra hbad
          obtain ⟨q,P,hP,hne,hPY,hbadP⟩ :=
            exists_bad_pairing_of_not_rootedLinked H Y hbad
          let Hs := rootPairSaturation H Y P
          have hmassBad := rootPairSaturation_massed_bad Y P
            ((8 * k : ℕ) : ℝ) hmY hbadP
          have hmHs : MassedPair Hs (Y : Set V) ((8 * k : ℕ) : ℝ) :=
            hmassBad.1
          have hbadHs : ¬ RootedLinked Hs Y := by
            intro hlinked
            exact hmassBad.2 (hlinked q P hP hne hPY)
          have hmissing : ∀ y ∈ Y,
              (Y.erase y \ Hs.neighborFinset y).card ≤ 1 := by
            intro y hy
            exact rootPairSaturation_missing H Y P hP y hy
          have hNo : NoRigidSeparation Hs (Y : Set V) :=
            hNoRigidStep Hs Y hY hmHs hbadHs hSmall
          have hρHs : edgeIncidenceSetCount Hs (Y : Set V)ᶜ = m := by
            rw [rootPairSaturation_incidence]
            exact hρ
          have hSame : ∀ H' : SimpleGraph V,
              edgeIncidenceSetCount H' (Y : Set V)ᶜ <
                edgeIncidenceSetCount Hs (Y : Set V)ᶜ →
              MassedPair H' (Y : Set V) ((8 * k : ℕ) : ℝ) →
              RootedLinked H' Y := by
            intro H' hlt hmH'
            exact ihInc (edgeIncidenceSetCount H' (Y : Set V)ᶜ)
              (by omega) H' Y rfl hY hmH'
          have hlinkedHs := rootedLinked_of_massed_extremal
            Hs Y k hk hY hmHs hmissing hNo hSmall hSame
          exact hbadHs hlinkedHs
      exact hInc (edgeIncidenceSetCount G (X : Set V)ᶜ) G X rfl hX hm
  intro V _ _ G X hX hm
  exact hOrder (Fintype.card V) G X rfl hX hm

end Linkedness
end HadwigerLean
