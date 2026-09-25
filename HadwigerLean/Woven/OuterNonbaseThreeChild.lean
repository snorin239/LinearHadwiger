import HadwigerLean.Woven.OuterNonbaseBridge
import HadwigerLean.Woven.OuterInductionTransport
import HadwigerLean.Woven.ThreeChildResidualUniform
import HadwigerLean.Woven.SeparationIso
import Mathlib.Tactic

/-!
# Nonbase outer step from three woven children

The induction hypothesis is inherited by the normalized graph and then
the connected residual graph. The three-child theorem supplies rooted
minors there for every root map.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_solution_of_three_child_nonbase
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m i K U B a c j κ σ h : ℕ}
    (ha : a = outerScale m i)
    (hc : c = outerScale m (i + 1))
    (hi : i < m)
    (hIH : OuterAt G m (i + 1) K U B)
    (hκchild : 0 < K * a)
    (hκparent : a + 16 * (2 * a) ≤ K * a)
    (hchildconn : K * c ≤ K * a)
    (hχsep : 3 * a + 3 * σ <
      3 * a + (U + B * c) + 2 * σ + 6 * (K * a))
    (hχGN : K * a ≤ U + B * c)
    (root : Fin a → V) (P : IndexedPairs (Fin j) V)
    [Fintype (normalizedSet root P)]
    (hroot : Function.Injective root)
    (hP : P.DisjointTerminals)
    (role : Fin (a + 2 * j) → normalizedSet root P)
    (hrole : Function.Injective role)
    (hadj : ∀ x, G.Adj (originalRoleFin root P x) (role x).1)
    (hconn : VertexConnected (G.induce (normalizedSet root P)) κ)
    (H : Finset (normalizedSet root P))
    (hHconn : VertexConnected
      ((G.induce (normalizedSet root P)).induce (H : Set _))
      (16 * (a + j)))
    (hHχ : chromatic
      ((G.induce (normalizedSet root P)).induce (H : Set _)) ≤ h)
    (hZH : Disjoint (Finset.univ.image (hubRoleFin role)) H)
    (hfan : 3 * (Finset.univ.image (hubRoleFin role)).card ≤ κ)
    (hconnector : (Finset.univ.image (hubRoleFin role)).card + 2 * a ≤ κ)
    (hχN :
      (3 * a + (U + B * c) + 2 * σ + 6 * (K * a)) +
        5 * (Finset.univ.image (hubRoleFin role)).card +
        h + 6 * (K * a) ≤
        chromatic (G.induce (normalizedSet root P)))
    (hsep : ∀ X : Finset (normalizedSet root P),
      2 * σ <
        chromatic ((G.induce (normalizedSet root P)).induce (X : Set _)) →
      Bootstrap.ChromaticSeparable
        ((G.induce (normalizedSet root P)).induce (X : Set _)) σ) :
    Nonempty (WovenSolution G root P) := by
  classical
  let N := G.induce (normalizedSet root P)
  let q := 3 * a + (U + B * c) + 2 * σ + 6 * (K * a)
  have hscale : 2 * a = 3 * c := by
    have hs := outerScale_child m i hi
    rw [← ha, ← hc] at hs
    omega
  have hapos : 0 < a := by
    rw [ha]
    exact outerScale_pos m i
  have hchild : OuterAt N m (i + 1) K U B :=
    outerAt_induce G m (i + 1) K U B hIH (normalizedSet root P)
  have hrooted (X : Finset (normalizedSet root P))
      (hXconn : VertexConnected (N.induce (X : Set _)) (K * a))
      (hXχ : q ≤ chromatic (N.induce (X : Set _))) :
      ∀ (r : Fin a → (X : Set (normalizedSet root P))),
        Function.Injective r →
        HasRootedCliqueMinor (N.induce (X : Set _)) r := by
    let R := N.induce (X : Set _)
    have hchildR : OuterAt R m (i + 1) K U B :=
      outerAt_induce N m (i + 1) K U B hchild (X : Set _)
    have hsepR (Y : Finset (X : Set (normalizedSet root P)))
        (hYχ : 2 * σ < chromatic (R.induce (Y : Set _))) :
        Bootstrap.ChromaticSeparable (R.induce (Y : Set _)) σ := by
      let Y' : Finset (normalizedSet root P) :=
        Y.image Subtype.val
      let e := outerNestedIso N (X : Set _) Y
      have hχeq : chromatic (R.induce (Y : Set _)) =
          chromatic (N.induce (Y' : Set _)) := by
        unfold chromatic
        exact congrArg ENat.toNat (SimpleGraph.chromaticNumber_congr e)
      have hY'χ : 2 * σ < chromatic (N.induce (Y' : Set _)) := by
        rw [← hχeq]
        exact hYχ
      exact chromaticSeparable_of_iso e σ (hsep Y' hY'χ)
    have hchildR' (Y : Finset (X : Set (normalizedSet root P)))
        (hYconn : VertexConnected (R.induce (Y : Set _)) (K * a))
        (hYχ : U + B * c ≤ chromatic (R.induce (Y : Set _))) :
        Woven (R.induce (Y : Set _)) c (3 * c) := by
      have hYconn' : VertexConnected (R.induce (Y : Set _)) (K * c) :=
        hYconn.of_le hchildconn
      have hYχ' : U + B * outerScale m (i + 1) ≤
          chromatic (R.induce (Y : Set _)) := by
        rwa [← hc]
      have hYconn'' : VertexConnected (R.induce (Y : Set _))
          (K * outerScale m (i + 1)) := by simpa [← hc] using hYconn'
      have hYwoven := hchildR Y hYconn'' hYχ'
      simpa [hc] using hYwoven
    apply rooted_minor_for_every_root_of_high_chromatic_residual
      R hapos hscale
      (s := σ) (κparent := K * a) (κchild := K * a)
      (childThreshold := U + B * c) (b := 3 * c)
      hsepR
    · change q ≤ chromatic R at hXχ
      dsimp [q] at hXχ
      omega
    · change q ≤ chromatic R at hXχ
      dsimp [q] at hXχ
      omega
    · exact hκchild
    · change q ≤ chromatic R at hXχ
      dsimp [q] at hXχ
      omega
    · omega
    · intro Y hYconn hYχ
      exact hchildR' Y hYconn hYχ
    · exact hXconn
    · exact hκparent
    · omega
  have hχfan :
      5 * (Finset.univ.image (hubRoleFin role)).card +
        h + 7 * (K * a) ≤ chromatic N := by
    have hq : K * a ≤ q := by
      dsimp [q]
      omega
    change q + 5 * (Finset.univ.image (hubRoleFin role)).card +
      h + 6 * (K * a) ≤ chromatic N at hχN
    omega
  exact exists_solution_of_hub_and_uniform_residual G root P
    hroot hP role hrole hadj hconn H hHconn hHχ hZH
    hfan hconnector (by omega : 2 * a ≤ K * a) hκchild
    hχfan hχN hrooted

end Woven
end HadwigerLean
