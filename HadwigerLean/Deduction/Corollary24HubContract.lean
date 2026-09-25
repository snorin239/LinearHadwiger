import HadwigerLean.Deduction.Corollary24Hub
import HadwigerLean.Deduction.Corollary24Numerics
import HadwigerLean.Woven.OuterContracts
import HadwigerLean.Woven.OuterInductionTransport
import HadwigerLean.Woven.OuterDeletion
import Mathlib.Tactic

/-!
# Corollary 24 hub contract

The large chromatic reserve remains above 980a after deleting the
original roles and the distinct proxies. A chromatic slice and GN give
the low-color, highly connected hub.
-/

namespace HadwigerLean.Deduction

theorem cor24_hub_contract
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T d a : ℕ) (ha : 0 < a)
    (hχ : 2000 * T + cor24B d * a ≤ chromatic G) :
    Woven.OuterHubContract G a (980 * a) := by
  classical
  intro j hj root P role hrole _hminor
  let N := G.induce (Woven.normalizedSet root P)
  let Z : Finset (Woven.normalizedSet root P) :=
    Finset.univ.image (Woven.hubRoleFin role)
  have hZcard : Z.card = a + 2 * j := by
    simp [Z, Finset.card_image_of_injective _
      (Woven.hubRoleFin_injective role hrole),
      Woven.HubProxyRole, Fintype.card_sum, Fintype.card_prod,
      Nat.mul_comm]
  have hZ7 : Z.card ≤ 7 * a := by omega
  have hχdel := Woven.chromatic_le_normalized_add_seven G root P hj
  have hχNZ := Woven.chromatic_le_card_add_complement N Z
  have hBcoef : 994 ≤ cor24B d := by
    dsimp [cor24B]
    omega
  have hBmul : 994 * a ≤ cor24B d * a :=
    Nat.mul_le_mul_right a hBcoef
  have hχD : 980 * a ≤
      chromatic (N.induce (Z : Set (Woven.normalizedSet root P))ᶜ) := by
    change chromatic G ≤ 7 * a + chromatic N at hχdel
    omega
  obtain ⟨H',hHconn',hHχ'⟩ :=
    exists_cor24_hub
      (N.induce (Z : Set (Woven.normalizedSet root P))ᶜ)
      a ha hχD
  let H : Finset (Woven.normalizedSet root P) := H'.image Subtype.val
  let e := Woven.outerNestedIso N
    (Z : Set (Woven.normalizedSet root P))ᶜ H'
  have hHconn140 : VertexConnected (N.induce (H : Set _)) (140 * a) :=
    VertexConnected.of_iso e (140 * a) hHconn'
  have hHconn : VertexConnected (N.induce (H : Set _))
      (16 * (a + j)) := by
    apply hHconn140.of_le
    omega
  have hHχ : chromatic (N.induce (H : Set _)) ≤ 980 * a := by
    have heq : chromatic
        ((N.induce (Z : Set (Woven.normalizedSet root P))ᶜ).induce
          (H' : Set _)) =
        chromatic (N.induce (H : Set _)) := by
      unfold chromatic
      exact congrArg ENat.toNat (SimpleGraph.chromaticNumber_congr e)
    rw [← heq]
    exact hHχ'
  have hZH : Disjoint Z H := by
    apply Finset.disjoint_left.mpr
    intro z hz hzH
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hzH
    exact v.property hz
  exact ⟨H,hZH,hHconn,hHχ⟩

end HadwigerLean.Deduction