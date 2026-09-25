import HadwigerLean.Woven.OuterNonbaseThreeChild
import HadwigerLean.Woven.OuterDeletion
import HadwigerLean.Woven.NormalizedBase
import HadwigerLean.Graph.CliqueMinorOrder
import Mathlib.Tactic

/-!
# A full nonbase woven step under explicit hub and separation contracts

The contracts describe only the external chromatic inputs. The proof
checks normalization, the large-minor case, double-fan assembly, the
three-child rooted model, and the exact scale budget.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem vertexConnected_change_fintype
    {W : Type*} {G : SimpleGraph W} {k : ℕ}
    {f₁ f₂ : Fintype W}
    (h : @VertexConnected W f₁ G k) :
    @VertexConnected W f₂ G k := by
  have hc : @Fintype.card W f₁ = @Fintype.card W f₂ :=
    @Fintype.card_congr W W f₁ f₂ (Equiv.refl W)
  have ho : k < @Fintype.card W f₁ := h.1
  exact ⟨by omega, h.2⟩

theorem woven_nonbase_of_hub_separation
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m i K U B h σ : ℕ}
    (hi : i < m)
    (hK : 33 ≤ K)
    (hbudget :
      3 * outerChildLoss (outerScale m i) K h σ ≤
        B * outerScale m i)
    (hGN : K * outerScale m i ≤
      U + B * outerScale m (i + 1))
    (hsepThreshold : σ <
      U + B * outerScale m (i + 1) +
        6 * (K * outerScale m i))
    (hIH : OuterAt G m (i + 1) K U B)
    (hhub : ∀ (j : ℕ) (_ : j ≤ 3 * outerScale m i)
      (root : Fin (outerScale m i) → V)
      (P : IndexedPairs (Fin j) V)
      (role : Fin (outerScale m i + 2 * j) →
        normalizedSet root P),
      Function.Injective role →
      ¬ HasCliqueMinor (G.induce (normalizedSet root P))
        (14 * outerScale m i) →
      ∃ H : Finset (normalizedSet root P),
        Disjoint (Finset.univ.image (hubRoleFin role)) H ∧
        VertexConnected
          ((G.induce (normalizedSet root P)).induce (H : Set _))
          (16 * (outerScale m i + j)) ∧
        chromatic
          ((G.induce (normalizedSet root P)).induce (H : Set _)) ≤ h)
    (hsep : ∀ (j : ℕ) (_ : j ≤ 3 * outerScale m i)
      (root : Fin (outerScale m i) → V)
      (P : IndexedPairs (Fin j) V),
      ¬ HasCliqueMinor (G.induce (normalizedSet root P))
        (14 * outerScale m i) →
      ∀ X : Finset (normalizedSet root P),
        2 * σ <
          chromatic ((G.induce (normalizedSet root P)).induce
            (X : Set _)) →
        Bootstrap.ChromaticSeparable
          ((G.induce (normalizedSet root P)).induce (X : Set _)) σ)
    (hconn : VertexConnected G (K * outerScale m i))
    (hχ : U + B * outerScale m i ≤ chromatic G) :
    Woven G (outerScale m i) (3 * outerScale m i) := by
  classical
  let a := outerScale m i
  let c := outerScale m (i + 1)
  have hapos : 0 < a := outerScale_pos m i
  have hscale : 3 * c = 2 * a := outerScale_child m i hi
  have hK7 : 7 ≤ K := by omega
  have hK28 : 28 ≤ K := by omega
  have hKa7 : 7 * a ≤ K * a :=
    Nat.mul_le_mul_right a hK7
  have hKa28 : 28 * a ≤ K * a :=
    Nat.mul_le_mul_right a hK28
  have hKa33 : 33 * a ≤ K * a :=
    Nat.mul_le_mul_right a hK
  have hheadroom :
      U + B * c + outerChildLoss a K h σ ≤ U + B * a := by
    have hs : 3 * (B * c) = 2 * (B * a) := by
      calc
        3 * (B * c) = B * (3 * c) := by ring
        _ = B * (2 * a) := by rw [hscale]
        _ = 2 * (B * a) := by ring
    change 3 * outerChildLoss a K h σ ≤ B * a at hbudget
    omega
  have hloss :
      outerChildLoss a K h σ =
        45 * a + 12 * (K * a) + h + 2 * σ := by
    simp only [outerChildLoss]
    ring
  intro root hroot j hj P hP
  let N := G.induce (normalizedSet root P)
  have hbudgetMinor : 2 * (a + 2 * j) ≤ K * a := by
    have hj' : j ≤ 3 * a := hj
    omega
  by_cases hminor : HasCliqueMinor N (14 * a)
  · have hsmall : HasCliqueMinor N (2 * (a + 2 * j)) :=
      hasCliqueMinor_of_le hminor (by omega)
    exact exists_solution_of_ambient_normalized_minor
      G root P hroot hP hconn hbudgetMinor hsmall
  · let κ := K * a - 7 * a
    have hocc : (occupiedRoles root P).card ≤ 7 * a := by
      have hc := occupiedRoles_card_le root P
      omega
    have hκ : (occupiedRoles root P).card + κ ≤ K * a := by
      dsimp [κ]
      omega
    have hNconn : VertexConnected N κ := by
      exact vertexConnected_change_fintype
        (hconn.induce_compl (occupiedRoles root P) κ hκ)
    have hκfan : 21 * a ≤ κ := by
      dsimp [κ]
      omega
    have hκconnector : 9 * a ≤ κ := by omega
    have hdegree : ∀ x,
        2 * (a + 2 * j) ≤ G.degree (originalRoleFin root P x) := by
      intro x
      exact hbudgetMinor.trans
        (Linkedness.degree_ge_of_vertexConnected hconn _)
    obtain ⟨role,hrole,hadj⟩ :=
      exists_normalized_proxies G root P hdegree
    let Z : Finset (normalizedSet root P) :=
      Finset.univ.image (hubRoleFin role)
    have hZcard : Z.card = a + 2 * j := by
      simp [Z, a, Finset.card_image_of_injective _
        (hubRoleFin_injective role hrole), HubProxyRole,
        Fintype.card_sum, Fintype.card_prod, Nat.mul_comm]
    have hZ7 : Z.card ≤ 7 * a := by omega
    obtain ⟨H,hZH,hHconn,hHχ⟩ :=
      hhub j hj root P role hrole hminor
    have hfan : 3 * Z.card ≤ κ := by omega
    have hconnector : Z.card + 2 * a ≤ κ := by omega
    have hχdel := chromatic_le_normalized_add_seven G root P hj
    have hχN :
        (3 * a + (U + B * c) + 2 * σ + 6 * (K * a)) +
          5 * Z.card + h + 6 * (K * a) ≤ chromatic N := by
      change chromatic G ≤ 7 * a + chromatic N at hχdel
      rw [hloss] at hheadroom
      change U + B * a ≤ chromatic G at hχ
      omega
    have hchildconn : K * c ≤ K * a :=
      Nat.mul_le_mul_left K (by omega : c ≤ a)
    have hκparent : a + 16 * (2 * a) ≤ K * a := by omega
    have hκchild : 0 < K * a := Nat.mul_pos (by omega) hapos
    have hχsep :
        3 * a + 3 * σ <
          3 * a + (U + B * c) + 2 * σ + 6 * (K * a) := by
      change σ < U + B * c + 6 * (K * a) at hsepThreshold
      omega
    exact exists_solution_of_three_child_nonbase
      G rfl rfl hi hIH hκchild hκparent hchildconn
      hχsep hGN root P hroot hP role hrole hadj
      hNconn H hHconn hHχ hZH hfan hconnector hχN
      (hsep j hj root P hminor)

end Woven
end HadwigerLean
