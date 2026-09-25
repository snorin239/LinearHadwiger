import HadwigerLean.Woven.OuterNonbaseGeometryRooted
import HadwigerLean.Woven.OuterResidual
import HadwigerLean.Graph.Linkedness.Final
import Mathlib.Tactic

/-!
# The normalized nonbase woven assembly

A low-chromatic linked hub and the uniformly rooted minor conclusion in
the residual graph imply a woven solution for arbitrary original roles.
This theorem carries out the double-fan and chromatic-residual extraction.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_solution_of_hub_and_uniform_residual
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a j κ k h q : ℕ}
    (root : Fin a → V) (P : IndexedPairs (Fin j) V)
    [Fintype (normalizedSet root P)]
    (hroot : Function.Injective root)
    (hP : P.DisjointTerminals)
    (role : Fin (a + 2 * j) → normalizedSet root P)
    (hrole : Function.Injective role)
    (hadj : ∀ i, G.Adj (originalRoleFin root P i) (role i).1)
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
    (hUcard : 2 * a ≤ k)
    (hk : 0 < k)
    (hχfan : 5 * (Finset.univ.image (hubRoleFin role)).card +
      h + 7 * k ≤ chromatic (G.induce (normalizedSet root P)))
    (hχrooted : q + 5 * (Finset.univ.image (hubRoleFin role)).card +
      h + 6 * k ≤ chromatic (G.induce (normalizedSet root P)))
    (hrooted : ∀ U : Finset (normalizedSet root P),
      VertexConnected
        ((G.induce (normalizedSet root P)).induce (U : Set _)) k →
      q ≤ chromatic
        ((G.induce (normalizedSet root P)).induce (U : Set _)) →
      ∀ (r : Fin a → (U : Set (normalizedSet root P))),
        Function.Injective r →
        HasRootedCliqueMinor
          ((G.induce (normalizedSet root P)).induce
            (U : Set (normalizedSet root P))) r) :
    Nonempty (WovenSolution G root P) := by
  classical
  let N := G.induce (normalizedSet root P)
  let Z : Finset (normalizedSet root P) :=
    Finset.univ.image (hubRoleFin role)
  have hHcard : 2 * Z.card ≤ H.card := by
    have hh := hHconn.order_gt
    change 16 * (a + j) < Fintype.card (H : Set (normalizedSet root P)) at hh
    have hcard : Fintype.card (H : Set (normalizedSet root P)) = H.card := by
      simpa using (Fintype.card_coe H)
    rw [hcard] at hh
    have hzcard : Z.card = a + 2 * j := by
      simp [Z, Finset.card_image_of_injective _ (hubRoleFin_injective role hrole),
        HubProxyRole, Fintype.card_sum, Fintype.card_prod, Nat.mul_comm]
    omega
  obtain ⟨F, -, hFχ⟩ :=
    exists_double_fan_chromatic_le_four_mul
      (G := N) (Z := Z) (H := H) κ hconn hfan hHcard hZH
  obtain ⟨U, hU, hUconn, hUχ⟩ :=
    exists_connected_fan_residual (G := N) (Z := Z) (H := H)
      F hFχ h hHχ k hk (by
        have hχ := hχfan
        change 5 * Z.card + h + 7 * k ≤ chromatic N at hχ
        omega)
  have hUχq : q ≤ chromatic (N.induce (U : Set _)) := by
    have hχ := hχrooted
    change q + 5 * Z.card + h + 6 * k ≤ chromatic N at hχ
    omega
  have hUZ : Disjoint Z U := by
    apply Finset.disjoint_left.mpr
    intro v hvZ hvU
    exact (Finset.mem_compl.mp (hU hvU)) (Finset.mem_union.mpr
      (Or.inl (Finset.mem_union.mpr (Or.inl hvZ))))
  have hUH : Disjoint H U := by
    apply Finset.disjoint_left.mpr
    intro v hvH hvU
    exact (Finset.mem_compl.mp (hU hvU)) (Finset.mem_union.mpr
      (Or.inl (Finset.mem_union.mpr (Or.inr hvH))))
  have hUF : ∀ slot v, v ∈ pathVertexSet (F.path slot) → v ∉ U := by
    intro slot v hv hvU
    have hvF : v ∈ F.vertexFinset := by
      apply Finset.mem_biUnion.mpr
      exact ⟨slot, Finset.mem_univ _, List.mem_toFinset.mpr hv⟩
    exact (Finset.mem_compl.mp (hU hvU)) (Finset.mem_union.mpr
      (Or.inr hvF))
  have hUorder : 2 * a ≤ U.card := by
    have hu := hUconn.order_gt
    change k < Fintype.card (U : Set (normalizedSet root P)) at hu
    have hcard : Fintype.card (U : Set (normalizedSet root P)) = U.card := by
      simpa using (Fintype.card_coe U)
    rw [hcard] at hu
    omega
  have hHorder : 2 * (a + j) ≤ H.card := by
    have hh := hHconn.order_gt
    change 16 * (a + j) < Fintype.card (H : Set (normalizedSet root P)) at hh
    have hcard : Fintype.card (H : Set (normalizedSet root P)) = H.card := by
      simpa using (Fintype.card_coe H)
    rw [hcard] at hh
    omega
  have hlinked : Linkedness.KLinked
      (N.induce (H : Set _)) (a + j) :=
    Linkedness.kLinked_of_sixteen_mul_vertexConnected
      (N.induce (H : Set _)) (a + j) hHconn
  exact exists_original_solution_of_normalized_hub_geometry_of_residual_minors
    G root P hroot hP role hrole hadj U H F hUF
    hUZ hUH hZH (hrooted U hUconn hUχq)
    hconn hconnector hUorder hlinked hHorder

end Woven
end HadwigerLean
