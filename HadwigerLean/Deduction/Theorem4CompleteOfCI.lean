import HadwigerLean.Deduction.Theorem4Outer
import HadwigerLean.Deduction.Theorem4SepContract
import HadwigerLean.Deduction.Theorem4FinalNat
import HadwigerLean.Deduction.PowerThree
import HadwigerLean.Woven.ThreeChildGNIso
import HadwigerLean.Graph.VertexConnectivityIso
import Mathlib.Tactic

/-! The exact Theorem 4 statement follows from the local-bound CI theorem. -/

namespace HadwigerLean.Deduction

universe u

private theorem theorem4_outerScale_le_top
    (m i : ℕ) (hi : i ≤ m) :
    Woven.outerScale m i ≤ 3 ^ m := by
  have hp : 2 ^ i ≤ 3 ^ i := by
    gcongr
    omega
  calc
    Woven.outerScale m i = 2 ^ i * 3 ^ (m - i) := rfl
    _ ≤ 3 ^ i * 3 ^ (m - i) := Nat.mul_le_mul_right _ hp
    _ = 3 ^ m := by rw [← pow_add, Nat.add_sub_of_le hi]

theorem theorem4_outerAt_top_of_ci
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m T D : ℕ) (hT : T = 3 ^ m) (hT3 : 3 ≤ T)
    (hD : 2000 ≤ D) (hCI : Theorem4CIInput.{u} D) :
    Woven.OuterAt G m 0 D (D * T)
      (theorem4B D (theorem4RatioCeil (theorem4ScaleMaxRatio G D T))) := by
  classical
  apply theorem4_outerAt_top_of_sep_contracts G m T D hT hT3 hD
  intro i hi hcut F
  let a := Woven.outerScale m i
  let s := theorem4RatioCeil (theorem4ScaleMaxRatio G D T)
  have ha : 0 < a := Woven.outerScale_pos m i
  have haT : a ≤ T := by
    rw [hT]
    exact theorem4_outerScale_le_top m i (Nat.le_of_lt hi)
  have hmaxF : theorem4ScaleMaxRatio (G.induce (F : Set V)) D T ≤
      theorem4ScaleMaxRatio G D T :=
    theorem4ScaleMaxRatio_induce_le G (F : Set V) D T
  have hf : theorem4ScaleMaxRatio (G.induce (F : Set V)) D T ≤ (s : ℝ) :=
    hmaxF.trans (theorem4_ratio_le_ceil _)
  exact theorem4_sep_contract_of_ci (G.induce (F : Set V))
    T D a s ha haT hcut hf hCI

theorem theorem4_of_ci
    (D : ℕ) (hD : 2000 ≤ D) (hCI : Theorem4CIInput.{u} D) :
    Theorem4Statement.{u} := by
  classical
  refine ⟨3 ^ 9 * D, by omega, ?_⟩
  intro V _ G t ht hminor
  let m : ℕ := Nat.clog 3 t
  let T : ℕ := 3 ^ m
  have hT : Bootstrap.IsLeastPowerOfThreeAtLeast t T :=
    least_power_of_three_spec t
  have hT3 : 3 ≤ T := ht.trans hT.2.1
  apply theorem4_final_of_top_woven_nat G D t T hD ht hT hminor
  intro U hconn hχ
  let F := G.induce (U : Set V)
  have htop : Woven.OuterAt F m 0 D (D * T)
      (theorem4B D (theorem4RatioCeil (theorem4ScaleMaxRatio F D T))) :=
    theorem4_outerAt_top_of_ci F m T D rfl hT3 hD hCI
  let e : F.induce ((Finset.univ : Finset (U : Set V)) : Set (U : Set V))
      ≃g F := by
    let f : {x : (U : Set V) // x ∈ ((Finset.univ : Finset (U : Set V)) : Set (U : Set V))}
        ≃ (U : Set V) :=
      Equiv.ofBijective Subtype.val
        ⟨Subtype.val_injective, by
          intro x
          exact ⟨⟨x, by simp⟩, rfl⟩⟩
    exact { toEquiv := f, map_rel_iff' := by intro x y; rfl }
  have hconnUniv : VertexConnected
      (F.induce ((Finset.univ : Finset (U : Set V)) : Set (U : Set V)))
      (D * T) := VertexConnected.of_iso e.symm (D * T) hconn
  have hchrom : chromatic
      (F.induce ((Finset.univ : Finset (U : Set V)) : Set (U : Set V))) =
      chromatic F := by
    unfold chromatic
    exact congrArg ENat.toNat (SimpleGraph.chromaticNumber_congr e)
  have hχUniv : D * T +
      theorem4B D (theorem4RatioCeil (theorem4ScaleMaxRatio F D T)) * T ≤
      chromatic (F.induce ((Finset.univ : Finset (U : Set V)) : Set (U : Set V))) := by
    rw [hchrom]
    exact hχ
  have hWuniv := htop Finset.univ
    (by simpa [Woven.outerScale_zero, T] using hconnUniv)
    (by simpa [Woven.outerScale_zero, T] using hχUniv)
  have hW : Woven F T (3 * T) :=
    Woven.of_iso e
      (by simpa [Woven.outerScale_zero, T] using hWuniv)
  exact hW
end HadwigerLean.Deduction
