import HadwigerLean.Inseparability.StageMixedPaths
import HadwigerLean.Inseparability.RawModelTangency
import HadwigerLean.Inseparability.RawModelStage
import Mathlib.Tactic

/-!
# Indexing the mixed linkage by the raw-model path blocks

The mixed construction indexes old sources by a finite source set and
new sources by pairs. The raw model uses `(4p+1)x` ordered path slots.
An explicit equivalence aligns the three old-source blocks and the
final `H₃` blocks with that path partition.
-/

namespace HadwigerLean.Inseparability

def ciPathMixedEquiv {V : Type*} (p x : ℕ) (Z : Finset V)
    (source : Fin (3 * p * x) ≃ Z) :
    CIPathIndex p x ≃ Z ⊕ Fin ((p + 1) * x) :=
  (finCongr (by ring : (4 * p + 1) * x = 3 * p * x + (p + 1) * x)).trans
    ((finSumFinEquiv.symm).trans
      (Equiv.sumCongr source (Equiv.refl (Fin ((p + 1) * x)))))

def ciSourceBlock (p x : ℕ) (b : Fin (3 * p)) (r : Fin x) :
    Fin (3 * p * x) :=
  ⟨b.val * x + r.val, by
    have hb : b.val + 1 ≤ 3 * p := by omega
    calc
      b.val * x + r.val < b.val * x + x := Nat.add_lt_add_left r.isLt _
      _ = (b.val + 1) * x := by ring
      _ ≤ (3 * p) * x := Nat.mul_le_mul_right x hb⟩

theorem ciPathMixedEquiv_source_block {V : Type*}
    (p x : ℕ) (Z : Finset V)
    (source : Fin (3 * p * x) ≃ Z)
    (b : Fin (3 * p)) (r : Fin x) :
    ciPathMixedEquiv p x Z source
      (finProdFinEquiv
        ((⟨b.val, by omega⟩ : Fin (4 * p + 1)), r)) =
      Sum.inl (source (ciSourceBlock p x b r)) := by
  have hleft :
      (finCongr (by ring : (4 * p + 1) * x =
        3 * p * x + (p + 1) * x))
        (finProdFinEquiv
          ((⟨b.val, by omega⟩ : Fin (4 * p + 1)), r)) =
      Fin.castAdd ((p + 1) * x) (ciSourceBlock p x b r) := by
    apply Fin.ext
    simp [ciSourceBlock, finProdFinEquiv, Nat.mul_comm]
    omega
  simp only [ciPathMixedEquiv, Equiv.trans_apply, hleft,
    finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply]
  rfl






theorem ciPathMixedEquiv_final_block {V : Type*}
    (p x : ℕ) (Z : Finset V)
    (source : Fin (3 * p * x) ≃ Z)
    (b : Fin (p + 1)) (r : Fin x) :
    ciPathMixedEquiv p x Z source
      (finProdFinEquiv
        ((⟨3 * p + b.val, by omega⟩ : Fin (4 * p + 1)), r)) =
      Sum.inr (finProdFinEquiv (b,r)) := by
  have hright :
      (finCongr (by ring : (4 * p + 1) * x =
        3 * p * x + (p + 1) * x))
        (finProdFinEquiv
          ((⟨3 * p + b.val, by omega⟩ : Fin (4 * p + 1)), r)) =
      Fin.natAdd (3 * p * x) (finProdFinEquiv (b,r)) := by
    apply Fin.ext
    simp [finProdFinEquiv]
    ring
  simp only [ciPathMixedEquiv, Equiv.trans_apply, hright,
    finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply]
  rfl



theorem ciPathMixedEquiv_final {V : Type*}
    (p x : ℕ) (Z : Finset V)
    (source : Fin (3 * p * x) ≃ Z)
    (z : CIRawIndex p x) :
    ciPathMixedEquiv p x Z source (ciFinalIndex p x z) =
      Sum.inr ((ciStageIndexEquiv p x).symm z) := by
  cases z with
  | inl z =>
      obtain ⟨i,r⟩ := z
      have h := ciPathMixedEquiv_final_block p x Z source
        (Fin.castSucc i) r
      have hindex :
          ciStageIndexEquiv p x
            (finProdFinEquiv (Fin.castSucc i,r)) =
              Sum.inl (i,r) := by
        have hleft :
            (finCongr (by simp [add_mul] :
              (p + 1) * x = p * x + x))
              (finProdFinEquiv (Fin.castSucc i,r)) =
                Fin.castAdd x (finProdFinEquiv (i,r)) := by
          apply Fin.ext
          simp [finProdFinEquiv]
        simp only [ciStageIndexEquiv, Equiv.trans_apply, hleft,
          finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply]
        simp
      have hinv :
          (ciStageIndexEquiv p x).symm (Sum.inl (i,r)) =
            finProdFinEquiv (Fin.castSucc i,r) :=
        (ciStageIndexEquiv p x).symm_apply_eq.mpr hindex.symm
      simpa [ciFinalIndex, hinv] using h
  | inr r =>
      have h := ciPathMixedEquiv_final_block p x Z source
        (Fin.last p) r
      have hindex :
          ciStageIndexEquiv p x
            (finProdFinEquiv (Fin.last p,r)) =
              Sum.inr r := by
        have hright :
            (finCongr (by simp [add_mul] :
              (p + 1) * x = p * x + x))
              (finProdFinEquiv (Fin.last p,r)) =
                Fin.natAdd (p * x) r := by
          apply Fin.ext
          simp [finProdFinEquiv]
          ring
        simp only [ciStageIndexEquiv, Equiv.trans_apply, hright,
          finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply]
        simp
      have hinv :
          (ciStageIndexEquiv p x).symm (Sum.inr r) =
            finProdFinEquiv (Fin.last p,r) :=
        (ciStageIndexEquiv p x).symm_apply_eq.mpr hindex.symm
      have hblock :
          (⟨3 * p + (Fin.last p).val, by omega⟩ : Fin (4 * p + 1)) =
            ⟨4 * p, by omega⟩ := by
        apply Fin.ext
        simp [Fin.val_last]
        omega
      rw [hblock] at h
      simpa [ciFinalIndex, hinv] using h

theorem ciPathMixedEquiv_old_start {V : Type*}
    (p x : ℕ) (Z : Finset V)
    (source : Fin (3 * p * x) ≃ Z)
    (i : Fin p) (r : Fin x) :
    ciPathMixedEquiv p x Z source (ciOldStartIndex p x i r) =
      Sum.inl (source
        (ciSourceBlock p x ⟨i.val, by omega⟩ r)) := by
  simpa [ciOldStartIndex] using
    ciPathMixedEquiv_source_block p x Z source
      (⟨i.val, by omega⟩ : Fin (3 * p)) r

theorem ciPathMixedEquiv_old_middle {V : Type*}
    (p x : ℕ) (Z : Finset V)
    (source : Fin (3 * p * x) ≃ Z)
    (i : Fin p) (r : Fin x) :
    ciPathMixedEquiv p x Z source (ciOldMiddleIndex p x i r) =
      Sum.inl (source
        (ciSourceBlock p x ⟨p + 2 * i.val, by omega⟩ r)) := by
  simpa [ciOldMiddleIndex] using
    ciPathMixedEquiv_source_block p x Z source
      (⟨p + 2 * i.val, by omega⟩ : Fin (3 * p)) r

theorem ciPathMixedEquiv_new_middle {V : Type*}
    (p x : ℕ) (Z : Finset V)
    (source : Fin (3 * p * x) ≃ Z)
    (i : Fin p) (r : Fin x) :
    ciPathMixedEquiv p x Z source (ciNewMiddleIndex p x i r) =
      Sum.inl (source
        (ciSourceBlock p x ⟨p + 2 * i.val + 1, by omega⟩ r)) := by
  simpa [ciNewMiddleIndex] using
    ciPathMixedEquiv_source_block p x Z source
      (⟨p + 2 * i.val + 1, by omega⟩ : Fin (3 * p)) r

theorem ciPathMixedEquiv_inr_is_final {V : Type*}
    (p x : ℕ) (Z : Finset V)
    (source : Fin (3 * p * x) ≃ Z)
    (k : CIPathIndex p x) (i : Fin ((p + 1) * x))
    (hki : ciPathMixedEquiv p x Z source k = Sum.inr i) :
    k = ciFinalIndex p x (pathOwner p x k) := by
  have hfirst :
      k = ciFinalIndex p x (ciStageIndexEquiv p x i) := by
    apply (ciPathMixedEquiv p x Z source).injective
    rw [hki, ciPathMixedEquiv_final]
    simp
  rw [hfirst, pathOwner_finalIndex]

end HadwigerLean.Inseparability
