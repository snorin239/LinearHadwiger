import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Terminal-group indexing for the chromatic inseparability induction

With `p` previous groups of `x` branches, the path family has
`(4p+1)x` indices. We use the product coordinates `(block, offset)`.
Three blocks belong to each old branch, and `p+1` blocks to each new
branch. The owner map gives an exact partition without quotienting
one-based paper indices.
-/

namespace HadwigerLean.Inseparability

/-- The four kinds of blocks are assigned to old or new terminal groups. -/
def blockOwner (p : ℕ) (k : Fin (4 * p + 1)) : Sum (Fin p) Unit :=
  if h₀ : k.val < p then
    Sum.inl ⟨k.val, h₀⟩
  else if h₁ : k.val < 3 * p then
    if h₂ : (k.val - p) % 2 = 0 then
      Sum.inl ⟨(k.val - p) / 2, by omega⟩
    else
      Sum.inr ⟨⟩
  else if h₃ : k.val < 4 * p then
    Sum.inl ⟨k.val - 3 * p, by omega⟩
  else
    Sum.inr ⟨⟩

/-- A path index is owned by one old branch `(i,r)` or one new branch `r`. -/
def pathOwner (p x : ℕ) (k : Fin ((4 * p + 1) * x)) :
    Sum (Fin p × Fin x) (Fin x) :=
  let z := finProdFinEquiv.symm k
  match blockOwner p z.1 with
  | Sum.inl i => Sum.inl (i, z.2)
  | Sum.inr _ => Sum.inr z.2

/-- The three terminal indices for an old branch are one old tangent,
one first-half auxiliary-graph source, and one old H3 source. -/
def oldTerminals (p x : ℕ) (i : Fin p) (r : Fin x) :
    Finset (Fin ((4 * p + 1) * x)) :=
  Finset.univ.filter (fun k => pathOwner p x k = Sum.inl (i, r))

/-- New branches use each second-half auxiliary-graph source and one new
H3 source. -/
def newTerminals (p x : ℕ) (r : Fin x) :
    Finset (Fin ((4 * p + 1) * x)) :=
  Finset.univ.filter (fun k => pathOwner p x k = Sum.inr r)

/-- Every path index belongs to exactly one old or new terminal group. -/
theorem path_index_has_unique_group (p x : ℕ)
    (k : Fin ((4 * p + 1) * x)) :
    (∃! z : Fin p × Fin x, k ∈ oldTerminals p x z.1 z.2) ∨
      (∃! r : Fin x, k ∈ newTerminals p x r) := by
  cases h : pathOwner p x k with
  | inl z =>
      left
      refine ⟨z, ?_, ?_⟩
      · simp [oldTerminals, h]
      · intro w hw
        have heq : z = w := by simpa [oldTerminals, h] using hw
        exact heq.symm
  | inr r =>
      right
      refine ⟨r, ?_, ?_⟩
      · simp [newTerminals, h]
      · intro w hw
        have heq : r = w := by simpa [newTerminals, h] using hw
        exact heq.symm

/-- Distinct terminal groups are disjoint. -/
theorem oldTerminals_disjoint (p x : ℕ)
    (z w : Fin p × Fin x) (hzw : z ≠ w) :
    Disjoint (oldTerminals p x z.1 z.2)
      (oldTerminals p x w.1 w.2) := by
  apply Finset.disjoint_left.mpr
  intro k hkz hkw
  have hz : pathOwner p x k = Sum.inl z :=
    (Finset.mem_filter.mp hkz).2
  have hw : pathOwner p x k = Sum.inl w :=
    (Finset.mem_filter.mp hkw).2
  exact hzw (Sum.inl.inj (hz.symm.trans hw))

theorem newTerminals_disjoint (p x : ℕ)
    (r s : Fin x) (hrs : r ≠ s) :
    Disjoint (newTerminals p x r) (newTerminals p x s) := by
  apply Finset.disjoint_left.mpr
  intro k hkr hks
  have hr : pathOwner p x k = Sum.inr r :=
    (Finset.mem_filter.mp hkr).2
  have hs : pathOwner p x k = Sum.inr s :=
    (Finset.mem_filter.mp hks).2
  exact hrs (Sum.inr.inj (hr.symm.trans hs))

theorem oldTerminals_disjoint_newTerminals (p x : ℕ)
    (z : Fin p × Fin x) (r : Fin x) :
    Disjoint (oldTerminals p x z.1 z.2) (newTerminals p x r) := by
  apply Finset.disjoint_left.mpr
  intro k hkz hkr
  have hz : pathOwner p x k = Sum.inl z :=
    (Finset.mem_filter.mp hkz).2
  have hr : pathOwner p x k = Sum.inr r :=
    (Finset.mem_filter.mp hkr).2
  exact Sum.inl_ne_inr (hz.symm.trans hr)

/-- The first block of each old group carries its old tangent source. -/
theorem blockOwner_old_start (p : ℕ) (i : Fin p) :
    blockOwner p ⟨i.val, by omega⟩ = Sum.inl i := by
  simp [blockOwner, i.isLt]

/-- The even middle blocks carry first-half auxiliary-graph sources. -/
theorem blockOwner_old_middle (p : ℕ) (i : Fin p) :
    blockOwner p ⟨p + 2 * i.val, by omega⟩ = Sum.inl i := by
  have h₀ : ¬ p + 2 * i.val < p := by omega
  have h₁ : p + 2 * i.val < 3 * p := by omega
  have h₂ : (p + 2 * i.val - p) % 2 = 0 := by omega
  simp only [blockOwner, h₀, dite_false, h₁, dite_true, h₂]
  apply congrArg Sum.inl
  apply Fin.ext
  simp only []
  omega

/-- The final old blocks carry old H3 sources. -/
theorem blockOwner_old_final (p : ℕ) (i : Fin p) :
    blockOwner p ⟨3 * p + i.val, by omega⟩ = Sum.inl i := by
  have h₀ : ¬ 3 * p + i.val < p := by omega
  have h₁ : ¬ 3 * p + i.val < 3 * p := by omega
  have h₂ : 3 * p + i.val < 4 * p := by omega
  simp only [blockOwner, h₀, dite_false, h₁, h₂, dite_true]
  apply congrArg Sum.inl
  apply Fin.ext
  simp only []
  omega

/-- Odd middle blocks carry the new branch with the same offset. -/
theorem blockOwner_new_middle (p : ℕ) (i : Fin p) :
    blockOwner p ⟨p + 2 * i.val + 1, by omega⟩ = Sum.inr () := by
  have h₀ : ¬ p + 2 * i.val + 1 < p := by omega
  have h₁ : p + 2 * i.val + 1 < 3 * p := by omega
  have h₂ : (p + 2 * i.val + 1 - p) % 2 ≠ 0 := by omega
  simp [blockOwner, h₀, h₁, h₂]

/-- The last block carries the last source for every new branch. -/
theorem blockOwner_new_final (p : ℕ) :
    blockOwner p ⟨4 * p, by omega⟩ = Sum.inr () := by
  have h₀ : ¬ 4 * p < p := by omega
  have h₁ : ¬ 4 * p < 3 * p := by omega
  have h₂ : ¬ 4 * p < 4 * p := by omega
  simp [blockOwner, h₀, h₁]
/-- An old group owns exactly its three prescribed block numbers. -/
theorem blockOwner_eq_old_iff (p : ℕ) (k : Fin (4 * p + 1))
    (i : Fin p) :
    blockOwner p k = Sum.inl i ↔
      k.val = i.val ∨
      k.val = p + 2 * i.val ∨
      k.val = 3 * p + i.val := by
  constructor
  · intro h
    unfold blockOwner at h
    split_ifs at h with h₀ h₁ h₂ h₃
    · left
      exact congrArg Fin.val (Sum.inl.inj h)
    · right
      left
      have heq := congrArg Fin.val (Sum.inl.inj h)
      change (k.val - p) / 2 = i.val at heq
      omega
    · right
      right
      have heq := congrArg Fin.val (Sum.inl.inj h)
      change k.val - 3 * p = i.val at heq
      omega
  · rintro (h | h | h)
    · have hk : k = ⟨i.val, by omega⟩ := Fin.ext h
      rw [hk]
      exact blockOwner_old_start p i
    · have hk : k = ⟨p + 2 * i.val, by omega⟩ := Fin.ext h
      rw [hk]
      exact blockOwner_old_middle p i
    · have hk : k = ⟨3 * p + i.val, by omega⟩ := Fin.ext h
      rw [hk]
      exact blockOwner_old_final p i
/-- A new group owns the odd middle blocks and the final block. -/
theorem blockOwner_eq_new_iff (p : ℕ) (k : Fin (4 * p + 1)) :
    blockOwner p k = Sum.inr () ↔
      (∃ i : Fin p, k.val = p + 2 * i.val + 1) ∨
      k.val = 4 * p := by
  constructor
  · intro h
    unfold blockOwner at h
    split_ifs at h with h₀ h₁ h₂ h₃
    · left
      let i : Fin p := ⟨(k.val - p) / 2, by omega⟩
      refine ⟨i, ?_⟩
      change k.val = p + 2 * ((k.val - p) / 2) + 1
      omega
    · right
      omega
  · rintro (⟨i, h⟩ | h)
    · have hk : k = ⟨p + 2 * i.val + 1, by omega⟩ := Fin.ext h
      rw [hk]
      exact blockOwner_new_middle p i
    · have hk : k = ⟨4 * p, by omega⟩ := Fin.ext h
      rw [hk]
      exact blockOwner_new_final p
private theorem pathOwner_eq_old_iff (p x : ℕ)
    (k : Fin ((4 * p + 1) * x)) (i : Fin p) (r : Fin x) :
    pathOwner p x k = Sum.inl (i, r) ↔
      blockOwner p (finProdFinEquiv.symm k).1 = Sum.inl i ∧
      (finProdFinEquiv.symm k).2 = r := by
  unfold pathOwner
  cases h : blockOwner p (finProdFinEquiv.symm k).1 with
  | inl j =>
      change blockOwner p k.divNat = Sum.inl j at h
      simp [h, Prod.mk.injEq]
  | inr u =>
      change blockOwner p k.divNat = Sum.inr u at h
      simp [h]

private theorem pathOwner_eq_new_iff (p x : ℕ)
    (k : Fin ((4 * p + 1) * x)) (r : Fin x) :
    pathOwner p x k = Sum.inr r ↔
      blockOwner p (finProdFinEquiv.symm k).1 = Sum.inr () ∧
      (finProdFinEquiv.symm k).2 = r := by
  unfold pathOwner
  cases h : blockOwner p (finProdFinEquiv.symm k).1 with
  | inl j =>
      change blockOwner p k.divNat = Sum.inl j at h
      simp [h]
  | inr u =>
      change blockOwner p k.divNat = Sum.inr u at h
      simp [h]
/-- Product-coordinate path indices realize the paper's three old slots. -/
theorem pathOwner_old_start (p x : ℕ) (i : Fin p) (r : Fin x) :
    pathOwner p x (finProdFinEquiv ((⟨i.val, by omega⟩ : Fin (4 * p + 1)), r)) =
      Sum.inl (i, r) := by
  simp [pathOwner, blockOwner_old_start]

theorem pathOwner_old_middle (p x : ℕ) (i : Fin p) (r : Fin x) :
    pathOwner p x
      (finProdFinEquiv ((⟨p + 2 * i.val, by omega⟩ : Fin (4 * p + 1)), r)) =
      Sum.inl (i, r) := by
  simp [pathOwner, blockOwner_old_middle]

theorem pathOwner_old_final (p x : ℕ) (i : Fin p) (r : Fin x) :
    pathOwner p x
      (finProdFinEquiv ((⟨3 * p + i.val, by omega⟩ : Fin (4 * p + 1)), r)) =
      Sum.inl (i, r) := by
  simp [pathOwner, blockOwner_old_final]

/-- Product-coordinate path indices realize the paper's new slots. -/
theorem pathOwner_new_middle (p x : ℕ) (i : Fin p) (r : Fin x) :
    pathOwner p x
      (finProdFinEquiv (⟨p + 2 * i.val + 1, by omega⟩, r)) =
      Sum.inr r := by
  simp [pathOwner, blockOwner_new_middle]

theorem pathOwner_new_final (p x : ℕ) (r : Fin x) :
    pathOwner p x (finProdFinEquiv (⟨4 * p, by omega⟩, r)) =
      Sum.inr r := by
  simp [pathOwner, blockOwner_new_final]
/-- The old terminal group consists of exactly its three paper slots. -/
theorem oldTerminals_eq_three (p x : ℕ) (i : Fin p) (r : Fin x) :
    oldTerminals p x i r =
      { finProdFinEquiv ((⟨i.val, by omega⟩ : Fin (4 * p + 1)), r),
        finProdFinEquiv ((⟨p + 2 * i.val, by omega⟩ : Fin (4 * p + 1)), r),
        finProdFinEquiv ((⟨3 * p + i.val, by omega⟩ : Fin (4 * p + 1)), r) } := by
  ext k
  simp only [oldTerminals, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hk
    obtain ⟨hb, hr⟩ := (pathOwner_eq_old_iff p x k i r).mp hk
    rcases (blockOwner_eq_old_iff p (finProdFinEquiv.symm k).1 i).mp hb with
      h | h | h
    · left
      have hz : finProdFinEquiv.symm k =
          (⟨i.val, by omega⟩, r) :=
        Prod.ext (Fin.ext h) hr
      calc
        k = finProdFinEquiv (finProdFinEquiv.symm k) :=
          (finProdFinEquiv.apply_symm_apply k).symm
        _ = finProdFinEquiv ((⟨i.val, by omega⟩ : Fin (4 * p + 1)), r) := by rw [hz]
    · right
      left
      have hz : finProdFinEquiv.symm k =
          (⟨p + 2 * i.val, by omega⟩, r) :=
        Prod.ext (Fin.ext h) hr
      calc
        k = finProdFinEquiv (finProdFinEquiv.symm k) :=
          (finProdFinEquiv.apply_symm_apply k).symm
        _ = finProdFinEquiv ((⟨p + 2 * i.val, by omega⟩ : Fin (4 * p + 1)), r) := by rw [hz]
    · right
      right
      have hz : finProdFinEquiv.symm k =
          (⟨3 * p + i.val, by omega⟩, r) :=
        Prod.ext (Fin.ext h) hr
      calc
        k = finProdFinEquiv (finProdFinEquiv.symm k) :=
          (finProdFinEquiv.apply_symm_apply k).symm
        _ = finProdFinEquiv ((⟨3 * p + i.val, by omega⟩ : Fin (4 * p + 1)), r) := by rw [hz]
  · rintro (rfl | rfl | rfl)
    · exact pathOwner_old_start p x i r
    · exact pathOwner_old_middle p x i r
    · exact pathOwner_old_final p x i r

/-- Each old terminal group has cardinality three. -/
theorem oldTerminals_card (p x : ℕ) (i : Fin p) (r : Fin x) :
    (oldTerminals p x i r).card = 3 := by
  rw [oldTerminals_eq_three]
  have h₀₁ : (⟨i.val, by omega⟩ : Fin (4 * p + 1)) ≠
      ⟨p + 2 * i.val, by omega⟩ := by
    intro h
    have hh := congrArg Fin.val h
    simp only [] at hh
    omega
  have h₀₂ : (⟨i.val, by omega⟩ : Fin (4 * p + 1)) ≠
      ⟨3 * p + i.val, by omega⟩ := by
    intro h
    have hh := congrArg Fin.val h
    simp only [] at hh
    omega
  have h₁₂ : (⟨p + 2 * i.val, by omega⟩ : Fin (4 * p + 1)) ≠
      ⟨3 * p + i.val, by omega⟩ := by
    intro h
    have hh := congrArg Fin.val h
    simp only [] at hh
    omega
  have hslot₀₁ : finProdFinEquiv ((⟨i.val, by omega⟩ : Fin (4 * p + 1)), r) ≠
      finProdFinEquiv ((⟨p + 2 * i.val, by omega⟩ : Fin (4 * p + 1)), r) := by
    intro h
    exact h₀₁ (congrArg Prod.fst (finProdFinEquiv.injective h))
  have hslot₀₂ : finProdFinEquiv ((⟨i.val, by omega⟩ : Fin (4 * p + 1)), r) ≠
      finProdFinEquiv ((⟨3 * p + i.val, by omega⟩ : Fin (4 * p + 1)), r) := by
    intro h
    exact h₀₂ (congrArg Prod.fst (finProdFinEquiv.injective h))
  have hslot₁₂ : finProdFinEquiv ((⟨p + 2 * i.val, by omega⟩ : Fin (4 * p + 1)), r) ≠
      finProdFinEquiv ((⟨3 * p + i.val, by omega⟩ : Fin (4 * p + 1)), r) := by
    intro h
    exact h₁₂ (congrArg Prod.fst (finProdFinEquiv.injective h))
  simp [hslot₀₁, hslot₀₂, hslot₁₂]
/-- The new terminal group consists of one odd middle slot per old
auxiliary graph and one final H3 slot. -/
theorem newTerminals_eq (p x : ℕ) (r : Fin x) :
    newTerminals p x r =
      insert (finProdFinEquiv ((⟨4 * p, by omega⟩ : Fin (4 * p + 1)), r))
        (Finset.univ.image (fun i : Fin p =>
          finProdFinEquiv
            ((⟨p + 2 * i.val + 1, by omega⟩ : Fin (4 * p + 1)), r))) := by
  ext k
  simp only [newTerminals, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_image]
  constructor
  · intro hk
    obtain ⟨hb, hr⟩ := (pathOwner_eq_new_iff p x k r).mp hk
    rcases (blockOwner_eq_new_iff p (finProdFinEquiv.symm k).1).mp hb with
      ⟨i, h⟩ | h
    · right
      refine ⟨i, ?_⟩
      have hz : finProdFinEquiv.symm k =
          ((⟨p + 2 * i.val + 1, by omega⟩ : Fin (4 * p + 1)), r) :=
        Prod.ext (Fin.ext h) hr
      symm
      calc
        k = finProdFinEquiv (finProdFinEquiv.symm k) :=
          (finProdFinEquiv.apply_symm_apply k).symm
        _ = finProdFinEquiv
            ((⟨p + 2 * i.val + 1, by omega⟩ : Fin (4 * p + 1)), r) := by
              rw [hz]
    · left
      have hz : finProdFinEquiv.symm k =
          ((⟨4 * p, by omega⟩ : Fin (4 * p + 1)), r) :=
        Prod.ext (Fin.ext h) hr
      calc
        k = finProdFinEquiv (finProdFinEquiv.symm k) :=
          (finProdFinEquiv.apply_symm_apply k).symm
        _ = finProdFinEquiv ((⟨4 * p, by omega⟩ : Fin (4 * p + 1)), r) := by
              rw [hz]
  · rintro (rfl | ⟨i, rfl⟩)
    · exact pathOwner_new_final p x r
    · exact pathOwner_new_middle p x i r

/-- A new terminal group has `p+1` members. -/
theorem newTerminals_card (p x : ℕ) (r : Fin x) :
    (newTerminals p x r).card = p + 1 := by
  rw [newTerminals_eq]
  have hinj : Function.Injective
      (fun i : Fin p => finProdFinEquiv
        ((⟨p + 2 * i.val + 1, by omega⟩ : Fin (4 * p + 1)), r)) := by
    intro i j hij
    have hblock := congrArg Prod.fst (finProdFinEquiv.injective hij)
    have hh := congrArg Fin.val hblock
    simp only [] at hh
    exact Fin.ext (by omega)
  have hnot : finProdFinEquiv ((⟨4 * p, by omega⟩ : Fin (4 * p + 1)), r) ∉
      Finset.univ.image (fun i : Fin p => finProdFinEquiv
        ((⟨p + 2 * i.val + 1, by omega⟩ : Fin (4 * p + 1)), r)) := by
    intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    have hblock := congrArg Prod.fst (finProdFinEquiv.injective hi)
    have hh := congrArg Fin.val hblock
    simp only [] at hh
    omega
  rw [Finset.card_insert_of_notMem hnot]
  simp [Finset.card_image_of_injective _ hinj]
end HadwigerLean.Inseparability
