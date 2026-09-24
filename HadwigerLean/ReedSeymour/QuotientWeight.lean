import HadwigerLean.ReedSeymour.Egg
import HadwigerLean.ReedSeymour.FiniteAveraging

/-!
# Extracting a weighted stable set from a colored egg quotient

The egg-decomposition theorem supplies a connected partition whose every block
has a yolk. Once its touching quotient is colored, one color class of yolks is
a stable set of the original graph. This module proves the finite bookkeeping
and the weighted inequality independently of the construction of the partition.
-/

namespace HadwigerLean

open Finset

namespace ConnectedPartition

variable {V I : Type*} [Fintype V] [Fintype I] {G : SimpleGraph V}

/-- The unique block containing a vertex. -/
noncomputable def owner (P : ConnectedPartition G I) (v : V) : I :=
  Classical.choose (P.cover v)

omit [Fintype V] [Fintype I] in
theorem owner_mem (P : ConnectedPartition G I) (v : V) :
    v ∈ P.block (P.owner v) :=
  Classical.choose_spec (P.cover v)

omit [Fintype V] [Fintype I] in
theorem mem_block_iff_owner_eq (P : ConnectedPartition G I) (v : V) (i : I) :
    v ∈ P.block i ↔ P.owner v = i := by
  obtain ⟨j, hj, huniq⟩ := P.existsUnique_block v
  have ho : P.owner v = j := huniq _ (P.owner_mem v)
  constructor
  · intro hi
    exact ho.trans (huniq i hi).symm
  · intro h
    rw [← h]
    exact P.owner_mem v

/-- The weights of partition blocks sum to the weight of the graph. -/
theorem sum_setWeight_blocks (P : ConnectedPartition G I) (w : V → ℝ) :
    (∑ i, setWeight w (P.block i)) = ∑ v, w v := by
  classical
  simp only [setWeight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp [P.mem_block_iff_owner_eq]

/-- The selected yolks in one quotient color class. -/
def classYolk {C : Type*} (P : ConnectedPartition G I)
    (Y : I → Set V) (color : I → C) (c : C) : Set V :=
  {v | v ∈ Y (P.owner v) ∧ color (P.owner v) = c}

omit [Fintype V] [Fintype I] in
theorem classYolk_independent {C : Type*} (P : ConnectedPartition G I)
    (Y : I → Set V) (hY : ∀ i, G.IsIndepSet (Y i))
    (color : I → C)
    (hcolor : ∀ {i j}, P.touchingQuotient.Adj i j → color i ≠ color j)
    (c : C) : G.IsIndepSet (P.classYolk Y color c) := by
  intro v hv u hu hvu hadj
  change v ∈ Y (P.owner v) ∧ color (P.owner v) = c at hv
  change u ∈ Y (P.owner u) ∧ color (P.owner u) = c at hu
  by_cases hsame : P.owner v = P.owner u
  · exact hY (P.owner v) hv.1 (hsame ▸ hu.1) hvu hadj
  · have hq : P.touchingQuotient.Adj (P.owner v) (P.owner u) :=
      ⟨hsame, v, P.owner_mem v, u, P.owner_mem u, hadj⟩
    exact (hcolor hq) (hv.2.trans hu.2.symm)

theorem sum_setWeight_yolks_color {C : Type*} [DecidableEq C]
    (P : ConnectedPartition G I) (w : V → ℝ)
    (Y : I → Set V) (hY : ∀ i, Y i ⊆ P.block i)
    (color : I → C) (c : C) :
    (∑ i, if color i = c then setWeight w (Y i) else 0) =
      setWeight w (P.classYolk Y color c) := by
  classical
  calc
    (∑ i, if color i = c then setWeight w (Y i) else 0) =
        ∑ i, ∑ v, if color i = c then (if v ∈ Y i then w v else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hc : color i = c <;> simp [setWeight, hc]
    _ = ∑ v, ∑ i, if color i = c then (if v ∈ Y i then w v else 0) else 0 :=
      Finset.sum_comm
    _ = setWeight w (P.classYolk Y color c) := by
      unfold setWeight
      apply Finset.sum_congr rfl
      intro v _
      have hno (i : I) (hi : i ≠ P.owner v) : v ∉ Y i := by
        intro hv
        have hown := (P.mem_block_iff_owner_eq v i).1 (hY i hv)
        exact hi hown.symm
      have hsingle :
          (∑ i, if color i = c then (if v ∈ Y i then w v else 0) else 0) =
            if color (P.owner v) = c then
              (if v ∈ Y (P.owner v) then w v else 0) else 0 := by
        apply Finset.sum_eq_single (P.owner v)
        · intro i _ hi
          simp [hno i hi]
        · intro h
          exact False.elim (h (Finset.mem_univ _))
      rw [hsingle]
      by_cases hy : v ∈ Y (P.owner v) <;>
        by_cases hc : color (P.owner v) = c <;>
          simp [classYolk, hy, hc]

end ConnectedPartition

variable {V I : Type*} [Fintype V] [Fintype I] [Nonempty I]
  {G : SimpleGraph V}

/-- A colored touching quotient of an egg partition yields the weighted stable
set required in Reed--Seymour's LP-duality argument. -/
theorem exists_weighted_stable_set_of_colored_egg_partition
    (P : ConnectedPartition G I) (w : V → ℝ)
    (hEgg : ∀ i, IsEgg G w (P.block i))
    {n : ℕ} (hColor : P.touchingQuotient.Colorable n) :
    ∃ S : Set V, G.IsIndepSet S ∧
      (∑ v, w v) ≤ 2 * (n : ℝ) * setWeight w S := by
  classical
  let col : P.touchingQuotient.Coloring (Fin n) := Classical.choice hColor
  let i₀ : I := Classical.choice inferInstance
  letI : Nonempty (Fin n) := ⟨col i₀⟩
  let Y : I → Set V := fun i => Classical.choose ((hEgg i).has_yolk)
  have hY (i : I) : IsYolk G w (P.block i) (Y i) :=
    Classical.choose_spec ((hEgg i).has_yolk)
  have hvalid : ∀ {i j}, P.touchingQuotient.Adj i j → col i ≠ col j := by
    intro i j hij
    exact col.valid hij
  obtain ⟨c, hc⟩ := exists_color_class_half_weight
    (fun i => col i)
    (fun i => setWeight w (P.block i))
    (fun i => setWeight w (Y i))
    (fun i => (hY i).half_weight)
  let S : Set V := P.classYolk Y (fun i => col i) c
  have hs : G.IsIndepSet S :=
    P.classYolk_independent Y (fun i => (hY i).stable)
      (fun i => col i) hvalid c
  refine ⟨S, hs, ?_⟩
  have hblocks := P.sum_setWeight_blocks w
  have hyolks := P.sum_setWeight_yolks_color w Y
    (fun i => (hY i).subset) (fun i => col i) c
  calc
    (∑ v, w v) = ∑ i, setWeight w (P.block i) := hblocks.symm
    _ ≤ 2 * (n : ℝ) *
          ∑ i, if col i = c then setWeight w (Y i) else 0 := by
            simpa using hc
    _ = 2 * (n : ℝ) * setWeight w S := by rw [hyolks]
/-- A finite representation of a vertex subset. -/
noncomputable def setFinset {U : Type*} [Fintype U] (S : Set U) : Finset U := by
  classical
  exact Finset.univ.filter (fun v => v ∈ S)

@[simp] theorem mem_setFinset {U : Type*} [Fintype U] (S : Set U) (v : U) :
    v ∈ setFinset S ↔ v ∈ S := by
  classical
  simp [setFinset]

/-- A vertex-set weight equals the corresponding finite sum. -/
theorem setWeight_eq_sum_toFinset {U : Type*} [Fintype U]
    (w : U → ℝ) (S : Set U) :
    setWeight w S = ∑ v ∈ setFinset S, w v := by
  classical
  simp [setWeight, setFinset, Finset.sum_filter]
/-- Finset formulation of the weighted stable-set extraction. -/
theorem exists_weighted_stable_finset_of_colored_egg_partition
    (P : ConnectedPartition G I) (w : V → ℝ)
    (hEgg : ∀ i, IsEgg G w (P.block i))
    {n : ℕ} (hColor : P.touchingQuotient.Colorable n) :
    ∃ s : Finset V, G.IsIndepSet (s : Set V) ∧
      (∑ v, w v) ≤ 2 * (n : ℝ) * ∑ v ∈ s, w v := by
  classical
  obtain ⟨S, hstable, hbound⟩ :=
    exists_weighted_stable_set_of_colored_egg_partition P w hEgg hColor
  refine ⟨setFinset S, ?_, ?_⟩
  · simpa [setFinset] using hstable
  · simpa only [setWeight_eq_sum_toFinset] using hbound
end HadwigerLean