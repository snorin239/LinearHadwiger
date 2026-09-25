import HadwigerLean.Woven.OuterScales
import Mathlib.Tactic

/-!
# The three-child overlap argument

Each parent root uses two connector paths whose indices differ by the
parent scale. Their endpoints land in different child blocks. Two pairs
of distinct children among three always share a child, supplying the
model edge between their rooted branches.
-/

namespace HadwigerLean
namespace Woven

/-- The block of length `c` containing an index in the first three blocks. -/
def childBlock (c i : ℕ) : Fin 3 :=
  if i < c then 0 else if i < 2 * c then 1 else 2

/-- Two indices separated by at least one child block land in different
blocks, provided both indices lie in the first three blocks. -/
theorem childBlock_ne_of_gap {c a i : ℕ}
    (hc : 0 < c) (hgap : c ≤ a)
    (hi : i < a) (hbound : a + i < 3 * c) :
    childBlock c i ≠ childBlock c (a + i) := by
  intro heq
  unfold childBlock at heq
  split_ifs at heq <;> simp_all <;> omega

/-- The two connectors assigned to one parent root belong to distinct
children at an exact integer scale step. -/
theorem childBlock_ne_for_parent_pair {m i j : ℕ}
    (hi : i < m) (hj : j < outerScale m i) :
    childBlock (outerScale m (i + 1)) j ≠
      childBlock (outerScale m (i + 1)) (outerScale m i + j) := by
  have hc := outerScale_pos m (i + 1)
  have hp := outerScale_pos m i
  have hstep := outerScale_child m i hi
  have hle : outerScale m (i + 1) ≤ outerScale m i := by omega
  apply childBlock_ne_of_gap hc hle hj
  omega

/-- Any two sets of at least two of the three child indices intersect. -/
theorem two_children_intersect (S T : Finset (Fin 3))
    (hS : 2 ≤ S.card) (hT : 2 ≤ T.card) :
    ∃ k : Fin 3, k ∈ S ∧ k ∈ T := by
  classical
  by_contra hnone
  have hdis : Disjoint S T := Finset.disjoint_left.mpr (by
    intro k hkS hkT
    exact hnone ⟨k, hkS, hkT⟩)
  have hcard : (S ∪ T).card = S.card + T.card :=
    Finset.card_union_of_disjoint hdis
  have hbound : (S ∪ T).card ≤ 3 := by
    calc
      (S ∪ T).card ≤ (Finset.univ : Finset (Fin 3)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = 3 := by simp
  omega

/-- The child pair used by a parent root. -/
def parentChildPair (c a j : ℕ) : Finset (Fin 3) :=
  {childBlock c j, childBlock c (a + j)}

/-- Any two parent branches assembled from two child models share at
least one child model. -/
theorem parentChildPair_intersect {c a i j : ℕ}
    (hc : 0 < c) (hca : c ≤ a)
    (hi : i < a) (hj : j < a)
    (hibound : a + i < 3 * c)
    (hjbound : a + j < 3 * c) :
    ∃ k : Fin 3, k ∈ parentChildPair c a i ∧
      k ∈ parentChildPair c a j := by
  classical
  have hni := childBlock_ne_of_gap hc hca hi hibound
  have hnj := childBlock_ne_of_gap hc hca hj hjbound
  have hci : 2 ≤ (parentChildPair c a i).card := by
    simp [parentChildPair, hni]
  have hcj : 2 ≤ (parentChildPair c a j).card := by
    simp [parentChildPair, hnj]
  exact two_children_intersect _ _ hci hcj

end Woven
end HadwigerLean