import HadwigerLean.ReedSeymour.Decomposition
import HadwigerLean.ReedSeymour.Absorption
import HadwigerLean.ReedSeymour.PathBipartite
import HadwigerLean.ReedSeymour.Reindex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Absorbing a central connector into a neighboring egg

This is the first quotient update in Reed--Seymour §2. A connected set `U`
from the central block is absorbed into one neighboring block. The rest of
the central block is divided into connected components. The statements below
separate this quotient operation from the parity and weight argument that
produces the absorbed egg.
-/

namespace HadwigerLean
namespace ReedSeymour

universe u v w

variable {V : Type v} {I : Type u} {J : Type w} {G : SimpleGraph V}

/-- Indices after deleting `i₀`, expanding `i₁`, and adding remainder blocks. -/
abbrev FusionIndex (I : Type u) (J : Type w) (i₀ i₁ : I) :=
  Sum {i : I // i ≠ i₀ ∧ i ≠ i₁} (Option J)

namespace CentralSplit

variable {P : ConnectedPartition G I} {i₀ : I}
variable (S : CentralSplit P i₀ J) (i₁ : I)

/-- The absorbed block is indexed by `none`; the remainder blocks by `some`. -/
def fusionBlock : FusionIndex I J i₀ i₁ → Set V
  | .inl i => P.block i.1
  | .inr none => P.block i₁ ∪ S.U
  | .inr (some j) => S.remainder j

/-- Absorbing `U` and splitting the remainder gives a connected partition. -/
def fusionPartition (hi : i₁ ≠ i₀)
    (hconn : (G.induce (P.block i₁ ∪ S.U)).Connected) :
    ConnectedPartition G (FusionIndex I J i₀ i₁) where
  block := S.fusionBlock i₁
  connected := by
    intro k
    cases k with
    | inl i => exact P.connected i.1
    | inr q =>
        cases q with
        | none => exact hconn
        | some j => exact S.remainder_connected j
  disjoint := by
    intro a b hab
    cases a with
    | inl i =>
        cases b with
        | inl j =>
            change Disjoint (P.block i.1) (P.block j.1)
            apply P.disjoint
            intro h
            exact hab (congrArg Sum.inl (Subtype.ext h))
        | inr q =>
            cases q with
            | none =>
                change Disjoint (P.block i.1) (P.block i₁ ∪ S.U)
                apply Set.disjoint_union_right.mpr
                exact ⟨P.disjoint i.2.2, (P.disjoint i.2.1).mono_right S.U_subset⟩
            | some j =>
                change Disjoint (P.block i.1) (S.remainder j)
                exact (P.disjoint i.2.1).mono_right (S.remainder_subset j)
    | inr q =>
        cases b with
        | inl i =>
            cases q with
            | none =>
                change Disjoint (P.block i₁ ∪ S.U) (P.block i.1)
                apply Set.disjoint_union_left.mpr
                exact ⟨P.disjoint i.2.2.symm,
                  (P.disjoint i.2.1.symm).mono_left S.U_subset⟩
            | some j =>
                change Disjoint (S.remainder j) (P.block i.1)
                exact (P.disjoint i.2.1.symm).mono_left (S.remainder_subset j)
        | inr r =>
            cases q with
            | none =>
                cases r with
                | none => exact False.elim (hab rfl)
                | some j =>
                    change Disjoint (P.block i₁ ∪ S.U) (S.remainder j)
                    apply Set.disjoint_union_left.mpr
                    exact ⟨(P.disjoint hi).mono_right (S.remainder_subset j),
                      S.U_remainder_disjoint j⟩
            | some j =>
                cases r with
                | none =>
                    change Disjoint (S.remainder j) (P.block i₁ ∪ S.U)
                    apply Set.disjoint_union_right.mpr
                    exact ⟨(P.disjoint hi.symm).mono_left (S.remainder_subset j),
                      (S.U_remainder_disjoint j).symm⟩
                | some k =>
                    change Disjoint (S.remainder j) (S.remainder k)
                    apply S.remainder_disjoint
                    intro h
                    exact hab (by simp [h])
  cover := by
    intro x
    obtain ⟨i, hix⟩ := P.cover x
    by_cases h₀ : i = i₀
    · subst i
      rcases S.central_cover x hix with hU | ⟨j, hj⟩
      · exact ⟨.inr none, Or.inr hU⟩
      · exact ⟨.inr (some j), hj⟩
    · by_cases h₁ : i = i₁
      · subst i
        exact ⟨.inr none, Or.inl hix⟩
      · exact ⟨.inl ⟨i, h₀, h₁⟩, hix⟩

variable {i₁ : I} (hi : i₁ ≠ i₀)
  (hconn : (G.induce (P.block i₁ ∪ S.U)).Connected)

/-- Absorption does not alter edges between untouched blocks. -/
theorem fusion_adj_old_old
    (a b : {i : I // i ≠ i₀ ∧ i ≠ i₁}) :
    (S.fusionPartition i₁ hi hconn).touchingQuotient.Adj (.inl a) (.inl b) ↔
      P.touchingQuotient.Adj a.1 b.1 := by
  simp only [ConnectedPartition.touchingQuotient_adj_iff, fusionPartition, fusionBlock]
  constructor
  · rintro ⟨hne, htouch⟩
    refine ⟨?_, htouch⟩
    intro hab
    exact hne (congrArg Sum.inl (Subtype.ext hab))
  · rintro ⟨hne, htouch⟩
    exact ⟨fun hab => hne (congrArg Subtype.val (Sum.inl.inj hab)), htouch⟩

/-- Every external neighbor of a remainder was an old central neighbor. -/
theorem fusion_old_neighbor_of_remainder
    (j : J) (a : {i : I // i ≠ i₀ ∧ i ≠ i₁})
    (h : (S.fusionPartition i₁ hi hconn).touchingQuotient.Adj
      (.inr (some j)) (.inl a)) :
    P.touchingQuotient.Adj i₀ a.1 := by
  obtain ⟨_, x, hx, y, hy, hxy⟩ :=
    ((S.fusionPartition i₁ hi hconn).touchingQuotient_adj_iff _ _).mp h
  exact (P.touchingQuotient_adj_iff _ _).mpr
    ⟨a.2.1.symm, x, S.remainder_subset j hx, y, hy, hxy⟩

/-- Every external neighbor of the absorbed block was already a neighbor of
the absorbing old block, by simpliciality of the central old block. -/
theorem fusion_old_neighbor_of_absorbed [Fintype I]
    (hcentral : IsSimplicialOn P.touchingQuotient Finset.univ i₀)
    (h₁ : P.touchingQuotient.Adj i₀ i₁)
    (a : {i : I // i ≠ i₀ ∧ i ≠ i₁})
    (h : (S.fusionPartition i₁ hi hconn).touchingQuotient.Adj
      (.inr none) (.inl a)) :
    P.touchingQuotient.Adj i₁ a.1 := by
  obtain ⟨_, x, hx, y, hy, hxy⟩ :=
    ((S.fusionPartition i₁ hi hconn).touchingQuotient_adj_iff _ _).mp h
  rcases hx with hx | hx
  · exact (P.touchingQuotient_adj_iff _ _).mpr
      ⟨a.2.2.symm, x, hx, y, hy, hxy⟩
  · have h₀a : P.touchingQuotient.Adj i₀ a.1 :=
      (P.touchingQuotient_adj_iff _ _).mpr
        ⟨a.2.1.symm, x, S.U_subset hx, y, hy, hxy⟩
    exact hcentral (Finset.mem_univ _) (Finset.mem_univ _) h₁ h₀a a.2.2.symm

/-- Every old edge from the absorbing block to an untouched block persists. -/
theorem fusion_absorbed_adj_of_old
    (a : {i : I // i ≠ i₀ ∧ i ≠ i₁})
    (h : P.touchingQuotient.Adj i₁ a.1) :
    (S.fusionPartition i₁ hi hconn).touchingQuotient.Adj
      (.inr none) (.inl a) := by
  obtain ⟨_, x, hx, y, hy, hxy⟩ := (P.touchingQuotient_adj_iff _ _).mp h
  have hne : (Sum.inr none : FusionIndex I J i₀ i₁) ≠ Sum.inl a := by
    intro he
    cases he
  exact ((S.fusionPartition i₁ hi hconn).touchingQuotient_adj_iff _ _).mpr
    ⟨hne, x, Or.inl hx, y, hy, hxy⟩

/-- Distinct remainder components have no quotient edge. -/
theorem fusion_not_adj_remainders
    (hno : ∀ j k, j ≠ k →
      ¬ ∃ x ∈ S.remainder j, ∃ y ∈ S.remainder k, G.Adj x y)
    (j k : J) :
    ¬ (S.fusionPartition i₁ hi hconn).touchingQuotient.Adj
      (.inr (some j)) (.inr (some k)) := by
  by_cases hjk : j = k
  · subst k
    exact (S.fusionPartition i₁ hi hconn).touchingQuotient.irrefl
  · intro h
    exact hno j k hjk
      (((S.fusionPartition i₁ hi hconn).touchingQuotient_adj_iff _ _).mp h).2

/-- Each remainder is simplicial in the fused quotient. Its old-block
neighbors all neighbor the old central block, hence form a clique. -/
theorem fusion_remainder_simplicial [Fintype I]
    [Fintype (FusionIndex I J i₀ i₁)]
    (hcentral : IsSimplicialOn P.touchingQuotient Finset.univ i₀)
    (h₁ : P.touchingQuotient.Adj i₀ i₁)
    (hno : ∀ j k, j ≠ k →
      ¬ ∃ x ∈ S.remainder j, ∃ y ∈ S.remainder k, G.Adj x y)
    (j : J) :
    IsSimplicialOn (S.fusionPartition i₁ hi hconn).touchingQuotient
      Finset.univ (.inr (some j)) := by
  classical
  intro a b _ _ hja hjb hab
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          have ha := S.fusion_old_neighbor_of_remainder hi hconn j a hja
          have hb := S.fusion_old_neighbor_of_remainder hi hconn j b hjb
          have hne : a.1 ≠ b.1 := by
            intro he
            exact hab (congrArg Sum.inl (Subtype.ext he))
          exact (S.fusion_adj_old_old hi hconn a b).2
            (hcentral (Finset.mem_univ _) (Finset.mem_univ _) ha hb hne)
      | inr q =>
          cases q with
          | none =>
              have ha := S.fusion_old_neighbor_of_remainder hi hconn j a hja
              have h₁a := hcentral (Finset.mem_univ _) (Finset.mem_univ _)
                h₁ ha a.2.2.symm
              exact (S.fusion_absorbed_adj_of_old hi hconn a h₁a).symm
          | some k =>
              exact False.elim (S.fusion_not_adj_remainders hi hconn hno j k hjb)
  | inr q =>
      cases q with
      | none =>
          cases b with
          | inl b =>
              have hb := S.fusion_old_neighbor_of_remainder hi hconn j b hjb
              have h₁b := hcentral (Finset.mem_univ _) (Finset.mem_univ _)
                h₁ hb b.2.2.symm
              exact S.fusion_absorbed_adj_of_old hi hconn b h₁b
          | inr r =>
              cases r with
              | none => exact False.elim (hab rfl)
              | some k =>
                  exact False.elim (S.fusion_not_adj_remainders hi hconn hno j k hjb)
      | some k =>
          exact False.elim (S.fusion_not_adj_remainders hi hconn hno j k hja)

/-- Replacing an egg block by its absorption of a nonempty part of a non-egg
central block strictly increases egg support. -/
theorem fusion_eggSupport_ssubset [Fintype V] [Fintype I] [DecidableEq I]
    [Fintype (FusionIndex I J i₀ i₁)]
    [DecidableEq (FusionIndex I J i₀ i₁)]
    (w : V → ℝ)
    (hnot : ¬ IsEgg G w (P.block i₀))
    (hnew : IsEgg G w (P.block i₁ ∪ S.U)) :
    eggSupport P w ⊂ eggSupport (S.fusionPartition i₁ hi hconn) w := by
  classical
  have hsubset : eggSupport P w ⊆
      eggSupport (S.fusionPartition i₁ hi hconn) w := by
    intro v hv
    obtain ⟨i, hvi, hegg⟩ := (mem_eggSupport P w v).mp hv
    by_cases h₀ : i = i₀
    · subst i
      exact False.elim (hnot hegg)
    · by_cases h₁ : i = i₁
      · subst i
        exact (mem_eggSupport (S.fusionPartition i₁ hi hconn) w v).mpr
          ⟨.inr none, Or.inl hvi, hnew⟩
      · exact (mem_eggSupport (S.fusionPartition i₁ hi hconn) w v).mpr
          ⟨.inl ⟨i, h₀, h₁⟩, hvi, hegg⟩
  obtain ⟨v, hv⟩ : S.U.Nonempty := by
    obtain ⟨x⟩ := S.U_connected.nonempty
    exact ⟨x.1, x.2⟩
  have hnewv : v ∈ eggSupport (S.fusionPartition i₁ hi hconn) w :=
    (mem_eggSupport (S.fusionPartition i₁ hi hconn) w v).mpr
      ⟨.inr none, Or.inr hv, hnew⟩
  have hold : v ∉ eggSupport P w := by
    intro h
    obtain ⟨i, hvi, hegg⟩ := (mem_eggSupport P w v).mp h
    by_cases h₀ : i = i₀
    · subst i
      exact hnot hegg
    · exact (Set.disjoint_left.mp (P.disjoint h₀)) hvi (S.U_subset hv)
  exact ssubset_iff_subset_ne.mpr
    ⟨hsubset, by intro heq; exact hold (heq ▸ hnewv)⟩

/-- The fused quotient core excludes its remainder components. -/
abbrev FusionCoreIndex (I : Type u) (J : Type w) (i₀ i₁ : I) :=
  {k : FusionIndex I J i₀ i₁ // ∀ j : J, k ≠ .inr (some j)}

/-- The old quotient with the central vertex deleted has the same labels as
the fused core, up to renaming the absorbed egg. -/
noncomputable def fusionCoreMap
    (i : {i : I // i ≠ i₀}) : FusionCoreIndex I J i₀ i₁ := by
  classical
  by_cases h : i.1 = i₁
  · exact ⟨.inr none, by intro j hj; cases hj⟩
  · exact ⟨.inl ⟨i.1, i.2, h⟩, by intro j hj; cases hj⟩

noncomputable def fusionCoreEquiv :
    {i : I // i ≠ i₀} ≃ FusionCoreIndex I J i₀ i₁ where
  toFun := fusionCoreMap (J := J) (i₁ := i₁)
  invFun k := match k.1 with
    | .inl i => ⟨i.1, i.2.1⟩
    | .inr none => ⟨i₁, hi⟩
    | .inr (some _) => ⟨i₁, hi⟩
  left_inv := by
    intro i
    by_cases h : i.1 = i₁
    · apply Subtype.ext
      simp [fusionCoreMap, h]
    · apply Subtype.ext
      simp [fusionCoreMap, h]
  right_inv := by
    rintro ⟨k, hk⟩
    cases k with
    | inl i =>
        apply Subtype.ext
        simp [fusionCoreMap, i.2.2]
    | inr q =>
        cases q with
        | none =>
            apply Subtype.ext
            simp [fusionCoreMap]
        | some j =>
            exact False.elim (hk j rfl)

/-- After deleting the new remainder components, the fused quotient is the
old quotient with its central vertex removed. -/
noncomputable def fusionCoreIso [Fintype I]
    (hcentral : IsSimplicialOn P.touchingQuotient Finset.univ i₀)
    (h₁ : P.touchingQuotient.Adj i₀ i₁) :
    (P.touchingQuotient.induce {i : I | i ≠ i₀}) ≃g
      ((S.fusionPartition i₁ hi hconn).touchingQuotient.induce
        {k : FusionIndex I J i₀ i₁ | ∀ j : J, k ≠ .inr (some j)}) where
  toEquiv := fusionCoreEquiv (J := J) hi
  map_rel_iff' := by
    intro a b
    change (S.fusionPartition i₁ hi hconn).touchingQuotient.Adj
      (fusionCoreMap (J := J) (i₁ := i₁) a).1
      (fusionCoreMap (J := J) (i₁ := i₁) b).1 ↔
        P.touchingQuotient.Adj a.1 b.1
    by_cases ha : a.1 = i₁
    · by_cases hb : b.1 = i₁
      · have hab : a = b := Subtype.ext (ha.trans hb.symm)
        subst b
        simp
      · simp only [fusionCoreMap, dif_pos ha, dif_neg hb]
        constructor
        · intro h
          rw [ha]
          exact S.fusion_old_neighbor_of_absorbed hi hconn hcentral h₁
            ⟨b.1, b.2, hb⟩ h
        · intro h
          apply S.fusion_absorbed_adj_of_old hi hconn ⟨b.1, b.2, hb⟩
          simpa only [ha] using h
    · by_cases hb : b.1 = i₁
      · simp only [fusionCoreMap, dif_neg ha, dif_pos hb]
        constructor
        · intro h
          rw [hb]
          exact (S.fusion_old_neighbor_of_absorbed hi hconn hcentral h₁
            ⟨a.1, a.2, ha⟩ h.symm).symm
        · intro h
          have h' : P.touchingQuotient.Adj i₁ a.1 := by
            simpa only [hb] using h.symm
          exact (S.fusion_absorbed_adj_of_old hi hconn ⟨a.1, a.2, ha⟩ h').symm
      · simp only [fusionCoreMap, dif_neg ha, dif_neg hb]
        exact S.fusion_adj_old_old hi hconn
          ⟨a.1, a.2, ha⟩ ⟨b.1, b.2, hb⟩

/-- The first Reed--Seymour quotient update preserves simplicial
elimination: eliminate all remainder vertices, then use the old quotient
with its simplicial central vertex removed. -/
theorem fusion_hasSimplicialElimination [Fintype I] [Fintype J]
    [Fintype (FusionIndex I J i₀ i₁)]
    (hPEO : HasSimplicialElimination P.touchingQuotient)
    (hcentral : IsSimplicialOn P.touchingQuotient Finset.univ i₀)
    (h₁ : P.touchingQuotient.Adj i₀ i₁)
    (hno : ∀ j k, j ≠ k →
      ¬ ∃ x ∈ S.remainder j, ∃ y ∈ S.remainder k, G.Adj x y) :
    HasSimplicialElimination
      (S.fusionPartition i₁ hi hconn).touchingQuotient := by
  classical
  let Z : Finset (FusionIndex I J i₀ i₁) :=
    Finset.univ.image (fun j : J => Sum.inr (some j))
  have hZ : ∀ z ∈ Z,
      IsSimplicialOn (S.fusionPartition i₁ hi hconn).touchingQuotient
        Finset.univ z := by
    intro z hz
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hz
    subst z
    exact S.fusion_remainder_simplicial hi hconn hcentral h₁ hno j
  have hset : {x : FusionIndex I J i₀ i₁ | x ∉ Z} =
      {x | ∀ j : J, x ≠ .inr (some j)} := by
    ext x
    constructor
    · intro hx j h
      apply hx
      apply Finset.mem_image.mpr
      exact ⟨j, Finset.mem_univ _, h.symm⟩
    · intro hx hz
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hz
      exact hx j hj.symm
  have hcoreOld :
      HasSimplicialElimination
        (P.touchingQuotient.induce {i : I | i ≠ i₀}) :=
    hPEO.induce _
  have hcore :
      HasSimplicialElimination
        ((S.fusionPartition i₁ hi hconn).touchingQuotient.induce
          {x : FusionIndex I J i₀ i₁ | ∀ j : J, x ≠ .inr (some j)}) :=
    HasSimplicialElimination.of_iso
      (S.fusionCoreIso hi hconn hcentral h₁) hcoreOld
  have hrest :
      HasSimplicialElimination
        ((S.fusionPartition i₁ hi hconn).touchingQuotient.induce
          {x : FusionIndex I J i₀ i₁ | x ∉ Z}) := by
    rw [hset]
    exact hcore
  exact HasSimplicialElimination.of_simplicial_set
    (S.fusionPartition i₁ hi hconn).touchingQuotient Z hZ hrest

/-- The odd-path absorption update preserves the partial egg-decomposition
invariant. The absorbed block is an egg; each new remainder is simplicial and
has only egg neighbors. -/
theorem fusion_isPartialEggDecomposition [Fintype V] [Fintype I]
    [DecidableEq I] [Fintype J] [Fintype (FusionIndex I J i₀ i₁)]
    [DecidableEq (FusionIndex I J i₀ i₁)]
    (w : V → ℝ)
    (hP : IsPartialEggDecomposition P w)
    (hnot : ¬ IsEgg G w (P.block i₀))
    (hnew : IsEgg G w (P.block i₁ ∪ S.U))
    (h₁ : P.touchingQuotient.Adj i₀ i₁)
    (hno : ∀ j k, j ≠ k →
      ¬ ∃ x ∈ S.remainder j, ∃ y ∈ S.remainder k, G.Adj x y) :
    IsPartialEggDecomposition (S.fusionPartition i₁ hi hconn) w := by
  classical
  have hcentralData : IsSimplicialOn P.touchingQuotient Finset.univ i₀ ∧
      ∀ k, P.touchingQuotient.Adj i₀ k → IsEgg G w (P.block k) := by
    rcases hP.2 i₀ with hegg | h
    · exact False.elim (hnot hegg)
    · exact h
  refine ⟨S.fusion_hasSimplicialElimination hi hconn hP.1
    hcentralData.1 h₁ hno, ?_⟩
  intro k
  cases k with
  | inr q =>
      cases q with
      | none =>
          left
          exact hnew
      | some j =>
          right
          refine ⟨S.fusion_remainder_simplicial hi hconn
            hcentralData.1 h₁ hno j, ?_⟩
          intro b hb
          cases b with
          | inl b =>
              exact hcentralData.2 b.1
                (S.fusion_old_neighbor_of_remainder hi hconn j b hb)
          | inr r =>
              cases r with
              | none => exact hnew
              | some k =>
                  exact False.elim (S.fusion_not_adj_remainders
                    hi hconn hno j k hb)
  | inl i =>
      rcases hP.2 i.1 with hegg | ⟨hsim, hall⟩
      · left
        exact hegg
      · right
        have hnoCentral : ¬ P.touchingQuotient.Adj i.1 i₀ := by
          intro h
          exact hnot (hall i₀ h)
        have hnoRemainder (j : J) :
            ¬ (S.fusionPartition i₁ hi hconn).touchingQuotient.Adj
              (.inl i) (.inr (some j)) := by
          intro h
          exact hnoCentral
            (S.fusion_old_neighbor_of_remainder hi hconn j i h.symm).symm
        have hOldFused :
            (S.fusionPartition i₁ hi hconn).touchingQuotient.Adj
              (.inl i) (.inr none) ↔
                P.touchingQuotient.Adj i.1 i₁ := by
          constructor
          · intro h
            exact (S.fusion_old_neighbor_of_absorbed hi hconn
              hcentralData.1 h₁ i h.symm).symm
          · intro h
            exact (S.fusion_absorbed_adj_of_old hi hconn i h.symm).symm
        constructor
        · intro a b _ _ hia hib hab
          cases a with
          | inl a =>
              cases b with
              | inl b =>
                  have ha := (S.fusion_adj_old_old hi hconn i a).1 hia
                  have hb := (S.fusion_adj_old_old hi hconn i b).1 hib
                  have hne : a.1 ≠ b.1 := by
                    intro he
                    exact hab (congrArg Sum.inl (Subtype.ext he))
                  exact (S.fusion_adj_old_old hi hconn a b).2
                    (hsim (Finset.mem_univ _) (Finset.mem_univ _) ha hb hne)
              | inr q =>
                  cases q with
                  | none =>
                      have ha := (S.fusion_adj_old_old hi hconn i a).1 hia
                      have hb := hOldFused.mp hib
                      have habOld := hsim (Finset.mem_univ _)
                        (Finset.mem_univ _) ha hb a.2.2
                      exact (S.fusion_absorbed_adj_of_old
                        hi hconn a habOld.symm).symm
                  | some j =>
                      exact False.elim (hnoRemainder j hib)
          | inr q =>
              cases q with
              | none =>
                  cases b with
                  | inl b =>
                      have ha := hOldFused.mp hia
                      have hb := (S.fusion_adj_old_old hi hconn i b).1 hib
                      have habOld := hsim (Finset.mem_univ _)
                        (Finset.mem_univ _) ha hb b.2.2.symm
                      exact S.fusion_absorbed_adj_of_old
                        hi hconn b habOld
                  | inr r =>
                      cases r with
                      | none => exact False.elim (hab rfl)
                      | some j =>
                          exact False.elim (hnoRemainder j hib)
              | some j =>
                  exact False.elim (hnoRemainder j hia)
        · intro b hb
          cases b with
          | inl b =>
              exact hall b.1 ((S.fusion_adj_old_old hi hconn i b).1 hb)
          | inr q =>
              cases q with
              | none => exact hnew
              | some j => exact False.elim (hnoRemainder j hb)

/-- The concrete first update: absorb a connected central set into an old
neighboring egg and use the components of its complement as remainder blocks. -/
theorem ofComponents_fusion_partial_and_support [Fintype V] [Fintype I]
    [DecidableEq I] (P : ConnectedPartition G I) (i₀ i₁ : I) (w : V → ℝ)
    (U : Set V)
    [Fintype (G.induce (P.block i₀ \ U)).ConnectedComponent]
    [Fintype (FusionIndex I
      (G.induce (P.block i₀ \ U)).ConnectedComponent i₀ i₁)]
    [DecidableEq (FusionIndex I
      (G.induce (P.block i₀ \ U)).ConnectedComponent i₀ i₁)]
    (hUconn : (G.induce U).Connected) (hsubset : U ⊆ P.block i₀)
    (hP : IsPartialEggDecomposition P w)
    (hnot : ¬ IsEgg G w (P.block i₀))
    (hi : i₁ ≠ i₀)
    (h₁ : P.touchingQuotient.Adj i₀ i₁)
    (hnew : IsEgg G w (P.block i₁ ∪ U)) :
    IsPartialEggDecomposition
      ((CentralSplit.ofComponents P i₀ U hUconn hsubset).fusionPartition
        i₁ hi hnew.connected) w ∧
    eggSupport P w ⊂
      eggSupport
        ((CentralSplit.ofComponents P i₀ U hUconn hsubset).fusionPartition
          i₁ hi hnew.connected) w := by
  let S := CentralSplit.ofComponents P i₀ U hUconn hsubset
  have hno := CentralSplit.ofComponents_no_cross P i₀ U hUconn hsubset
  exact ⟨S.fusion_isPartialEggDecomposition hi hnew.connected
      w hP hnot hnew h₁ hno,
    S.fusion_eggSupport_ssubset hi hnew.connected w hnot hnew⟩

/-- Applying yolk absorption to a bipartite central connector yields one of
the two fused partial decompositions with strictly larger egg support. The
path argument supplies the stable classes and no-cross-edge hypotheses. -/
theorem bipartite_connector_fusion_improves [Fintype V] [Fintype I]
    [DecidableEq I] [Fintype J]
    [Fintype (FusionIndex I J i₀ i₁)]
    [DecidableEq (FusionIndex I J i₀ i₁)]
    {i₂ : I}
    [Fintype (FusionIndex I J i₀ i₂)]
    [DecidableEq (FusionIndex I J i₀ i₂)]
    (w : V → ℝ) (Y₁ Y₂ A B : Set V)
    (hP : IsPartialEggDecomposition P w)
    (hnot : ¬ IsEgg G w (P.block i₀))
    (hi₂ : i₂ ≠ i₀)
    (h₁ : P.touchingQuotient.Adj i₀ i₁)
    (h₂ : P.touchingQuotient.Adj i₀ i₂)
    (hY₁ : IsYolk G w (P.block i₁) Y₁)
    (hY₂ : IsYolk G w (P.block i₂) Y₂)
    (hU : S.U = A ∪ B)
    (hAB : Disjoint A B)
    (hA : G.IsIndepSet A) (hB : G.IsIndepSet B)
    (hconn₁ : (G.induce (P.block i₁ ∪ S.U)).Connected)
    (hconn₂ : (G.induce (P.block i₂ ∪ S.U)).Connected)
    (hcross₁ : ∀ u ∈ Y₁, ∀ v ∈ B, ¬ G.Adj u v)
    (hcross₂ : ∀ u ∈ Y₂, ∀ v ∈ A, ¬ G.Adj u v)
    (hno : ∀ j k, j ≠ k →
      ¬ ∃ x ∈ S.remainder j, ∃ y ∈ S.remainder k, G.Adj x y) :
    (IsPartialEggDecomposition (S.fusionPartition i₁ hi hconn₁) w ∧
      eggSupport P w ⊂ eggSupport (S.fusionPartition i₁ hi hconn₁) w) ∨
    (IsPartialEggDecomposition (S.fusionPartition i₂ hi₂ hconn₂) w ∧
      eggSupport P w ⊂ eggSupport (S.fusionPartition i₂ hi₂ hconn₂) w) := by
  classical
  have hdisj₁ : Disjoint (P.block i₁) S.U :=
    (P.disjoint hi).mono_right S.U_subset
  have hdisj₂ : Disjoint (P.block i₂) S.U :=
    (P.disjoint hi₂).mono_right S.U_subset
  rcases egg_absorbs_bipartite_connector hY₁ hY₂ hU hAB hA hB
      hdisj₁ hdisj₂ hconn₁ hconn₂ hcross₁ hcross₂ with hegg | hegg
  · exact Or.inl ⟨S.fusion_isPartialEggDecomposition hi hconn₁
      w hP hnot hegg h₁ hno,
      S.fusion_eggSupport_ssubset hi hconn₁ w hnot hegg⟩
  · exact Or.inr ⟨S.fusion_isPartialEggDecomposition hi₂ hconn₂
      w hP hnot hegg h₂ hno,
      S.fusion_eggSupport_ssubset hi₂ hconn₂ w hnot hegg⟩

/-- Forgetting an induced-graph subtype in a walk preserves its original
vertices and edges. -/
def liftInducedWalk {T : Set V} {a b : T}
    (p : (G.induce T).Walk a b) : G.Walk a.1 b.1 :=
  p.map (SimpleGraph.Embedding.induce T).toHom

theorem liftInducedWalk_isPath {T : Set V} {a b : T}
    {p : (G.induce T).Walk a b} (hp : p.IsPath) :
    (liftInducedWalk p).IsPath := by
  exact hp.map (SimpleGraph.Embedding.induce (G := G) T).injective

theorem liftInducedWalk_isChordless {T : Set V} {a b : T}
    {p : (G.induce T).Walk a b} (hp : p.IsChordless) :
    (liftInducedWalk p).IsChordless := by
  apply SimpleGraph.Walk.isChordless_iff_forall_mem_edges.mpr
  intro x y hx hy hxy
  change x ∈ (p.map (SimpleGraph.Embedding.induce T).toHom).support at hx
  rw [SimpleGraph.Walk.support_map] at hx
  change y ∈ (p.map (SimpleGraph.Embedding.induce T).toHom).support at hy
  rw [SimpleGraph.Walk.support_map] at hy
  obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx
  obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
  have hxy' : (G.induce T).Adj x' y' := hxy
  have hedge := hp.mem_edges hx' hy' hxy'
  change s((SimpleGraph.Embedding.induce (G := G) T).toHom x',
    (SimpleGraph.Embedding.induce (G := G) T).toHom y') ∈
      (p.map (SimpleGraph.Embedding.induce T).toHom).edges
  rw [SimpleGraph.Walk.edges_map]
  exact List.mem_map.mpr ⟨s(x', y'), hedge, rfl⟩

/-- The vertices of an odd induced path split into two independent classes
containing its respective endpoints. -/
theorem odd_chordless_path_bipartition {a b : V}
    (p : G.Walk a b) (hp : p.IsPath)
    (hchord : p.IsChordless) (hodd : Odd p.length) :
    ∃ A B : Set V,
      {v | v ∈ p.support} = A ∪ B ∧
      Disjoint A B ∧ G.IsIndepSet A ∧ G.IsIndepSet B ∧
      a ∈ A ∧ b ∈ B := by
  classical
  obtain ⟨c, hends⟩ :=
    exists_chordless_odd_path_bicoloring p hp hchord hodd
  let X : Set V := {v | v ∈ p.support}
  let ca : Bool := c ⟨a, p.start_mem_support⟩
  let A : Set V := {v | ∃ hv : v ∈ X, c ⟨v, hv⟩ = ca}
  let B : Set V := {v | ∃ hv : v ∈ X, c ⟨v, hv⟩ ≠ ca}
  have hcover : X = A ∪ B := by
    ext v
    constructor
    · intro hv
      by_cases h : c ⟨v, hv⟩ = ca
      · exact Or.inl ⟨hv, h⟩
      · exact Or.inr ⟨hv, h⟩
    · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
  have hdisj : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro v hvA hvB
    obtain ⟨hvX, hvEq⟩ := hvA
    obtain ⟨_, hvNe⟩ := hvB
    exact hvNe hvEq
  have hA : G.IsIndepSet A := by
    intro u hu v hv huv hadj
    obtain ⟨huX, huEq⟩ := hu
    obtain ⟨hvX, hvEq⟩ := hv
    exact (c.valid
      (show (G.induce X).Adj ⟨u, huX⟩ ⟨v, hvX⟩ from hadj))
      (huEq.trans hvEq.symm)
  have hB : G.IsIndepSet B := by
    intro u hu v hv huv hadj
    obtain ⟨huX, huNe⟩ := hu
    obtain ⟨hvX, hvNe⟩ := hv
    have heq : c ⟨u, huX⟩ = c ⟨v, hvX⟩ := by
      cases hcu : c ⟨u, huX⟩ <;>
        cases hcv : c ⟨v, hvX⟩ <;>
        simp_all [ca]
    exact (c.valid
      (show (G.induce X).Adj ⟨u, huX⟩ ⟨v, hvX⟩ from hadj)) heq
  refine ⟨A, B, hcover, hdisj, hA, hB, ?_, ?_⟩
  · exact ⟨p.start_mem_support, rfl⟩
  · exact ⟨p.end_mem_support, hends.symm⟩

/-- An odd induced path between two terminal sets can be absorbed into one
of the corresponding eggs. Its endpoint-only property prevents the added
parity class from meeting the old yolk by an edge. -/
theorem odd_terminal_connector_absorbs [Fintype V]
    (P : ConnectedPartition G I) (i₀ i₁ i₂ : I)
    (w : V → ℝ) {a b : V} (p : G.Walk a b)
    (hp : IsTerminalConnector (terminalSet P i₀) i₁ i₂ p)
    (hodd : Odd p.length)
    (hinside : ∀ v, v ∈ p.support → v ∈ P.block i₀)
    (hi₁ : i₁ ≠ i₀) (hi₂ : i₂ ≠ i₀)
    {Y₁ Y₂ : Set V}
    (hY₁ : IsYolk G w (P.block i₁) Y₁)
    (hY₂ : IsYolk G w (P.block i₂) Y₂) :
    IsEgg G w (P.block i₁ ∪ {v | v ∈ p.support}) ∨
      IsEgg G w (P.block i₂ ∪ {v | v ∈ p.support}) := by
  let U : Set V := {v | v ∈ p.support}
  obtain ⟨A, B, hU, hAB, hA, hB, haA, hbB⟩ :=
    odd_chordless_path_bipartition p hp.isPath hp.isChordless hodd
  have hsubset : U ⊆ P.block i₀ := by
    intro v hv
    exact hinside v hv
  have hdisj₁ : Disjoint (P.block i₁) U :=
    (P.disjoint hi₁).mono_right hsubset
  have hdisj₂ : Disjoint (P.block i₂) U :=
    (P.disjoint hi₂).mono_right hsubset
  have hconnU : (G.induce U).Connected := p.connected_induce_support
  obtain ⟨x₁, hx₁, hax₁⟩ := hp.start_mem.2
  obtain ⟨x₂, hx₂, hbx₂⟩ := hp.end_mem.2
  have hconn₁ : (G.induce (P.block i₁ ∪ U)).Connected :=
    G.connected_induce_union (P.connected i₁).preconnected
      hconnU.preconnected hx₁ p.start_mem_support hax₁.symm
  have hconn₂ : (G.induce (P.block i₂ ∪ U)).Connected :=
    G.connected_induce_union (P.connected i₂).preconnected
      hconnU.preconnected hx₂ p.end_mem_support hbx₂.symm
  have hcross₁ : ∀ u ∈ Y₁, ∀ v ∈ B, ¬ G.Adj u v := by
    intro u hu v hv hadj
    have hvU : v ∈ U := by
      change v ∈ ({x | x ∈ p.support} : Set V)
      rw [hU]
      exact Or.inr hv
    have hvNi : v ∈ terminalSet P i₀ i₁ :=
      ⟨hsubset hvU, u, hY₁.subset hu, hadj.symm⟩
    have hva : v = a := hp.start_only v hvU hvNi
    subst v
    exact (Set.disjoint_left.mp hAB) haA hv
  have hcross₂ : ∀ u ∈ Y₂, ∀ v ∈ A, ¬ G.Adj u v := by
    intro u hu v hv hadj
    have hvU : v ∈ U := by
      change v ∈ ({x | x ∈ p.support} : Set V)
      rw [hU]
      exact Or.inl hv
    have hvNj : v ∈ terminalSet P i₀ i₂ :=
      ⟨hsubset hvU, u, hY₂.subset hu, hadj.symm⟩
    have hvb : v = b := hp.end_only v hvU hvNj
    subst v
    exact (Set.disjoint_left.mp hAB) hv hbB
  exact egg_absorbs_bipartite_connector hY₁ hY₂ hU hAB hA hB
    hdisj₁ hdisj₂ hconn₁ hconn₂ hcross₁ hcross₂

/-- The first Reed--Seymour improvement: an odd induced terminal connector
contradicts maximal egg support by absorption into one neighboring egg. -/
theorem improve_of_odd_terminal_connector [Fintype V] [Fintype I]
    [DecidableEq I]
    (P : ConnectedPartition G I) (i₀ : I) (w : V → ℝ)
    (hP : IsPartialEggDecomposition P w)
    (hnot : ¬ IsEgg G w (P.block i₀))
    {i₁ i₂ : I}
    (h₁ : P.touchingQuotient.Adj i₀ i₁)
    (h₂ : P.touchingQuotient.Adj i₀ i₂)
    {a b : V} (p : G.Walk a b)
    (hp : IsTerminalConnector (terminalSet P i₀) i₁ i₂ p)
    (hodd : Odd p.length)
    (hinside : ∀ v, v ∈ p.support → v ∈ P.block i₀) :
    ∃ m : ℕ, ∃ Q : ConnectedPartition G (Fin m),
      IsPartialEggDecomposition Q w ∧
        eggSupport P w ⊂ eggSupport Q w := by
  classical
  have hi₁ : i₁ ≠ i₀ :=
    ((P.touchingQuotient_adj_iff _ _).mp h₁).1.symm
  have hi₂ : i₂ ≠ i₀ :=
    ((P.touchingQuotient_adj_iff _ _).mp h₂).1.symm
  have hcentralNeighbors : ∀ i,
      P.touchingQuotient.Adj i₀ i → IsEgg G w (P.block i) := by
    rcases hP.2 i₀ with hegg | h
    · exact False.elim (hnot hegg)
    · exact h.2
  obtain ⟨Y₁, hY₁⟩ := (hcentralNeighbors i₁ h₁).has_yolk
  obtain ⟨Y₂, hY₂⟩ := (hcentralNeighbors i₂ h₂).has_yolk
  let U : Set V := {v | v ∈ p.support}
  have hUconn : (G.induce U).Connected := p.connected_induce_support
  have hsubset : U ⊆ P.block i₀ := by
    intro v hv
    exact hinside v hv
  rcases odd_terminal_connector_absorbs P i₀ i₁ i₂ w p hp hodd
    hinside hi₁ hi₂ hY₁ hY₂ with hnew | hnew
  · let S := CentralSplit.ofComponents P i₀ U hUconn hsubset
    have hQ := CentralSplit.ofComponents_fusion_partial_and_support
      P i₀ i₁ w U hUconn hsubset hP hnot hi₁ h₁ hnew
    obtain ⟨m, Q, hQpartial, hQsupport⟩ :=
      (S.fusionPartition i₁ hi₁ hnew.connected).exists_fin_relabel w hQ.1
    exact ⟨m, Q, hQpartial, by simpa only [hQsupport] using hQ.2⟩
  · let S := CentralSplit.ofComponents P i₀ U hUconn hsubset
    have hQ := CentralSplit.ofComponents_fusion_partial_and_support
      P i₀ i₂ w U hUconn hsubset hP hnot hi₂ h₂ hnew
    obtain ⟨m, Q, hQpartial, hQsupport⟩ :=
      (S.fusionPartition i₂ hi₂ hnew.connected).exists_fin_relabel w hQ.1
    exact ⟨m, Q, hQpartial, by simpa only [hQsupport] using hQ.2⟩

end CentralSplit
end ReedSeymour
end HadwigerLean