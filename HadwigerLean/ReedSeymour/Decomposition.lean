import HadwigerLean.ReedSeymour.Partial
import HadwigerLean.ReedSeymour.Parity
import HadwigerLean.Graph.SimplicialElimination

/-!
# Refining one block of a connected partition

The final step of Reed--Seymour's egg-decomposition argument replaces one
non-egg block by a connected bipartite set and the connected components of
its complement.  This file records the partition and touching-quotient facts
for that replacement.  The existence of the bipartite set is a separate
parity argument.
-/

namespace HadwigerLean
namespace ReedSeymour

universe u v w

variable {V : Type v} {I : Type u} {J : Type w}
variable {G : SimpleGraph V}

/-- The indices after replacing `i₀` by a new block and remainder blocks. -/
abbrev SplitIndex (I : Type u) (J : Type w) (i₀ : I) :=
  Sum {i : I // i ≠ i₀} (Option J)

/-- Data for splitting one connected block into a connected set `U` and
connected remainder blocks. -/
structure CentralSplit (P : ConnectedPartition G I) (i₀ : I) (J : Type w) where
  U : Set V
  remainder : J → Set V
  U_connected : (G.induce U).Connected
  remainder_connected : ∀ j, (G.induce (remainder j)).Connected
  U_subset : U ⊆ P.block i₀
  remainder_subset : ∀ j, remainder j ⊆ P.block i₀
  U_remainder_disjoint : ∀ j, Disjoint U (remainder j)
  remainder_disjoint : Pairwise fun j k => Disjoint (remainder j) (remainder k)
  central_cover : ∀ x ∈ P.block i₀, x ∈ U ∨ ∃ j, x ∈ remainder j

namespace CentralSplit

variable {P : ConnectedPartition G I} {i₀ : I}
variable (S : CentralSplit P i₀ J)

/-- The blocks of the refined connected partition. -/
def block : SplitIndex I J i₀ → Set V
  | .inl i => P.block i.1
  | .inr none => S.U
  | .inr (some j) => S.remainder j

/-- Splitting the central block preserves a connected partition. -/
def partition : ConnectedPartition G (SplitIndex I J i₀) where
  block := S.block
  connected := by
    intro k
    cases k with
    | inl i => exact P.connected i.1
    | inr q =>
        cases q with
        | none => exact S.U_connected
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
            apply hab
            exact congrArg Sum.inl (Subtype.ext h)
        | inr q =>
            cases q with
            | none =>
                change Disjoint (P.block i.1) S.U
                exact (P.disjoint i.2).mono_right S.U_subset
            | some j =>
                change Disjoint (P.block i.1) (S.remainder j)
                exact (P.disjoint i.2).mono_right (S.remainder_subset j)
    | inr q =>
        cases b with
        | inl j =>
            cases q with
            | none =>
                change Disjoint S.U (P.block j.1)
                exact (P.disjoint j.2.symm).mono_left S.U_subset
            | some k =>
                change Disjoint (S.remainder k) (P.block j.1)
                exact (P.disjoint j.2.symm).mono_left (S.remainder_subset k)
        | inr r =>
            cases q with
            | none =>
                cases r with
                | none => exact False.elim (hab rfl)
                | some j => exact S.U_remainder_disjoint j
            | some j =>
                cases r with
                | none => exact (S.U_remainder_disjoint j).symm
                | some k =>
                    change Disjoint (S.remainder j) (S.remainder k)
                    apply S.remainder_disjoint
                    intro h
                    apply hab
                    simp [h]
  cover := by
    intro x
    obtain ⟨i, hi⟩ := P.cover x
    by_cases hieq : i = i₀
    · subst i
      rcases S.central_cover x hi with hu | ⟨j, hj⟩
      · exact ⟨.inr none, hu⟩
      · exact ⟨.inr (some j), hj⟩
    · exact ⟨.inl ⟨i, hieq⟩, hi⟩

/-- Edges between untouched blocks are unchanged by the split. -/
theorem adj_old_old (i j : {i : I // i ≠ i₀}) :
    S.partition.touchingQuotient.Adj (.inl i) (.inl j) ↔
      P.touchingQuotient.Adj i.1 j.1 := by
  simp only [ConnectedPartition.touchingQuotient_adj_iff, partition, block]
  constructor
  · rintro ⟨hij, htouch⟩
    refine ⟨?_, htouch⟩
    intro h
    exact hij (congrArg Sum.inl (Subtype.ext h))
  · rintro ⟨hij, htouch⟩
    exact ⟨fun h => hij (congrArg Subtype.val (Sum.inl.inj h)), htouch⟩

/-- An edge from the new block to an untouched block was already incident
with the old central block. -/
theorem old_neighbor_of_U_adj (i : {i : I // i ≠ i₀})
    (h : S.partition.touchingQuotient.Adj (.inr none) (.inl i)) :
    P.touchingQuotient.Adj i₀ i.1 := by
  obtain ⟨_, x, hx, y, hy, hxy⟩ :=
    (S.partition.touchingQuotient_adj_iff _ _).mp h
  exact (P.touchingQuotient_adj_iff _ _).mpr
    ⟨i.2.symm, x, S.U_subset hx, y, hy, hxy⟩

/-- An edge from a remainder block to an untouched block was already
incident with the old central block. -/
theorem old_neighbor_of_remainder_adj (j : J) (i : {i : I // i ≠ i₀})
    (h : S.partition.touchingQuotient.Adj (.inr (some j)) (.inl i)) :
    P.touchingQuotient.Adj i₀ i.1 := by
  obtain ⟨_, x, hx, y, hy, hxy⟩ :=
    (S.partition.touchingQuotient_adj_iff _ _).mp h
  exact (P.touchingQuotient_adj_iff _ _).mpr
    ⟨i.2.symm, x, S.remainder_subset j hx, y, hy, hxy⟩

/-- The new block keeps all old neighbors if it meets each old neighboring
block. This is the terminal-hitting property of the minimal connector. -/
theorem U_adj_of_old_neighbor (i : {i : I // i ≠ i₀})
    (htouch : ∀ k, P.touchingQuotient.Adj i₀ k →
      ∃ x ∈ S.U, ∃ y ∈ P.block k, G.Adj x y)
    (h : P.touchingQuotient.Adj i₀ i.1) :
    S.partition.touchingQuotient.Adj (.inr none) (.inl i) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := htouch i.1 h
  have hne : (Sum.inr none : SplitIndex I J i₀) ≠ Sum.inl i := by
    intro h
    cases h
  exact (S.partition.touchingQuotient_adj_iff _ _).mpr
    ⟨hne, x, hx, y, hy, hxy⟩

/-- Remainder blocks from distinct connected components do not touch. -/
theorem not_adj_remainders (j k : J) (hjk : j ≠ k)
    (hno : ∀ j k, j ≠ k →
      ¬ ∃ x ∈ S.remainder j, ∃ y ∈ S.remainder k, G.Adj x y) :
    ¬ S.partition.touchingQuotient.Adj (.inr (some j)) (.inr (some k)) := by
  intro h
  exact hno j k hjk ((S.partition.touchingQuotient_adj_iff _ _).mp h).2


/-- Distinct remainder components have no quotient edge. -/
theorem not_adj_remainder_any (j k : J)
    (hno : ∀ j k, j ≠ k →
      ¬ ∃ x ∈ S.remainder j, ∃ y ∈ S.remainder k, G.Adj x y) :
    ¬ S.partition.touchingQuotient.Adj (.inr (some j)) (.inr (some k)) := by
  by_cases h : j = k
  · subst k
    intro hadj
    exact S.partition.touchingQuotient.irrefl hadj
  · exact S.not_adj_remainders j k h hno

/-- Each remainder component is simplicial in the new quotient when the old
central block was simplicial and the new block retains its neighbors. -/
theorem remainder_simplicial [Fintype I] [Fintype (SplitIndex I J i₀)] (j : J)
    (hcentral : IsSimplicialOn P.touchingQuotient Finset.univ i₀)
    (htouch : ∀ k, P.touchingQuotient.Adj i₀ k →
      ∃ x ∈ S.U, ∃ y ∈ P.block k, G.Adj x y)
    (hno : ∀ j k, j ≠ k →
      ¬ ∃ x ∈ S.remainder j, ∃ y ∈ S.remainder k, G.Adj x y) :
    IsSimplicialOn S.partition.touchingQuotient Finset.univ (.inr (some j)) := by
  classical
  intro a b _ _ hja hjb hab
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          have ha := S.old_neighbor_of_remainder_adj j a hja
          have hb := S.old_neighbor_of_remainder_adj j b hjb
          have hne : a.1 ≠ b.1 := by
            intro he
            apply hab
            exact congrArg Sum.inl (Subtype.ext he)
          exact (S.adj_old_old a b).2
            (hcentral (Finset.mem_univ _) (Finset.mem_univ _) ha hb hne)
      | inr q =>
          cases q with
          | none =>
              exact (S.U_adj_of_old_neighbor a htouch
                (S.old_neighbor_of_remainder_adj j a hja)).symm
          | some k =>
              exact False.elim (S.not_adj_remainder_any j k hno hjb)
  | inr q =>
      cases q with
      | none =>
          cases b with
          | inl b =>
              exact S.U_adj_of_old_neighbor b htouch
                (S.old_neighbor_of_remainder_adj j b hjb)
          | inr r =>
              cases r with
              | none => exact False.elim (hab rfl)
              | some k =>
                  exact False.elim (S.not_adj_remainder_any j k hno hjb)
      | some k =>
          exact False.elim (S.not_adj_remainder_any j k hno hja)

/-- The indices left after deleting the remainder components. -/
abbrev CoreIndex (I : Type u) (J : Type w) (i₀ : I) :=
  {k : SplitIndex I J i₀ // ∀ j : J, k ≠ .inr (some j)}

/-- Renaming the old central index as the new connected block. -/
noncomputable def coreMap (i : I) : CoreIndex I J i₀ := by
  classical
  by_cases h : i = i₀
  · exact ⟨.inr none, by intro j hj; cases hj⟩
  · exact ⟨.inl ⟨i, h⟩, by intro j hj; cases hj⟩

/-- The core of a split quotient has exactly the old index set. -/
noncomputable def coreEquiv : I ≃ CoreIndex I J i₀ where
  toFun := coreMap (J := J)
  invFun k := match k.1 with
    | .inl i => i.1
    | .inr none => i₀
    | .inr (some _) => i₀
  left_inv := by
    intro i
    by_cases h : i = i₀
    · simp [coreMap, h]
    · simp [coreMap, h]
  right_inv := by
    rintro ⟨k, hk⟩
    cases k with
    | inl i =>
        apply Subtype.ext
        simp [coreMap, i.property]
    | inr q =>
        cases q with
        | none =>
            apply Subtype.ext
            simp [coreMap]
        | some j =>
            exact False.elim (hk j rfl)

/-- Deleting the new remainder vertices leaves the original quotient, with
the central vertex renamed as U. -/
noncomputable def coreIso
    (htouch : ∀ k, P.touchingQuotient.Adj i₀ k →
      ∃ x ∈ S.U, ∃ y ∈ P.block k, G.Adj x y) :
    P.touchingQuotient ≃g
      (S.partition.touchingQuotient.induce
        {k : SplitIndex I J i₀ | ∀ j : J, k ≠ .inr (some j)}) where
  toEquiv := coreEquiv (I := I) (J := J) (i₀ := i₀)
  map_rel_iff' := by
    intro i k
    change S.partition.touchingQuotient.Adj
      (coreMap (J := J) (i₀ := i₀) i).1
      (coreMap (J := J) (i₀ := i₀) k).1 ↔ P.touchingQuotient.Adj i k
    by_cases hi : i = i₀
    · subst i
      by_cases hk : k = i₀
      · subst k
        simp
      · simp only [coreMap, dif_neg hk]
        exact ⟨S.old_neighbor_of_U_adj ⟨k, hk⟩,
          S.U_adj_of_old_neighbor ⟨k, hk⟩ htouch⟩
    · by_cases hk : k = i₀
      · subst k
        simp only [coreMap, dif_neg hi]
        constructor
        · intro h
          exact (S.old_neighbor_of_U_adj ⟨i, hi⟩ h.symm).symm
        · intro h
          exact (S.U_adj_of_old_neighbor ⟨i, hi⟩ htouch h.symm).symm
      · simp only [coreMap, dif_neg hi, dif_neg hk]
        exact S.adj_old_old ⟨i, hi⟩ ⟨k, hk⟩

/-- The central split preserves simplicial elimination. The assumptions
are exactly the quotient conditions used in the final Reed--Seymour update:
the old central vertex is simplicial, U meets all its old neighbors, and
distinct remainder components have no edges between them. -/
theorem partition_hasSimplicialElimination [Fintype I] [Fintype J]
    [Fintype (SplitIndex I J i₀)]
    (hPEO : HasSimplicialElimination P.touchingQuotient)
    (hcentral : IsSimplicialOn P.touchingQuotient Finset.univ i₀)
    (htouch : ∀ k, P.touchingQuotient.Adj i₀ k →
      ∃ x ∈ S.U, ∃ y ∈ P.block k, G.Adj x y)
    (hno : ∀ j k, j ≠ k →
      ¬ ∃ x ∈ S.remainder j, ∃ y ∈ S.remainder k, G.Adj x y) :
    HasSimplicialElimination S.partition.touchingQuotient := by
  classical
  let Z : Finset (SplitIndex I J i₀) :=
    Finset.univ.image (fun j : J => Sum.inr (some j))
  have hZ : ∀ z ∈ Z,
      IsSimplicialOn S.partition.touchingQuotient Finset.univ z := by
    intro z hz
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hz
    subst z
    exact S.remainder_simplicial j hcentral htouch hno
  have hset : {x : SplitIndex I J i₀ | x ∉ Z} =
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
  have hcore : HasSimplicialElimination
      (S.partition.touchingQuotient.induce
        {x : SplitIndex I J i₀ | ∀ j : J, x ≠ .inr (some j)}) :=
    HasSimplicialElimination.of_iso (S.coreIso htouch) hPEO
  have hrest : HasSimplicialElimination
      (S.partition.touchingQuotient.induce {x : SplitIndex I J i₀ | x ∉ Z}) := by
    rw [hset]
    exact hcore
  exact HasSimplicialElimination.of_simplicial_set
    S.partition.touchingQuotient Z hZ hrest

/-- The central update preserves the partial egg-decomposition invariant.
An old non-egg block cannot neighbor the central non-egg block, so its quotient
neighborhood is unchanged by the split. -/
theorem partition_isPartialEggDecomposition [Fintype V] [Fintype I]
    [DecidableEq I] [Fintype J] [Fintype (SplitIndex I J i₀)]
    [DecidableEq (SplitIndex I J i₀)]
    (w : V → ℝ)
    (hP : IsPartialEggDecomposition P w)
    (hnot : ¬ IsEgg G w (P.block i₀))
    (hU : IsEgg G w S.U)
    (htouch : ∀ k, P.touchingQuotient.Adj i₀ k →
      ∃ x ∈ S.U, ∃ y ∈ P.block k, G.Adj x y)
    (hno : ∀ j k, j ≠ k →
      ¬ ∃ x ∈ S.remainder j, ∃ y ∈ S.remainder k, G.Adj x y) :
    IsPartialEggDecomposition S.partition w := by
  classical
  have hcentralData : IsSimplicialOn P.touchingQuotient Finset.univ i₀ ∧
      ∀ k, P.touchingQuotient.Adj i₀ k → IsEgg G w (P.block k) := by
    rcases hP.2 i₀ with h | h
    · exact False.elim (hnot h)
    · exact h
  refine ⟨S.partition_hasSimplicialElimination hP.1 hcentralData.1 htouch hno, ?_⟩
  intro k
  cases k with
  | inr q =>
      cases q with
      | none =>
          left
          exact hU
      | some j =>
          right
          refine ⟨S.remainder_simplicial j hcentralData.1 htouch hno, ?_⟩
          intro b hb
          cases b with
          | inl i =>
              exact hcentralData.2 i.1 (S.old_neighbor_of_remainder_adj j i hb)
          | inr r =>
              cases r with
              | none => exact hU
              | some k =>
                  exact False.elim (S.not_adj_remainder_any j k hno hb)
  | inl i =>
      rcases hP.2 i.1 with hegg | ⟨hsim, hall⟩
      · left
        exact hegg
      · right
        have hnoCentral : ¬ P.touchingQuotient.Adj i.1 i₀ := by
          intro h
          exact hnot (hall i₀ h)
        have hnoNew (q : Option J) :
            ¬ S.partition.touchingQuotient.Adj (.inl i) (.inr q) := by
          intro h
          cases q with
          | none =>
              exact hnoCentral
                (S.old_neighbor_of_U_adj i h.symm).symm
          | some j =>
              exact hnoCentral
                (S.old_neighbor_of_remainder_adj j i h.symm).symm
        constructor
        · intro a b _ _ hia hib hab
          cases a with
          | inl a =>
              cases b with
              | inl b =>
                  have ha := (S.adj_old_old i a).1 hia
                  have hb := (S.adj_old_old i b).1 hib
                  have hne : a.1 ≠ b.1 := by
                    intro he
                    exact hab (congrArg Sum.inl (Subtype.ext he))
                  exact (S.adj_old_old a b).2
                    (hsim (Finset.mem_univ _) (Finset.mem_univ _) ha hb hne)
              | inr q =>
                  exact False.elim (hnoNew q hib)
          | inr q =>
              exact False.elim (hnoNew q hia)
        · intro b hb
          cases b with
          | inl b =>
              exact hall b.1 ((S.adj_old_old i b).1 hb)
          | inr q =>
              exact False.elim (hnoNew q hb)

/-- Replacing a non-egg central block by an egg strictly increases egg
support, regardless of the status of the remainder blocks. -/
theorem eggSupport_ssubset [Fintype V] [Fintype I] [DecidableEq I]
    [Fintype (SplitIndex I J i₀)] [DecidableEq (SplitIndex I J i₀)]
    (w : V → ℝ)
    (hnot : ¬ IsEgg G w (P.block i₀))
    (hU : IsEgg G w S.U) :
    eggSupport P w ⊂ eggSupport S.partition w := by
  classical
  have hsubset : eggSupport P w ⊆ eggSupport S.partition w := by
    intro v hv
    obtain ⟨i, hi, hegg⟩ := (mem_eggSupport P w v).mp hv
    by_cases h : i = i₀
    · subst i
      exact False.elim (hnot hegg)
    · exact (mem_eggSupport S.partition w v).mpr
        ⟨.inl ⟨i, h⟩, hi, hegg⟩
  obtain ⟨v, hv⟩ := hU.nonempty
  have hnew : v ∈ eggSupport S.partition w :=
    (mem_eggSupport S.partition w v).mpr
      ⟨.inr none, hv, hU⟩
  have hold : v ∉ eggSupport P w := by
    intro hvold
    obtain ⟨i, hi, hegg⟩ := (mem_eggSupport P w v).mp hvold
    have hvi₀ : v ∈ P.block i₀ := S.U_subset hv
    by_cases h : i = i₀
    · subst i
      exact hnot hegg
    · exact (Set.disjoint_left.mp (P.disjoint h)) hi hvi₀
  exact ssubset_iff_subset_ne.mpr
    ⟨hsubset, by intro heq; exact hold (heq ▸ hnew)⟩

end CentralSplit

namespace Components

variable {P : ConnectedPartition G I} (i₀ : I) (U : Set V)

/-- The vertices of a connected component of the part of the central block
left after removing U. -/
def block
    (c : (G.induce (P.block i₀ \ U)).ConnectedComponent) : Set V :=
  {x | ∃ hx : x ∈ P.block i₀ \ U,
    (⟨x, hx⟩ : {v : V // v ∈ P.block i₀ \ U}) ∈ c.supp}

theorem block_subset_central
    (c : (G.induce (P.block i₀ \ U)).ConnectedComponent) :
    block i₀ U c ⊆ P.block i₀ := by
  rintro x ⟨hx, _⟩
  exact hx.1

theorem block_disjoint_U
    (c : (G.induce (P.block i₀ \ U)).ConnectedComponent) :
    Disjoint U (block i₀ U c) := by
  apply Set.disjoint_left.mpr
  rintro x hxU ⟨hx, _⟩
  exact hx.2 hxU

/-- Every vertex outside U belongs to its canonical component. -/
theorem cover (x : V) (hx : x ∈ P.block i₀)
    (hU : x ∉ U) :
    ∃ c : (G.induce (P.block i₀ \ U)).ConnectedComponent,
      x ∈ block i₀ U c := by
  let hxR : x ∈ P.block i₀ \ U := ⟨hx, hU⟩
  exact ⟨(G.induce (P.block i₀ \ U)).connectedComponentMk ⟨x, hxR⟩,
    ⟨hxR, rfl⟩⟩

/-- A component block, viewed as a subset of V, is connected. -/
theorem block_connected
    (c : (G.induce (P.block i₀ \ U)).ConnectedComponent) :
    (G.induce (block i₀ U c)).Connected := by
  classical
  let R : Set V := P.block i₀ \ U
  let H : SimpleGraph R := G.induce R
  let Z : Set V := block i₀ U c
  let e : (G.induce Z) ≃g (H.induce c.supp) := {
    toEquiv := {
      toFun := fun x => ⟨⟨x.1, Classical.choose x.2⟩,
        Classical.choose_spec x.2⟩
      invFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
      left_inv := by
        intro x
        exact Subtype.ext rfl
      right_inv := by
        intro x
        exact Subtype.ext (Subtype.ext rfl)
    }
    map_rel_iff' := by
      intro x y
      rfl
  }
  exact e.connected_iff.mpr c.connected_toSimpleGraph

/-- Different connected components produce disjoint subsets of the original
vertex type. -/
theorem block_disjoint (c d : (G.induce (P.block i₀ \ U)).ConnectedComponent)
    (hcd : c ≠ d) :
    Disjoint (block i₀ U c) (block i₀ U d) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨hx, hc⟩ ⟨hy, hd⟩
  have heq : (⟨x, hx⟩ : {v : V // v ∈ P.block i₀ \ U}) = ⟨x, hy⟩ :=
    Subtype.ext rfl
  exact hcd (SimpleGraph.ConnectedComponent.eq_of_common_vertex
    (heq ▸ hc) hd)

/-- Different connected components have no edge between them. -/
theorem no_cross (c d : (G.induce (P.block i₀ \ U)).ConnectedComponent)
    (hcd : c ≠ d) :
    ¬ ∃ x ∈ block i₀ U c, ∃ y ∈ block i₀ U d, G.Adj x y := by
  rintro ⟨x, ⟨hx, hc⟩, y, ⟨hy, hd⟩, hxy⟩
  have hadj : (G.induce (P.block i₀ \ U)).Adj ⟨x, hx⟩ ⟨y, hy⟩ :=
    hxy
  have hcy : (⟨y, hy⟩ : {v : V // v ∈ P.block i₀ \ U}) ∈ c.supp :=
    (c.mem_supp_congr_adj hadj).mp hc
  exact hcd (SimpleGraph.ConnectedComponent.eq_of_common_vertex hcy hd)

end Components

namespace CentralSplit

/-- Split a connected block along a connected subset, taking the connected
components of its complement as the remainder blocks. -/
noncomputable def ofComponents (P : ConnectedPartition G I) (i₀ : I)
    (U : Set V) (hconn : (G.induce U).Connected)
    (hsubset : U ⊆ P.block i₀) :
    CentralSplit P i₀
      (G.induce (P.block i₀ \ U)).ConnectedComponent where
  U := U
  remainder := Components.block i₀ U
  U_connected := hconn
  remainder_connected := Components.block_connected i₀ U
  U_subset := hsubset
  remainder_subset := Components.block_subset_central i₀ U
  U_remainder_disjoint := Components.block_disjoint_U i₀ U
  remainder_disjoint := by
    intro c d hcd
    exact Components.block_disjoint i₀ U c d hcd
  central_cover := by
    intro x hx
    by_cases hu : x ∈ U
    · exact Or.inl hu
    · exact Or.inr (Components.cover i₀ U x hx hu)

/-- Components of the complement of U satisfy the no-cross hypothesis of
the quotient update automatically. -/
theorem ofComponents_no_cross (P : ConnectedPartition G I) (i₀ : I)
    (U : Set V) (hconn : (G.induce U).Connected)
    (hsubset : U ⊆ P.block i₀) :
    ∀ c d : (G.induce (P.block i₀ \ U)).ConnectedComponent,
      c ≠ d →
      ¬ ∃ x ∈ (ofComponents P i₀ U hconn hsubset).remainder c,
        ∃ y ∈ (ofComponents P i₀ U hconn hsubset).remainder d,
          G.Adj x y := by
  intro c d hcd
  exact Components.no_cross i₀ U c d hcd

/-- The concrete final update: a connected egg U inside a non-egg central
block that meets every old quotient neighbor yields a new partial
egg-decomposition with strictly larger support. -/
theorem ofComponents_partial_and_support [Fintype V] [Fintype I]
    [DecidableEq I] (P : ConnectedPartition G I) (i₀ : I) (w : V → ℝ)
    (U : Set V)
    [Fintype (G.induce (P.block i₀ \ U)).ConnectedComponent]
    [Fintype (SplitIndex I
      (G.induce (P.block i₀ \ U)).ConnectedComponent i₀)]
    [DecidableEq (SplitIndex I
      (G.induce (P.block i₀ \ U)).ConnectedComponent i₀)] (hsubset : U ⊆ P.block i₀)
    (hU : IsEgg G w U)
    (hP : IsPartialEggDecomposition P w)
    (hnot : ¬ IsEgg G w (P.block i₀))
    (htouch : ∀ k, P.touchingQuotient.Adj i₀ k →
      ∃ x ∈ U, ∃ y ∈ P.block k, G.Adj x y) :
    IsPartialEggDecomposition
      (ofComponents P i₀ U hU.connected hsubset).partition w ∧
    eggSupport P w ⊂
      eggSupport (ofComponents P i₀ U hU.connected hsubset).partition w := by
  let S := ofComponents P i₀ U hU.connected hsubset
  have hno := ofComponents_no_cross P i₀ U hU.connected hsubset
  exact ⟨S.partition_isPartialEggDecomposition w hP hnot hU htouch hno,
    S.eggSupport_ssubset w hnot hU⟩

end CentralSplit
/-- The vertices of the central block with a neighbor in another block.
These are the terminal sets Nᵢ in Reed--Seymour, Section 2. -/
def terminalSet (P : ConnectedPartition G I) (i₀ i : I) : Set V :=
  {x | x ∈ P.block i₀ ∧ ∃ y ∈ P.block i, G.Adj x y}

/-- Every old quotient neighbor has a nonempty terminal set. -/
theorem terminalSet_nonempty_of_adj (P : ConnectedPartition G I)
    {i₀ i : I} (h : P.touchingQuotient.Adj i₀ i) :
    (terminalSet P i₀ i).Nonempty := by
  obtain ⟨_, x, hx, y, hy, hxy⟩ :=
    (P.touchingQuotient_adj_iff _ _).mp h
  exact ⟨x, hx, y, hy, hxy⟩

/-- Meeting every terminal set is exactly the quotient-neighbor retention
condition required by the concrete central update. -/
theorem touches_neighbors_of_meets_terminals
    (P : ConnectedPartition G I) (i₀ : I) (U : Set V)
    (hmeets : ∀ i, P.touchingQuotient.Adj i₀ i →
      (U ∩ terminalSet P i₀ i).Nonempty) :
    ∀ i, P.touchingQuotient.Adj i₀ i →
      ∃ x ∈ U, ∃ y ∈ P.block i, G.Adj x y := by
  intro i hi
  obtain ⟨x, hx⟩ := hmeets i hi
  exact ⟨x, hx.1, hx.2.2⟩

/-- A finite connected subset of the central block meeting the terminal
set of every old quotient neighbor. -/
def IsTerminalHittingSet (P : ConnectedPartition G I) (i₀ : I)
    (U : Finset V) : Prop :=
  (U : Set V) ⊆ P.block i₀ ∧
    (G.induce (U : Set V)).Connected ∧
    ∀ i, P.touchingQuotient.Adj i₀ i →
      ((U : Set V) ∩ terminalSet P i₀ i).Nonempty

/-- A connector of minimum cardinality exists, including when the central
block has no quotient neighbors. -/
theorem exists_minimal_terminal_connector [Fintype V]
    (P : ConnectedPartition G I) (i₀ : I) :
    ∃ U : Finset V, IsTerminalHittingSet P i₀ U ∧
      ∀ T : Finset V, IsTerminalHittingSet P i₀ T → U.card ≤ T.card := by
  classical
  let candidates : Finset (Finset V) :=
    Finset.univ.filter (IsTerminalHittingSet P i₀)
  let X : Finset V := Finset.univ.filter (· ∈ P.block i₀)
  have hX : (X : Set V) = P.block i₀ := by
    ext x
    simp [X]
  have hfull : IsTerminalHittingSet P i₀ X := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hX]
    · rw [hX]
      exact P.connected i₀
    · intro i hi
      obtain ⟨x, hx⟩ := terminalSet_nonempty_of_adj P hi
      exact ⟨x, ⟨by rw [hX]; exact hx.1, hx⟩⟩
  have hne : candidates.Nonempty := by
    refine ⟨X, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hfull
  obtain ⟨U, hUC, hmin⟩ := candidates.exists_min_image Finset.card hne
  have hU : IsTerminalHittingSet P i₀ U := by
    simpa only [candidates, Finset.mem_filter, Finset.mem_univ, true_and] using hUC
  refine ⟨U, hU, ?_⟩
  intro T hT
  apply hmin
  simpa only [candidates, Finset.mem_filter, Finset.mem_univ, true_and] using hT

/-- The chosen minimum-cardinality terminal connector is also
inclusion-minimal, the form used in the odd-cycle argument. -/
theorem exists_inclusion_minimal_terminal_connector [Fintype V]
    (P : ConnectedPartition G I) (i₀ : I) :
    ∃ U : Finset V, IsTerminalHittingSet P i₀ U ∧
      ∀ T : Finset V, T ⊂ U → ¬ IsTerminalHittingSet P i₀ T := by
  obtain ⟨U, hU, hmin⟩ := exists_minimal_terminal_connector P i₀
  refine ⟨U, hU, ?_⟩
  intro T hTU hT
  exact (not_le_of_gt (Finset.card_lt_card hTU)) (hmin T hT)

/-- A minimum terminal-hitting set cannot contain a proper connected
terminal-hitting subset. This is the finite form of the minimal transversal
hypothesis used in the parity argument. -/
theorem terminal_connector_subset_eq [Fintype V]
    (P : ConnectedPartition G I) (i₀ : I)
    {U T : Finset V}
    (hU : IsTerminalHittingSet P i₀ U)
    (hmin : ∀ T : Finset V, T ⊂ U → ¬ IsTerminalHittingSet P i₀ T)
    (hTU : T ⊆ U)
    (hconn : (G.induce (T : Set V)).Connected)
    (hmeets : ∀ i, P.touchingQuotient.Adj i₀ i →
      ((T : Set V) ∩ terminalSet P i₀ i).Nonempty) :
    T = U := by
  by_contra hne
  have hstrict : T ⊂ U := ssubset_iff_subset_ne.mpr ⟨hTU, hne⟩
  exact hmin T hstrict ⟨Set.Subset.trans
    (by exact_mod_cast hTU) hU.1, hconn, hmeets⟩

/-- The paper's terminal sets, restricted to a connector U, as vertex
sets in the induced graph on U. Labels are exactly the old quotient
neighbors of the central block. -/
def inducedTerminalSet (P : ConnectedPartition G I) (i₀ : I)
    (U : Set V)
    (i : {i : I // P.touchingQuotient.Adj i₀ i}) :
    Set {v : V // v ∈ U} :=
  {v | v.1 ∈ terminalSet P i₀ i.1}

/-- A minimum connector gives the minimal connected transversal hypothesis
used in the parity argument, after restricting the graph to U. -/
theorem minimal_hitting_set_is_minimal_transversal [Fintype V]
    (P : ConnectedPartition G I) (i₀ : I)
    {U : Finset V}
    (hU : IsTerminalHittingSet P i₀ U)
    (hmin : ∀ T : Finset V, T ⊂ U → ¬ IsTerminalHittingSet P i₀ T) :
    IsMinimalConnectedTransversal
      (G.induce (U : Set V))
      (inducedTerminalSet P i₀ (U : Set V)) := by
  classical
  refine ⟨hU.2.1, ?_, ?_⟩
  · intro i
    obtain ⟨v, hv⟩ := hU.2.2 i.1 i.2
    exact ⟨⟨v, hv.1⟩, hv.2⟩
  · intro S hSconn hSmeet
    let T : Finset V := Finset.univ.filter
      (fun v => ∃ hv : v ∈ (U : Set V),
        (⟨v, hv⟩ : {v : V // v ∈ (U : Set V)}) ∈ S)
    have hTmem (v : V) :
        v ∈ T ↔ ∃ hv : v ∈ (U : Set V),
          (⟨v, hv⟩ : {v : V // v ∈ (U : Set V)}) ∈ S := by
      simp [T]
    have hTU : T ⊆ U := by
      intro v hv
      exact ((hTmem v).mp hv).choose
    let e : (G.induce (T : Set V)) ≃g
        ((G.induce (U : Set V)).induce S) := {
      toEquiv := {
        toFun := fun x => ⟨⟨x.1, Classical.choose ((hTmem x.1).mp x.2)⟩,
          Classical.choose_spec ((hTmem x.1).mp x.2)⟩
        invFun := fun x => ⟨x.1.1, (hTmem x.1.1).mpr ⟨x.1.2, x.2⟩⟩
        left_inv := by
          intro x
          exact Subtype.ext rfl
        right_inv := by
          intro x
          exact Subtype.ext (Subtype.ext rfl)
      }
      map_rel_iff' := by
        intro x y
        rfl
    }
    have hTconn : (G.induce (T : Set V)).Connected :=
      e.connected_iff.mpr hSconn
    have hTmeet : ∀ i, P.touchingQuotient.Adj i₀ i →
        ((T : Set V) ∩ terminalSet P i₀ i).Nonempty := by
      intro i hi
      obtain ⟨v, hvN, hvS⟩ := hSmeet ⟨i, hi⟩
      exact ⟨v.1, (hTmem v.1).mpr ⟨v.2, hvS⟩, hvN⟩
    have hTUeq : T = U :=
      terminal_connector_subset_eq P i₀ hU hmin hTU hTconn hTmeet
    apply Set.eq_univ_of_forall
    intro v
    have hvT : v.1 ∈ T := by
      rw [hTUeq]
      exact v.2
    obtain ⟨hu, hs⟩ := (hTmem v.1).mp hvT
    have heq : (⟨v.1, hu⟩ : {x : V // x ∈ (U : Set V)}) = v :=
      Subtype.ext rfl
    exact heq ▸ hs

end ReedSeymour
end HadwigerLean
