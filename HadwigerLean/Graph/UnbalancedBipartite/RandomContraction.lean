import HadwigerLean.Graph.UnbalancedBipartite.NearComplete
import HadwigerLean.Graph.MinorFree
import Mathlib.Tactic

/-!
# Star contractions onto a selected bipartition side

A choice of one adjacent center for each opposite-side vertex gives a
minor on the selected centers. Random choices in Appendix C will later be
applied to this deterministic construction.
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The graph obtained by assigning every vertex of `A` to a center in `X`
and contracting its attachment edge. All surviving center-to-center edges
are retained. -/
def starContractionGraph (G : SimpleGraph V) (A X : Finset V)
    (f : ↥(A : Set V) → ↥(X : Set V)) : SimpleGraph (X : Set V) where
  Adj x y := x ≠ y ∧ (G.Adj x.1 y.1 ∨
    ∃ w : (A : Set V),
      (f w = x ∧ G.Adj w.1 y.1) ∨
      (f w = y ∧ G.Adj w.1 x.1))
  symm := by
    constructor
    intro x y h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with hxy | ⟨w, hw⟩
    · exact Or.inl hxy.symm
    · exact Or.inr ⟨w, hw.symm⟩
  loopless := by
    constructor
    intro x h
    exact h.1 rfl

private def starBranch (A X : Finset V)
    (f : ↥(A : Set V) → ↥(X : Set V)) (x : (X : Set V)) : Set V :=
  {v | v = x.1 ∨ ∃ w : (A : Set V), f w = x ∧ w.1 = v}

/-- The star contraction is a minor whenever each assignment follows an
edge and the attached vertices lie outside the center set. -/
noncomputable def starContractionMinorModel
    (G : SimpleGraph V) (A X : Finset V)
    (hAX : Disjoint A X)
    (f : ↥(A : Set V) → ↥(X : Set V))
    (hf : ∀ w, G.Adj w.1 (f w).1) :
    MinorModel (starContractionGraph G A X f) G := by
  classical
  let B : ↥(X : Set V) → Set V := starBranch A X f
  have hcenter (x : (X : Set V)) : x.1 ∈ B x := Or.inl rfl
  have hconn (x : (X : Set V)) : (G.induce (B x)).Connected := by
    let J := G.induce (B x)
    haveI : Nonempty (B x) := ⟨⟨x.1, hcenter x⟩⟩
    have hreach (z : (B x)) : J.Reachable ⟨x.1, hcenter x⟩ z := by
      rcases z.2 with heq | ⟨w, hfw, hwz⟩
      · have hz : z = ⟨x.1, hcenter x⟩ := Subtype.ext heq
        rw [hz]
      · have hzx : G.Adj x.1 z.1 := by
          rw [← hwz, ← hfw]
          exact (hf w).symm
        exact (show J.Adj ⟨x.1, hcenter x⟩ z from hzx).reachable
    refine (SimpleGraph.connected_iff J).mpr ⟨?_, inferInstance⟩
    intro p q
    exact (hreach p).symm.trans (hreach q)
  have hdis : Pairwise (fun x y : (X : Set V) => Disjoint (B x) (B y)) := by
    intro x y hxy
    apply Set.disjoint_left.mpr
    intro v hvx hvy
    rcases hvx with hx | ⟨wx, hfx, hwx⟩
    · rcases hvy with hy | ⟨wy, hfy, hwy⟩
      · exact hxy (Subtype.ext (hx.symm.trans hy))
      · have hvX : v ∈ X := hx ▸ x.property
        have hvA : v ∈ A := hwy ▸ wy.property
        exact (Finset.disjoint_left.mp hAX) hvA hvX
    · rcases hvy with hy | ⟨wy, hfy, hwy⟩
      · have hvA : v ∈ A := hwx ▸ wx.property
        have hvX : v ∈ X := hy ▸ y.property
        exact (Finset.disjoint_left.mp hAX) hvA hvX
      · have heq : wx = wy := Subtype.ext (hwx.trans hwy.symm)
        subst wy
        exact hxy (hfx.symm.trans hfy)
  let M : MinorModel (starContractionGraph G A X f) G := {
    branch := B
    connected := hconn
    disjoint := hdis
    adjacent := by
      intro x y hxy
      rcases hxy.2 with h | ⟨w, hw⟩
      · exact ⟨x.1, Or.inl rfl, y.1, Or.inl rfl, h⟩
      · rcases hw with ⟨hfw, hwy⟩ | ⟨hfw, hwx⟩
        · exact ⟨w.1, Or.inr ⟨w, hfw, rfl⟩,
            y.1, Or.inl rfl, hwy⟩
        · exact ⟨x.1, Or.inl rfl,
            w.1, Or.inr ⟨w, hfw, rfl⟩, hwx.symm⟩
  }
  exact M

/-- The explicit star branch-set model witnesses the minor relation. -/
theorem starContractionGraph_isMinor
    (G : SimpleGraph V) (A X : Finset V)
    (hAX : Disjoint A X)
    (f : ↥(A : Set V) → ↥(X : Set V))
    (hf : ∀ w, G.Adj w.1 (f w).1) :
    IsMinor (starContractionGraph G A X f) G :=
  ⟨starContractionMinorModel G A X hAX f hf⟩

/-- A common neighbor assigned to either endpoint creates their edge in
the star-contraction graph. -/
theorem starContractionGraph_adj_of_common_assignment
    (G : SimpleGraph V) (A X : Finset V)
    (f : ↥(A : Set V) → ↥(X : Set V))
    (x y : ↥(X : Set V)) (hxy : x ≠ y)
    (w : ↥(A : Set V))
    (hwx : G.Adj w.1 x.1) (hwy : G.Adj w.1 y.1)
    (hassigned : f w = x ∨ f w = y) :
    (starContractionGraph G A X f).Adj x y := by
  refine ⟨hxy, Or.inr ⟨w, ?_⟩⟩
  rcases hassigned with h | h
  · exact Or.inl ⟨h, hwy⟩
  · exact Or.inr ⟨h, hwx⟩

/-- A missing edge after star contraction means every original common
neighbor was assigned away from both endpoints. -/
theorem starContractionGraph_missing_avoids_common
    (G : SimpleGraph V) (A X : Finset V)
    (f : ↥(A : Set V) → ↥(X : Set V))
    (x y : ↥(X : Set V)) (hxy : x ≠ y)
    (hmiss : ¬ (starContractionGraph G A X f).Adj x y)
    (w : ↥(A : Set V))
    (hwx : G.Adj w.1 x.1) (hwy : G.Adj w.1 y.1) :
    f w ≠ x ∧ f w ≠ y := by
  constructor
  · intro h
    exact hmiss (starContractionGraph_adj_of_common_assignment
      G A X f x y hxy w hwx hwy (Or.inl h))
  · intro h
    exact hmiss (starContractionGraph_adj_of_common_assignment
      G A X f x y hxy w hwx hwy (Or.inr h))

/-- The finite product of admissible choices, one choice per attached
vertex. -/
def starAssignmentFinset (A : Finset V)
    (C : ↥(A : Set V) → Finset V) :
    Finset (↥(A : Set V) → V) :=
  Fintype.piFinset C

@[simp] theorem card_starAssignmentFinset
    (A : Finset V) (C : ↥(A : Set V) → Finset V) :
    (starAssignmentFinset A C).card =
      ∏ w : ↥(A : Set V), (C w).card := by
  classical
  simp [starAssignmentFinset]

@[simp] theorem mem_starAssignmentFinset
    (A : Finset V) (C : ↥(A : Set V) → Finset V)
    (f : ↥(A : Set V) → V) :
    f ∈ starAssignmentFinset A C ↔ ∀ w, f w ∈ C w := by
  classical
  simp [starAssignmentFinset, Fintype.mem_piFinset]

/-- Remove two forbidden center choices at each index in `W`. -/
def avoidPairChoices (A : Finset V)
    (C : ↥(A : Set V) → Finset V)
    (W : Finset ↥(A : Set V)) (x y : V) :
    ↥(A : Set V) → Finset V :=
  fun w => if w ∈ W then (C w).erase x |>.erase y else C w

/-- Independent assignments avoiding two centers on `W` are counted by
the product of the reduced local choice sets. -/
theorem card_star_assignments_avoiding_pair_le_prod
    (A : Finset V) (C : ↥(A : Set V) → Finset V)
    (W : Finset ↥(A : Set V)) (x y : V) :
    (starAssignmentFinset A C |>.filter (fun f =>
      ∀ w ∈ W, f w ≠ x ∧ f w ≠ y)).card ≤
      ∏ w : ↥(A : Set V),
        (avoidPairChoices A C W x y w).card := by
  classical
  have hsub :
      (starAssignmentFinset A C |>.filter (fun f =>
        ∀ w ∈ W, f w ≠ x ∧ f w ≠ y)) ⊆
        Fintype.piFinset (avoidPairChoices A C W x y) := by
    intro f hf
    have hfC := (mem_starAssignmentFinset A C f).mp
      (Finset.mem_filter.mp hf).1
    have hfavoid := (Finset.mem_filter.mp hf).2
    apply Fintype.mem_piFinset.mpr
    intro w
    by_cases hw : w ∈ W
    · have hxy := hfavoid w hw
      simp [avoidPairChoices, hw, Finset.mem_erase, hxy.1, hxy.2, hfC w]
    · simpa [avoidPairChoices, hw] using hfC w
  calc
    _ ≤ (Fintype.piFinset (avoidPairChoices A C W x y)).card :=
      Finset.card_le_card hsub
    _ = _ := Fintype.card_piFinset _

/-- At a common neighbor, excluding two distinct centers removes exactly
two local choices. -/
theorem card_avoidPairChoices_add_two
    (A : Finset V) (C : ↥(A : Set V) → Finset V)
    (W : Finset ↥(A : Set V)) (x y : V) (hxy : x ≠ y)
    (w : ↥(A : Set V)) (hw : w ∈ W)
    (hx : x ∈ C w) (hy : y ∈ C w) :
    (avoidPairChoices A C W x y w).card + 2 = (C w).card := by
  classical
  have hy' : y ∈ (C w).erase x :=
    Finset.mem_erase.mpr ⟨hxy.symm, hy⟩
  have hc : 2 ≤ (C w).card := by
    have h := (Finset.one_lt_card).mpr ⟨x, hx, y, hy, hxy⟩
    omega
  simp [avoidPairChoices, hw, Finset.card_erase_of_mem, hx, hy']
  omega

/-- Outside the selected common-neighbor set, local choices are unchanged. -/
theorem avoidPairChoices_eq_of_not_mem
    (A : Finset V) (C : ↥(A : Set V) → Finset V)
    (W : Finset ↥(A : Set V)) (x y : V)
    (w : ↥(A : Set V)) (hw : w ∉ W) :
    avoidPairChoices A C W x y w = C w := by
  simp [avoidPairChoices, hw]

/-- The ratio of choices avoiding two centers is bounded by a product of
identical local failure factors. -/
theorem card_star_assignments_avoiding_pair_le_factor
    (A : Finset V) (C : ↥(A : Set V) → Finset V)
    (W : Finset ↥(A : Set V)) (x y : V) (hxy : x ≠ y)
    (n : ℕ) (hn : 2 ≤ n)
    (hmax : ∀ w, (C w).card ≤ n)
    (hxyC : ∀ w ∈ W, x ∈ C w ∧ y ∈ C w) :
    ((starAssignmentFinset A C |>.filter (fun f =>
      ∀ w ∈ W, f w ≠ x ∧ f w ≠ y)).card : ℝ) ≤
      ((starAssignmentFinset A C).card : ℝ) *
        (1 - 2 / (n : ℝ)) ^ W.card := by
  classical
  let α : ℝ := 1 - 2 / (n : ℝ)
  let D := avoidPairChoices A C W x y
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hα : 0 ≤ α := by
    dsimp [α]
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hnR).mpr
    have hnCast : (2 : ℝ) ≤ n := by exact_mod_cast hn
    simpa using hnCast
  have hpoint (w : ↥(A : Set V)) :
      ((D w).card : ℝ) ≤ ((C w).card : ℝ) *
        (if w ∈ W then α else 1) := by
    by_cases hw : w ∈ W
    · have hcard := card_avoidPairChoices_add_two A C W x y hxy w hw
        (hxyC w hw).1 (hxyC w hw).2
      have hmaxR : ((C w).card : ℝ) ≤ n := by exact_mod_cast hmax w
      have hrat : ((C w).card : ℝ) * 2 / n ≤ 2 := by
        apply (div_le_iff₀ hnR).mpr
        nlinarith
      simp only [if_pos hw]
      have hcardR : ((D w).card : ℝ) + 2 = (C w).card := by
        exact_mod_cast hcard
      dsimp [α]
      calc
        ((D w).card : ℝ) = (C w).card - 2 := by linarith
        _ ≤ (C w).card - (C w).card * 2 / n := by linarith
        _ = (C w).card * (1 - 2 / n) := by ring
    · simp [D, avoidPairChoices, hw]
  have hprod :
      (∏ w : ↥(A : Set V), ((D w).card : ℝ)) ≤
      ∏ w : ↥(A : Set V),
        (((C w).card : ℝ) * (if w ∈ W then α else 1)) := by
    apply Finset.prod_le_prod
    · intro w hw
      positivity
    · intro w hw
      exact hpoint w
  have hfactor :
      (∏ w : ↥(A : Set V), if w ∈ W then α else 1) = α ^ W.card := by
    rw [Fintype.prod_ite_mem]
    simp
  have hcardAll : ((starAssignmentFinset A C).card : ℝ) =
      ∏ w : ↥(A : Set V), ((C w).card : ℝ) := by
    rw [card_starAssignmentFinset]
    exact_mod_cast (Finset.prod_natCast (Finset.univ : Finset ↥(A : Set V)) (fun w => (C w).card))
  have hcardD : ((starAssignmentFinset A C |>.filter (fun f =>
      ∀ w ∈ W, f w ≠ x ∧ f w ≠ y)).card : ℝ) ≤
      ∏ w : ↥(A : Set V), ((D w).card : ℝ) := by
    exact_mod_cast card_star_assignments_avoiding_pair_le_prod A C W x y
  calc
    _ ≤ ∏ w : ↥(A : Set V), ((D w).card : ℝ) := hcardD
    _ ≤ ∏ w : ↥(A : Set V),
        (((C w).card : ℝ) * (if w ∈ W then α else 1)) := hprod
    _ = ((starAssignmentFinset A C).card : ℝ) * α ^ W.card := by
      rw [Finset.prod_mul_distrib, ← hcardAll, hfactor]
    _ = _ := rfl

/-- The exponential form of the independent-assignment failure bound. -/
theorem card_star_assignments_avoiding_pair_le_exp
    (A : Finset V) (C : ↥(A : Set V) → Finset V)
    (W : Finset ↥(A : Set V)) (x y : V) (hxy : x ≠ y)
    (n : ℕ) (hn : 2 ≤ n)
    (hmax : ∀ w, (C w).card ≤ n)
    (hxyC : ∀ w ∈ W, x ∈ C w ∧ y ∈ C w) :
    ((starAssignmentFinset A C |>.filter (fun f =>
      ∀ w ∈ W, f w ≠ x ∧ f w ≠ y)).card : ℝ) ≤
      ((starAssignmentFinset A C).card : ℝ) *
        Real.exp (-(2 * (W.card : ℝ) / (n : ℝ))) := by
  have hfactor := card_star_assignments_avoiding_pair_le_factor
    A C W x y hxy n hn hmax hxyC
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hbaseNonneg : 0 ≤ (1 - 2 / (n : ℝ)) := by
    have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact sub_nonneg.mpr ((div_le_iff₀ hnR).mpr (by simpa using hnr))
  have hbase : 1 - 2 / (n : ℝ) ≤ Real.exp (-(2 / (n : ℝ))) := by
    have h := Real.add_one_le_exp (-(2 / (n : ℝ)))
    nlinarith
  have hpow := pow_le_pow_left₀ hbaseNonneg hbase W.card
  have hexp : (Real.exp (-(2 / (n : ℝ)))) ^ W.card =
      Real.exp (-(2 * (W.card : ℝ) / (n : ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp] at hpow
  have hcardNonneg : 0 ≤ ((starAssignmentFinset A C).card : ℝ) := by positivity
  exact hfactor.trans (mul_le_mul_of_nonneg_left hpow hcardNonneg)

/-- The available center choices for an attached vertex. -/
def starNeighborChoices (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (w : V) : Finset V :=
  G.neighborFinset w ∩ X

/-- Turn a tuple of adjacent center choices into a subtype-valued
assignment for the star-contraction model. -/
def starAssignedCenter (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V)
    (g : ↥(starAssignmentFinset A
      (fun w : ↥(A : Set V) => starNeighborChoices G X w.1))) :
    ↥(A : Set V) → ↥(X : Set V) := by
  classical
  intro w
  have hg := (mem_starAssignmentFinset A
    (fun w : ↥(A : Set V) => starNeighborChoices G X w.1) g.1).mp g.2 w
  exact ⟨g.1 w, (Finset.mem_inter.mp hg).2⟩

/-- Every chosen assignment follows a graph edge. -/
theorem starAssignedCenter_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V)
    (g : ↥(starAssignmentFinset A
      (fun w : ↥(A : Set V) => starNeighborChoices G X w.1)))
    (w : ↥(A : Set V)) :
    G.Adj w.1 (starAssignedCenter G A X g w).1 := by
  classical
  have hg := (mem_starAssignmentFinset A
    (fun w : ↥(A : Set V) => starNeighborChoices G X w.1) g.1).mp g.2 w
  exact (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hg).1

/-- Each admissible tuple of neighbor choices produces a graph minor. -/
theorem starContractionGraph_isMinor_of_neighbor_assignment
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) (hAX : Disjoint A X)
    (g : ↥(starAssignmentFinset A
      (fun w : ↥(A : Set V) => starNeighborChoices G X w.1))) :
    IsMinor (starContractionGraph G A X
      (starAssignedCenter G A X g)) G :=
  starContractionGraph_isMinor G A X hAX
    (starAssignedCenter G A X g) (starAssignedCenter_adj G A X g)

/-- A missing contracted edge forces every selected common neighbor to
avoid assigning itself to either endpoint. -/
theorem starAssignment_missing_avoids_common
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) (x y : ↥(X : Set V)) (hxy : x ≠ y)
    (W : Finset ↥(A : Set V))
    (hcommon : ∀ w ∈ W, G.Adj w.1 x.1 ∧ G.Adj w.1 y.1)
    (g : ↥(starAssignmentFinset A
      (fun w : ↥(A : Set V) => starNeighborChoices G X w.1)))
    (hmiss : ¬ (starContractionGraph G A X
      (starAssignedCenter G A X g)).Adj x y) :
    ∀ w ∈ W, g.1 w ≠ x.1 ∧ g.1 w ≠ y.1 := by
  intro w hw
  have h := starContractionGraph_missing_avoids_common
    G A X (starAssignedCenter G A X g) x y hxy hmiss w
    (hcommon w hw).1 (hcommon w hw).2
  constructor
  · intro heq
    apply h.1
    apply Subtype.ext
    exact heq
  · intro heq
    apply h.2
    apply Subtype.ext
    exact heq

/-- Assignments whose contracted graph misses a fixed pair. -/
noncomputable def starMissingAssignments
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) (x y : ↥(X : Set V)) :
    Finset ↥(starAssignmentFinset A
      (fun w : ↥(A : Set V) => starNeighborChoices G X w.1)) := by
  classical
  exact Finset.univ.filter (fun g =>
    ¬ (starContractionGraph G A X
      (starAssignedCenter G A X g)).Adj x y)
/-- The finite-sample version of the pair-failure probability estimate
(C.6), before replacing the common-neighbor count by its lower bound. -/
theorem card_star_assignments_missing_pair_le_exp
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) (x y : ↥(X : Set V)) (hxy : x ≠ y)
    (W : Finset ↥(A : Set V))
    (hcommon : ∀ w ∈ W, G.Adj w.1 x.1 ∧ G.Adj w.1 y.1)
    (hn : 2 ≤ X.card) :
    ((starMissingAssignments G A X x y).card : ℝ) ≤
      ((starAssignmentFinset A
        (fun w : ↥(A : Set V) => starNeighborChoices G X w.1)).card : ℝ) *
        Real.exp (-(2 * (W.card : ℝ) / (X.card : ℝ))) := by
  classical
  let C : ↥(A : Set V) → Finset V :=
    fun w => starNeighborChoices G X w.1
  let Ω := starAssignmentFinset A C
  let Bad : Finset Ω := starMissingAssignments G A X x y
  have hsub : Bad.image Subtype.val ⊆
      Ω.filter (fun f => ∀ w ∈ W, f w ≠ x.1 ∧ f w ≠ y.1) := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    have hgBad : ¬ (starContractionGraph G A X
      (starAssignedCenter G A X g)).Adj x y :=
      (Finset.mem_filter.mp hg).2
    exact Finset.mem_filter.mpr ⟨g.2,
      starAssignment_missing_avoids_common G A X x y hxy W hcommon g hgBad⟩
  have hcard : Bad.card ≤
      (Ω.filter (fun f => ∀ w ∈ W, f w ≠ x.1 ∧ f w ≠ y.1)).card := by
    have h := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective] at h
    exact Subtype.val_injective
  have hmax : ∀ w : ↥(A : Set V), (C w).card ≤ X.card := by
    intro w
    exact Finset.card_le_card Finset.inter_subset_right
  have hxyC : ∀ w ∈ W, x.1 ∈ C w ∧ y.1 ∈ C w := by
    intro w hw
    exact ⟨Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset _ _).mpr (hcommon w hw).1, x.property⟩,
      Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset _ _).mpr (hcommon w hw).2, y.property⟩⟩
  have hExp := card_star_assignments_avoiding_pair_le_exp
    A C W x.1 y.1 (fun h => hxy (Subtype.ext h)) X.card hn hmax hxyC
  have hcardR : (Bad.card : ℝ) ≤
      ((Ω.filter (fun f => ∀ w ∈ W, f w ≠ x.1 ∧ f w ≠ y.1)).card : ℝ) := by
    exact_mod_cast hcard
  exact hcardR.trans hExp

/-- Finite double counting: a uniform upper bound on each event's
frequency gives an outcome with at most the same fraction of failures. -/
theorem exists_outcome_with_few_failures
    {Ω E : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype E] [DecidableEq E]
    (S : Finset Ω) (T : Finset E) (P : Ω → E → Prop)
    [DecidableRel P] (hS : S.Nonempty) (q : ℝ)
    (hevent : ∀ e ∈ T,
      ((S.filter (fun ω => P ω e)).card : ℝ) ≤ q * (S.card : ℝ)) :
    ∃ ω ∈ S, ((T.filter (P ω)).card : ℝ) ≤ q * (T.card : ℝ) := by
  classical
  have hswap :
      (∑ ω ∈ S, ((T.filter (P ω)).card : ℝ)) =
        ∑ e ∈ T, ((S.filter (fun ω => P ω e)).card : ℝ) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero]
    rw [Finset.sum_comm]
  have hsum :
      (∑ ω ∈ S, ((T.filter (P ω)).card : ℝ)) ≤
        ∑ _ω ∈ S, q * (T.card : ℝ) := by
    rw [hswap]
    have h := Finset.sum_le_sum (s := T) (fun e he => hevent e he)
    simp at h ⊢
    nlinarith [h]
  exact Finset.exists_le_of_sum_le hS hsum

/-- Common attached vertices for a pair of selected centers. -/
def starCommonNeighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) (x y : ↥(X : Set V)) :
    Finset ↥(A : Set V) := by
  classical
  exact Finset.univ.filter (fun w => G.Adj w.1 x.1 ∧ G.Adj w.1 y.1)

/-- Equation (C.6) with an explicit lower bound on the number of common
neighbors. -/
theorem card_star_assignments_missing_pair_le_exp_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) (x y : ↥(X : Set V)) (hxy : x ≠ y)
    (s : ℕ) (hs : s ≤ (starCommonNeighbors G A X x y).card)
    (hn : 2 ≤ X.card) :
    ((starMissingAssignments G A X x y).card : ℝ) ≤
      ((starAssignmentFinset A
        (fun w : ↥(A : Set V) => starNeighborChoices G X w.1)).card : ℝ) *
        Real.exp (-(2 * (s : ℝ) / (X.card : ℝ))) := by
  classical
  let W := starCommonNeighbors G A X x y
  have hcommon : ∀ w ∈ W, G.Adj w.1 x.1 ∧ G.Adj w.1 y.1 := by
    intro w hw
    exact (Finset.mem_filter.mp hw).2
  have hbase := card_star_assignments_missing_pair_le_exp
    G A X x y hxy W hcommon hn
  have hnR : (0 : ℝ) < X.card := by exact_mod_cast (by omega : 0 < X.card)
  have hsR : (s : ℝ) ≤ W.card := by exact_mod_cast hs
  have hexp : Real.exp (-(2 * (W.card : ℝ) / (X.card : ℝ))) ≤
      Real.exp (-(2 * (s : ℝ) / (X.card : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hdiv : (2 * (s : ℝ)) / (X.card : ℝ) ≤
        (2 * (W.card : ℝ)) / (X.card : ℝ) := by
      apply (div_le_div_iff₀ hnR hnR).mpr
      nlinarith
    exact neg_le_neg hdiv
  exact hbase.trans (mul_le_mul_of_nonneg_left hexp (by positivity))

/-- Missing edges of one star-contraction outcome, measured against all
unordered center pairs. -/
noncomputable def starMissingEdges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V)
    (g : ↥(starAssignmentFinset A
      (fun w : ↥(A : Set V) => starNeighborChoices G X w.1))) :
    Finset (Sym2 ↥(X : Set V)) := by
  classical
  exact (⊤ : SimpleGraph ↥(X : Set V)).edgeFinset.filter
    (fun e => e ∉ (starContractionGraph G A X
      (starAssignedCenter G A X g)).edgeFinset)

/-- Averaging the fixed-pair estimate gives one contraction outcome with
at most the predicted missing-edge fraction. -/
theorem exists_star_assignment_with_few_missing_edges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) (s : ℕ) (hn : 2 ≤ X.card)
    (hchoices : ∀ w ∈ A, ∃ x ∈ X, G.Adj w x)
    (hcommon : ∀ x y : ↥(X : Set V), x ≠ y →
      s ≤ (starCommonNeighbors G A X x y).card) :
    ∃ g : ↥(starAssignmentFinset A
      (fun w : ↥(A : Set V) => starNeighborChoices G X w.1)),
      ((starMissingEdges G A X g).card : ℝ) ≤
        ((X.card.choose 2 : ℕ) : ℝ) *
          Real.exp (-(2 * (s : ℝ) / (X.card : ℝ))) := by
  classical
  let C : ↥(A : Set V) → Finset V :=
    fun w => starNeighborChoices G X w.1
  let Ω := starAssignmentFinset A C
  let E := (⊤ : SimpleGraph ↥(X : Set V)).edgeFinset
  let P : Ω → Sym2 ↥(X : Set V) → Prop := fun g e =>
    e ∉ (starContractionGraph G A X
      (starAssignedCenter G A X g)).edgeFinset
  have hΩnonempty : Ω.Nonempty := by
    apply Fintype.piFinset_nonempty.mpr
    intro w
    obtain ⟨x, hx, hwx⟩ := hchoices w.1 w.property
    exact ⟨x, Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset _ _).mpr hwx, hx⟩⟩
  have hS : (Finset.univ : Finset Ω).Nonempty := by
    obtain ⟨g, hg⟩ := hΩnonempty
    exact ⟨⟨g, hg⟩, Finset.mem_univ _⟩
  have hpair (e : Sym2 ↥(X : Set V)) (he : e ∈ E) :
      (((Finset.univ : Finset Ω).filter (fun g => P g e)).card : ℝ) ≤
        Real.exp (-(2 * (s : ℝ) / (X.card : ℝ))) *
          ((Finset.univ : Finset Ω).card : ℝ) := by
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hxy : x ≠ y := by
        simpa [E, SimpleGraph.mem_edgeFinset] using he
      have hEq :
          ((Finset.univ : Finset Ω).filter (fun g => P g (s(x, y)))).card =
            (starMissingAssignments G A X x y).card := by
        congr 1
        ext g
        simp [P, starMissingAssignments, SimpleGraph.mem_edgeFinset]
      rw [hEq]
      have h := card_star_assignments_missing_pair_le_exp_lower
        G A X x y hxy s (hcommon x y hxy) hn
      simpa [Ω, C, mul_comm] using h
  obtain ⟨g, _, hg⟩ := exists_outcome_with_few_failures
    (Finset.univ : Finset Ω) E P hS
    (Real.exp (-(2 * (s : ℝ) / (X.card : ℝ)))) hpair
  refine ⟨g, ?_⟩
  have hE : E.card = X.card.choose 2 := by
    rw [show E = (⊤ : SimpleGraph ↥(X : Set V)).edgeFinset by rfl,
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    congr 1
    apply Fintype.card_of_subtype
    intro v
    simp
  rw [← hE]
  simpa only [starMissingEdges, E, P, mul_comm] using hg

/-- The counted missing center pairs are exactly the complement edges of
the contracted graph. -/
theorem starMissingEdges_card_eq_complement_edgeCount
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V)
    (g : ↥(starAssignmentFinset A
      (fun w : ↥(A : Set V) => starNeighborChoices G X w.1))) :
    (starMissingEdges G A X g).card =
      edgeCount (starContractionGraph G A X
        (starAssignedCenter G A X g))ᶜ := by
  classical
  rw [edgeCount_eq_card_edgeFinset]
  congr 1
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
    simp [starMissingEdges, SimpleGraph.mem_edgeFinset,
      SimpleGraph.compl_adj]

/-- The random-contraction step of Appendix C, packaged as the existence
of a minor with few missing edges. -/
theorem exists_star_contraction_minor_with_few_missing_edges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) (hAX : Disjoint A X)
    (s : ℕ) (hn : 2 ≤ X.card)
    (hchoices : ∀ w ∈ A, ∃ x ∈ X, G.Adj w x)
    (hcommon : ∀ x y : ↥(X : Set V), x ≠ y →
      s ≤ (starCommonNeighbors G A X x y).card) :
    ∃ H : SimpleGraph ↥(X : Set V),
      IsMinor H G ∧
      (edgeCount Hᶜ : ℝ) ≤
        ((X.card.choose 2 : ℕ) : ℝ) *
          Real.exp (-(2 * (s : ℝ) / (X.card : ℝ))) := by
  classical
  obtain ⟨g, hmissing⟩ :=
    exists_star_assignment_with_few_missing_edges G A X s hn hchoices hcommon
  let H := starContractionGraph G A X (starAssignedCenter G A X g)
  refine ⟨H, starContractionGraph_isMinor_of_neighbor_assignment
    G A X hAX g, ?_⟩
  rw [← starMissingEdges_card_eq_complement_edgeCount G A X g]
  exact hmissing

/-- A vertex touching every branch of a clique-minor model gives one
additional singleton branch. -/
theorem hasCliqueMinor_succ_of_touched_model
    {n : ℕ} (G : SimpleGraph V)
    (M : MinorModel (SimpleGraph.completeGraph (Fin n)) G)
    (v : V) (hv : ∀ i, v ∉ M.branch i)
    (htouch : ∀ i, ∃ x ∈ M.branch i, G.Adj v x) :
    HasCliqueMinor G (n + 1) := by
  classical
  have hdis (i : Fin n) : Disjoint ({v} : Set V) (M.branch i) := by
    apply Set.disjoint_left.mpr
    intro x hx hxi
    have heq : x = v := by simpa using hx
    subst x
    exact hv i hxi
  refine ⟨{
    branch := Fin.cases {v} M.branch
    connected := ?_
    disjoint := ?_
    adjacent := ?_
  }⟩
  · intro i
    cases i using Fin.cases with
    | zero => simp
    | succ i => exact M.connected i
  · intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => exact hdis j
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (hdis i).symm
      | succ j =>
        apply M.disjoint
        intro heq
        exact hij (congrArg Fin.succ heq)
  · intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (hij.ne rfl).elim
      | succ j =>
        obtain ⟨x, hx, hvx⟩ := htouch j
        exact ⟨v, by simp, x, hx, hvx⟩
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        obtain ⟨x, hx, hvx⟩ := htouch i
        exact ⟨x, hx, v, by simp, hvx.symm⟩
      | succ j =>
        apply M.adjacent
        intro heq
        exact hij.ne (congrArg Fin.succ heq)

/-- A complete star-contraction graph, together with a vertex adjacent
to every center, yields one larger clique minor. -/
theorem hasCliqueMinor_succ_of_complete_star_assignment
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) (hAX : Disjoint A X)
    (g : ↥(starAssignmentFinset A
      (fun w : ↥(A : Set V) => starNeighborChoices G X w.1)))
    (v : V) (hvA : v ∉ A) (hvX : v ∉ X)
    (hneighbor : ∀ x ∈ X, G.Adj v x)
    (hcomplete : ∀ x y : ↥(X : Set V), x ≠ y →
      (starContractionGraph G A X
        (starAssignedCenter G A X g)).Adj x y) :
    HasCliqueMinor G (Fintype.card ↥(X : Set V) + 1) := by
  classical
  let f := starAssignedCenter G A X g
  let M := starContractionMinorModel G A X hAX f
    (starAssignedCenter_adj G A X g)
  let e : Fin (Fintype.card ↥(X : Set V)) ≃ ↥(X : Set V) :=
    (Fintype.equivFin ↥(X : Set V)).symm
  let N : MinorModel
      (SimpleGraph.completeGraph (Fin (Fintype.card ↥(X : Set V)))) G := {
    branch := fun i => M.branch (e i)
    connected := fun i => M.connected (e i)
    disjoint := by
      intro i j hij
      apply M.disjoint
      intro heq
      exact hij (e.injective heq)
    adjacent := by
      intro i j hij
      apply M.adjacent
      apply hcomplete
      intro heq
      have hne : i ≠ j := by simpa using hij
      exact hne (e.injective heq)
  }
  apply hasCliqueMinor_succ_of_touched_model G N v
  · intro i hvi
    change v ∈ starBranch A X f (e i) at hvi
    rcases hvi with heq | ⟨w, _, hw⟩
    · exact hvX (heq ▸ (e i).property)
    · exact hvA (hw.symm ▸ w.property)
  · intro i
    exact ⟨(e i).1, Or.inl rfl, hneighbor (e i).1 (e i).property⟩

/-- Zero missing pairs means every two distinct centers are adjacent after
star contraction. -/
theorem starContraction_complete_of_no_missing_edges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V)
    (g : ↥(starAssignmentFinset A
      (fun w : ↥(A : Set V) => starNeighborChoices G X w.1)))
    (hzero : (starMissingEdges G A X g).card = 0) :
    ∀ x y : ↥(X : Set V), x ≠ y →
      (starContractionGraph G A X
        (starAssignedCenter G A X g)).Adj x y := by
  classical
  intro x y hxy
  by_contra hmiss
  have hempty : starMissingEdges G A X g = ∅ :=
    Finset.card_eq_zero.mp hzero
  have hmem : s(x, y) ∈ starMissingEdges G A X g := by
    simp [starMissingEdges, SimpleGraph.mem_edgeFinset, hxy, hmiss]
  rw [hempty] at hmem
  simp at hmem

/-- If the expected number of missing pairs is below one, a complete
star-contraction outcome exists and the vertex `v` extends it. -/
theorem hasCliqueMinor_of_star_pair_expect_lt_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) (hAX : Disjoint A X)
    (v : V) (hvA : v ∉ A) (hvX : v ∉ X)
    (hneighbor : ∀ x ∈ X, G.Adj v x)
    (s t : ℕ) (hn : 2 ≤ X.card) (ht : t ≤ X.card + 1)
    (hchoices : ∀ w ∈ A, ∃ x ∈ X, G.Adj w x)
    (hcommon : ∀ x y : ↥(X : Set V), x ≠ y →
      s ≤ (starCommonNeighbors G A X x y).card)
    (hsmall : ((X.card.choose 2 : ℕ) : ℝ) *
      Real.exp (-(2 * (s : ℝ) / (X.card : ℝ))) < 1) :
    HasCliqueMinor G t := by
  classical
  obtain ⟨g, hmissing⟩ :=
    exists_star_assignment_with_few_missing_edges
      G A X s hn hchoices hcommon
  have hzero : (starMissingEdges G A X g).card = 0 := by
    have hlt : ((starMissingEdges G A X g).card : ℝ) < 1 :=
      hmissing.trans_lt hsmall
    have hnat : (starMissingEdges G A X g).card < 1 := by
      exact_mod_cast hlt
    omega
  have hcomplete := starContraction_complete_of_no_missing_edges
    G A X g hzero
  have hminor := hasCliqueMinor_succ_of_complete_star_assignment
    G A X hAX g v hvA hvX hneighbor hcomplete
  have hcardX : Fintype.card ↥(X : Set V) = X.card := by
    apply Fintype.card_of_subtype
    intro x
    simp
  rw [hcardX] at hminor
  exact hasCliqueMinor_order_mono ht hminor
end HadwigerLean
