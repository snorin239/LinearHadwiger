import HadwigerLean.Graph.TouchingQuotient
import HadwigerLean.Graph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Weighted eggs

Reed and Seymour, *Fractional Colouring and Hadwiger's Conjecture*,
Section 1, define a yolk of a vertex set to be an independent subset carrying
at least half of its weight. An egg is a nonempty connected induced subgraph
with a yolk. We use real weights because the fractional-coloring dual in this
repository is over `ℝ`; the lemmas that need nonnegative weights state that
hypothesis explicitly.
-/

namespace HadwigerLean

variable {V : Type*} [Fintype V]

/-- The weight of a vertex set, for a real-valued vertex weight. -/
noncomputable def setWeight (w : V → ℝ) (X : Set V) : ℝ := by
  classical
  exact
  ∑ v : V, if v ∈ X then w v else 0

@[simp] theorem setWeight_empty (w : V → ℝ) : setWeight w ∅ = 0 := by
  simp [setWeight]

@[simp] theorem setWeight_univ (w : V → ℝ) :
    setWeight w Set.univ = ∑ v : V, w v := by
  simp [setWeight]

@[simp] theorem setWeight_singleton (w : V → ℝ) (v : V) :
    setWeight w {v} = w v := by
  classical
  simp [setWeight]

theorem setWeight_nonneg (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (X : Set V) :
    0 ≤ setWeight w X := by
  classical
  unfold setWeight
  apply Finset.sum_nonneg
  intro v _
  split_ifs with hv
  · exact hw v
  · exact le_refl _

theorem setWeight_union_of_disjoint (w : V → ℝ) {A B : Set V}
    (hAB : Disjoint A B) :
    setWeight w (A ∪ B) = setWeight w A + setWeight w B := by
  classical
  calc
    setWeight w (A ∪ B) =
        ∑ v : V, ((if v ∈ A then w v else 0) +
          (if v ∈ B then w v else 0)) := by
            unfold setWeight
            apply Finset.sum_congr rfl
            intro v _
            by_cases ha : v ∈ A
            · have hb : v ∉ B := by
                intro hb
                exact (Set.disjoint_left.mp hAB) ha hb
              simp [ha, hb]
            · by_cases hb : v ∈ B <;> simp [ha, hb]
    _ = setWeight w A + setWeight w B := by
      rw [Finset.sum_add_distrib]
      rfl

/-- A stable subset carrying at least half of the total weight of `X`. -/
structure IsYolk (G : SimpleGraph V) (w : V → ℝ) (X Y : Set V) : Prop where
  subset : Y ⊆ X
  stable : G.IsIndepSet Y
  half_weight : setWeight w X ≤ 2 * setWeight w Y

/-- A connected induced subgraph with a half-weight stable subset. -/
structure IsEgg (G : SimpleGraph V) (w : V → ℝ) (X : Set V) : Prop where
  connected : (G.induce X).Connected
  has_yolk : ∃ Y, IsYolk G w X Y

theorem IsEgg.nonempty {G : SimpleGraph V} {w : V → ℝ} {X : Set V}
    (hX : IsEgg G w X) : X.Nonempty := by
  obtain ⟨v⟩ := hX.connected.nonempty
  exact ⟨v.val, v.property⟩

/-- An independent set is its own yolk when vertex weights are nonnegative. -/
theorem yolk_self {G : SimpleGraph V} {w : V → ℝ} {X : Set V}
    (hw : ∀ v, 0 ≤ w v) (hX : G.IsIndepSet X) : IsYolk G w X X := by
  refine ⟨Set.Subset.rfl, hX, ?_⟩
  have hnonneg := setWeight_nonneg w hw X
  linarith

/-- A connected independent induced subgraph is an egg. -/
theorem egg_of_independent {G : SimpleGraph V} {w : V → ℝ} {X : Set V}
    (hw : ∀ v, 0 ≤ w v) (hconn : (G.induce X).Connected)
    (hstable : G.IsIndepSet X) : IsEgg G w X :=
  ⟨hconn, ⟨X, yolk_self hw hstable⟩⟩

/-- One side of an independent bipartition is a yolk. -/
theorem exists_yolk_of_bipartition {G : SimpleGraph V} (w : V → ℝ)
    {X A B : Set V} (hX : X = A ∪ B) (hdisj : Disjoint A B)
    (hA : G.IsIndepSet A) (hB : G.IsIndepSet B) :
    ∃ Y, IsYolk G w X Y := by
  have hweight : setWeight w X = setWeight w A + setWeight w B := by
    rw [hX, setWeight_union_of_disjoint w hdisj]
  rcases le_total (setWeight w B) (setWeight w A) with hBA | hAB
  · refine ⟨A, ⟨?_, hA, ?_⟩⟩
    · rw [hX]
      exact Set.subset_union_left
    · rw [hweight]
      linarith
  · refine ⟨B, ⟨?_, hB, ?_⟩⟩
    · rw [hX]
      exact Set.subset_union_right
    · rw [hweight]
      linarith

/-- A connected bipartite piece is an egg for every real vertex weight. -/
theorem egg_of_bipartition {G : SimpleGraph V} (w : V → ℝ)
    {X A B : Set V} (hconn : (G.induce X).Connected)
    (hX : X = A ∪ B) (hdisj : Disjoint A B)
    (hA : G.IsIndepSet A) (hB : G.IsIndepSet B) : IsEgg G w X :=
  ⟨hconn, exists_yolk_of_bipartition w hX hdisj hA hB⟩

/-- A two-colorable induced subgraph has a half-weight stable subset. -/
theorem exists_yolk_of_colorable_two {G : SimpleGraph V} (w : V → ℝ)
    {X : Set V} (hcolor : (G.induce X).Colorable 2) :
    ∃ Y, IsYolk G w X Y := by
  classical
  obtain ⟨c⟩ := hcolor
  let A : Set V := {v | ∃ hv : v ∈ X, c ⟨v, hv⟩ = 0}
  let B : Set V := {v | ∃ hv : v ∈ X, c ⟨v, hv⟩ = 1}
  have hX : X = A ∪ B := by
    ext v
    constructor
    · intro hv
      by_cases hzero : c ⟨v, hv⟩ = 0
      · exact Or.inl ⟨hv, hzero⟩
      · exact Or.inr ⟨hv, Fin.eq_one_of_ne_zero _ hzero⟩
    · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
  have hdisj : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro v hvA hvB
    obtain ⟨hvX, hzero⟩ := hvA
    obtain ⟨_, hone⟩ := hvB
    have hbad : (0 : Fin 2) = 1 := hzero.symm.trans hone
    simp at hbad
  have hA : G.IsIndepSet A := by
    intro u hu v hv huv hadj
    obtain ⟨huX, hu0⟩ := hu
    obtain ⟨hvX, hv0⟩ := hv
    exact (c.valid (show (G.induce X).Adj ⟨u, huX⟩ ⟨v, hvX⟩ from hadj))
      (hu0.trans hv0.symm)
  have hB : G.IsIndepSet B := by
    intro u hu v hv huv hadj
    obtain ⟨huX, hu1⟩ := hu
    obtain ⟨hvX, hv1⟩ := hv
    exact (c.valid (show (G.induce X).Adj ⟨u, huX⟩ ⟨v, hvX⟩ from hadj))
      (hu1.trans hv1.symm)
  exact exists_yolk_of_bipartition w hX hdisj hA hB

/-- A connected two-colorable induced subgraph is an egg. -/
theorem egg_of_colorable_two {G : SimpleGraph V} (w : V → ℝ)
    {X : Set V} (hconn : (G.induce X).Connected)
    (hcolor : (G.induce X).Colorable 2) : IsEgg G w X :=
  ⟨hconn, exists_yolk_of_colorable_two w hcolor⟩
/-- A singleton piece is an egg for nonnegative weights. -/
theorem egg_singleton {G : SimpleGraph V} {w : V → ℝ}
    (hw : ∀ u, 0 ≤ w u) (v : V) : IsEgg G w {v} := by
  have hconn : (G.induce ({v} : Set V)).Connected := by
    letI : Subsingleton {u : V // u ∈ ({v} : Set V)} := ⟨by
      intro a b
      apply Subtype.ext
      have ha : a.val = v := Set.mem_singleton_iff.mp a.property
      have hb : b.val = v := Set.mem_singleton_iff.mp b.property
      exact ha.trans hb.symm⟩
    letI : Nonempty {u : V // u ∈ ({v} : Set V)} := ⟨⟨v, rfl⟩⟩
    exact SimpleGraph.Connected.of_subsingleton
  have hstable : G.IsIndepSet ({v} : Set V) := by
    simp [SimpleGraph.isIndepSet_iff]
  exact egg_of_independent hw hconn hstable
/-- Yolks combine across disjoint pieces when there are no edges between them. -/
theorem IsYolk.union_of_no_cross {G : SimpleGraph V} {w : V → ℝ}
    {X Q Y Z : Set V} (hY : IsYolk G w X Y)
    (hZ : IsYolk G w Q Z) (hXQ : Disjoint X Q)
    (hcross : ∀ u ∈ Y, ∀ v ∈ Z, ¬ G.Adj u v) :
    IsYolk G w (X ∪ Q) (Y ∪ Z) := by
  have hYZ : Disjoint Y Z := Set.disjoint_left.mpr (by
    intro v hvY hvZ
    exact (Set.disjoint_left.mp hXQ) (hY.subset hvY) (hZ.subset hvZ))
  refine ⟨Set.union_subset_union hY.subset hZ.subset, ?_, ?_⟩
  · intro u hu v hv huv hadj
    rcases hu with huY | huZ <;> rcases hv with hvY | hvZ
    · exact hY.stable huY hvY huv hadj
    · exact hcross u huY v hvZ hadj
    · exact hcross v hvY u huZ hadj.symm
    · exact hZ.stable huZ hvZ huv hadj
  · rw [setWeight_union_of_disjoint w hXQ,
      setWeight_union_of_disjoint w hYZ]
    linarith [hY.half_weight, hZ.half_weight]
end HadwigerLean
