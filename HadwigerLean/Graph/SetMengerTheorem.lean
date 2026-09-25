import Mathlib.Tactic
import HadwigerLean.Graph.SplitPathProjection

namespace HadwigerLean.SetMenger

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem capacityPath_unit_delta_nonneg (G : SimpleGraph V)
    (A B : Finset V) (p : (splitNetwork G A B).CapacityPath)
    (v : V) : 0 ≤ p.2.delta (splitIn v) (splitOut v) := by
  apply p.2.delta_nonneg_of_no_reverse
  simp [splitNetwork, splitCapacity, splitIn, splitOut]

private theorem pathFlux_unit_nonneg (G : SimpleGraph V) (A B : Finset V)
    (ps : List (splitNetwork G A B).CapacityPath) (v : V) :
    0 ≤ (splitNetwork G A B).pathFlux ps (splitIn v) (splitOut v) := by
  induction ps with
  | nil => simp [FiniteFlow.Network.pathFlux]
  | cons p ps ih =>
      simp only [FiniteFlow.Network.pathFlux]
      exact add_nonneg (capacityPath_unit_delta_nonneg G A B p v) ih

private theorem pathFlux_unit_get_le (G : SimpleGraph V) (A B : Finset V)
    (ps : List (splitNetwork G A B).CapacityPath) (v : V)
    (i : Fin ps.length) :
    (ps.get i).2.delta (splitIn v) (splitOut v) ≤
      (splitNetwork G A B).pathFlux ps (splitIn v) (splitOut v) := by
  induction ps with
  | nil => exact Fin.elim0 i
  | cons p ps ih =>
      cases i using Fin.cases with
      | zero =>
          simp only [List.get_cons_zero, FiniteFlow.Network.pathFlux]
          exact le_add_of_nonneg_right (pathFlux_unit_nonneg G A B ps v)
      | succ i =>
          change (ps.get i).2.delta (splitIn v) (splitOut v) ≤
            p.2.delta (splitIn v) (splitOut v) +
              (splitNetwork G A B).pathFlux ps (splitIn v) (splitOut v)
          exact (ih i).trans (le_add_of_nonneg_left
            (capacityPath_unit_delta_nonneg G A B p v))
private theorem pathFlux_unit_two_get_le (G : SimpleGraph V) (A B : Finset V)
    (ps : List (splitNetwork G A B).CapacityPath) (v : V)
    (i j : Fin ps.length) (hij : i ≠ j) :
    (ps.get i).2.delta (splitIn v) (splitOut v) +
      (ps.get j).2.delta (splitIn v) (splitOut v) ≤
      (splitNetwork G A B).pathFlux ps (splitIn v) (splitOut v) := by
  induction ps with
  | nil => exact Fin.elim0 i
  | cons p ps ih =>
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => exact False.elim (hij rfl)
          | succ j =>
              change p.2.delta (splitIn v) (splitOut v) +
                  (ps.get j).2.delta (splitIn v) (splitOut v) ≤
                p.2.delta (splitIn v) (splitOut v) +
                  (splitNetwork G A B).pathFlux ps (splitIn v) (splitOut v)
              exact add_le_add_right (pathFlux_unit_get_le G A B ps v j) _
      | succ i =>
          cases j using Fin.cases with
          | zero =>
              change (ps.get i).2.delta (splitIn v) (splitOut v) +
                  p.2.delta (splitIn v) (splitOut v) ≤
                p.2.delta (splitIn v) (splitOut v) +
                  (splitNetwork G A B).pathFlux ps (splitIn v) (splitOut v)
              have h := pathFlux_unit_get_le G A B ps v i
              calc
                _ ≤ (splitNetwork G A B).pathFlux ps (splitIn v) (splitOut v) +
                      p.2.delta (splitIn v) (splitOut v) := add_le_add_left h _
                _ = _ := add_comm _ _
          | succ j =>
              have hne : i ≠ j := by
                intro h
                exact hij (congrArg Fin.succ h)
              have htail := ih i j hne
              have hhead := capacityPath_unit_delta_nonneg G A B p v
              change (ps.get i).2.delta (splitIn v) (splitOut v) +
                  (ps.get j).2.delta (splitIn v) (splitOut v) ≤
                p.2.delta (splitIn v) (splitOut v) +
                  (splitNetwork G A B).pathFlux ps (splitIn v) (splitOut v)
              exact htail.trans (le_add_of_nonneg_left hhead)

private theorem pathFlux_unit_le_one_of_decomposition (G : SimpleGraph V)
    (A B : Finset V) (f g : FiniteFlow.Flow (splitNetwork G A B))
    (ps : List (splitNetwork G A B).CapacityPath)
    (hdecomp : ∀ x y, f.amount x y = g.amount x y +
      (splitNetwork G A B).pathFlux ps x y) (v : V) :
    (splitNetwork G A B).pathFlux ps (splitIn v) (splitOut v) ≤ 1 := by
  have hf := f.bound (splitIn v) (splitOut v)
  have hg := g.bound (splitOut v) (splitIn v)
  have hga := g.antisymm (splitOut v) (splitIn v)
  have heq := hdecomp (splitIn v) (splitOut v)
  have hcap : splitCapacity G A B (splitIn v) (splitOut v) = 1 := by
    simp [splitCapacity, splitIn, splitOut]
  have hrev : splitCapacity G A B (splitOut v) (splitIn v) = 0 := by
    simp [splitCapacity, splitIn, splitOut]
  change f.amount (splitIn v) (splitOut v) ≤
    (splitCapacity G A B (splitIn v) (splitOut v) : ℤ) at hf
  change g.amount (splitOut v) (splitIn v) ≤
    (splitCapacity G A B (splitOut v) (splitIn v) : ℤ) at hg
  rw [hcap] at hf
  rw [hrev] at hg
  omega

private structure ProjectedCapacityPath (G : SimpleGraph V)
    (A B : Finset V) (p : (splitNetwork G A B).CapacityPath) where
  start : V
  finish : V
  path : G.Path start finish
  start_mem : start ∈ A
  finish_mem : finish ∈ B
  unit_delta : ∀ v ∈ pathVertexSet path,
    p.2.delta (splitIn v) (splitOut v) = 1

private noncomputable def projectCapacityPath (G : SimpleGraph V)
    (A B : Finset V) (p : (splitNetwork G A B).CapacityPath) :
    ProjectedCapacityPath G A B p := by
  classical
  apply Classical.choice
  obtain ⟨a, ha, b, hb, q, hunit⟩ := capacityPath_project G A B p
  exact ⟨⟨a, b, q, ha, hb, hunit⟩⟩

/-- A decomposed integral split-network flow supplies disjoint A--B paths. -/
theorem linkage_of_decomposition (G : SimpleGraph V) (A B : Finset V)
    (f g : FiniteFlow.Flow (splitNetwork G A B))
    (ps : List (splitNetwork G A B).CapacityPath)
    (hdecomp : ∀ x y, f.amount x y = g.amount x y +
      (splitNetwork G A B).pathFlux ps x y) :
    ∃ (P : IndexedPairs (Fin ps.length) V) (L : IndexedLinkage G P),
      IsABLinkage L A B := by
  classical
  let D (i : Fin ps.length) := projectCapacityPath G A B (ps.get i)
  let P : IndexedPairs (Fin ps.length) V :=
    ⟨fun i => (D i).start, fun i => (D i).finish⟩
  let L : IndexedLinkage G P := {
    path := fun i => (D i).path
    disjoint := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro v hvi hvj
      have hi := (D i).unit_delta v hvi
      have hj := (D j).unit_delta v hvj
      have htwo := pathFlux_unit_two_get_le G A B ps v i j hij
      have hbound := pathFlux_unit_le_one_of_decomposition G A B f g ps hdecomp v
      rw [hi, hj] at htwo
      omega
  }
  exact ⟨P, L, ⟨fun i => (D i).start_mem, fun i => (D i).finish_mem⟩⟩

/-- Finite set Menger: a minimum A--B separator and a vertex-disjoint
A--B linkage have the same order. Paths of length zero are included. -/
theorem finite_set_menger (G : SimpleGraph V) (A B : Finset V) :
    ∃ (Q : Finset V) (n : ℕ) (P : IndexedPairs (Fin n) V)
      (L : IndexedLinkage G P),
      IsABSeparator G A B Q ∧ IsABLinkage L A B ∧ Q.card = n ∧
      ∀ T : Finset V, IsABSeparator G A B T → Q.card ≤ T.card := by
  classical
  obtain ⟨f, S, hsource, hsink, hvalue, hsmall, _⟩ :=
    exists_small_split_cut G A B
  let Q := splitSeparator S
  have hQ : IsABSeparator G A B Q :=
    splitSeparator_isABSeparator G A B S hsource hsink hsmall
  have hcard : f.value = (Q.card : ℤ) := by
    calc
      f.value = (splitNetwork G A B).cutCapacity S := hvalue
      _ = (Q.card : ℤ) := small_cut_capacity_eq_separator_card G A B S hsmall
  obtain ⟨ps, g, hlen, hzero, hdecomp⟩ := f.exists_path_decomposition
  obtain ⟨P, L, hAB⟩ := linkage_of_decomposition G A B f g ps hdecomp
  have hlenQ : ps.length = Q.card := by omega
  refine ⟨Q, ps.length, P, L, hQ, hAB, hlenQ.symm, ?_⟩
  intro T hT
  have hle := card_le_separator L A B T hAB hT
  simpa [hlenQ] using hle

/-- If every A--B separator has at least `k` vertices, there are `k`
pairwise vertex-disjoint A--B paths. -/
theorem exists_linkage_of_separator_lower_bound (G : SimpleGraph V)
    (A B : Finset V) (k : ℕ)
    (hsep : ∀ Q : Finset V, IsABSeparator G A B Q → k ≤ Q.card) :
    ∃ (P : IndexedPairs (Fin k) V) (L : IndexedLinkage G P),
      IsABLinkage L A B := by
  obtain ⟨Q, n, P, L, hQ, hAB, hcard, _⟩ := finite_set_menger G A B
  have hk : k ≤ n := by
    rw [← hcard]
    exact hsep Q hQ
  let e := Fin.castLEEmb hk
  refine ⟨P.reindex e, L.reindex e, ?_⟩
  exact ⟨fun i => hAB.1 (e i), fun i => hAB.2 (e i)⟩

/-- The minimum separator in finite set Menger is saturated: each of its
vertices lies on one of the disjoint paths. -/
theorem finite_set_menger_saturated (G : SimpleGraph V) (A B : Finset V) :
    ∃ (Q : Finset V) (n : ℕ) (P : IndexedPairs (Fin n) V)
      (L : IndexedLinkage G P),
      IsABSeparator G A B Q ∧ IsABLinkage L A B ∧ Q.card = n ∧
      (∀ q ∈ Q, ∃ i : Fin n, q ∈ pathVertexSet (L.path i)) := by
  obtain ⟨Q, n, P, L, hQ, hAB, hcard, _⟩ := finite_set_menger G A B
  refine ⟨Q, n, P, L, hQ, hAB, hcard, ?_⟩
  apply separator_saturated L A B Q hAB hQ
  simpa using hcard
end HadwigerLean.SetMenger
