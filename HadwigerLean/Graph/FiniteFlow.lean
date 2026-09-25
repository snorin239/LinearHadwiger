import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite capacitated networks

An antisymmetric integer flow is bounded above by the capacity of each
directed arc.  This representation automatically includes reverse residual
arcs.  The cut lemmas below are the algebraic core of the finite max-flow
argument used for vertex-disjoint paths.
-/

namespace HadwigerLean
namespace FiniteFlow

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A finite directed network. The source has no incoming capacity and the
sink has no outgoing capacity. Parallel arcs can be combined by adding their
capacities. -/
structure Network (V : Type*) where
  source : V
  sink : V
  capacity : V → V → ℕ
  source_ne_sink : source ≠ sink
  no_into_source : ∀ v, capacity v source = 0
  no_out_of_sink : ∀ v, capacity sink v = 0

/-- An integer flow, represented by its antisymmetric net amount on each
ordered vertex pair. -/
structure Flow (N : Network V) where
  amount : V → V → ℤ
  antisymm : ∀ u v, amount u v = -amount v u
  bound : ∀ u v, amount u v ≤ (N.capacity u v : ℤ)
  balanced : ∀ u, u ≠ N.source → u ≠ N.sink → ∑ v, amount u v = 0

variable {N : Network V}

/-- Net flow sent by the source. -/
def Flow.value (f : Flow N) : ℤ := ∑ v, f.amount N.source v

/-- The capacity of the directed cut from `S` to its complement. -/
def Network.cutCapacity (N : Network V) (S : Finset V) : ℤ :=
  ∑ u ∈ S, ∑ v ∈ Finset.univ \ S, (N.capacity u v : ℤ)

/-- The net flow crossing the directed cut from `S` to its complement. -/
def Flow.cutFlux (f : Flow N) (S : Finset V) : ℤ :=
  ∑ u ∈ S, ∑ v ∈ Finset.univ \ S, f.amount u v

theorem Flow.source_out_nonneg (f : Flow N) (v : V) :
    0 ≤ f.amount N.source v := by
  have h := f.bound v N.source
  rw [N.no_into_source] at h
  rw [f.antisymm v N.source] at h
  exact neg_nonpos.mp h

theorem Flow.value_nonneg (f : Flow N) : 0 ≤ f.value := by
  unfold Flow.value
  exact Finset.sum_nonneg (fun v _ => f.source_out_nonneg v)

theorem Flow.value_le_source_capacity (f : Flow N) :
    f.value ≤ ∑ v, (N.capacity N.source v : ℤ) := by
  unfold Flow.value
  exact Finset.sum_le_sum (fun v _ => f.bound N.source v)

theorem Flow.cutFlux_le_cutCapacity (f : Flow N) (S : Finset V) :
    f.cutFlux S ≤ N.cutCapacity S := by
  unfold Flow.cutFlux Network.cutCapacity
  apply Finset.sum_le_sum
  intro u hu
  exact Finset.sum_le_sum (fun v hv => f.bound u v)

/-- A saturated cut certifies a flow's value once flow conservation has been
used to identify source value with cut flux. -/
theorem Flow.cutFlux_eq_cutCapacity_of_saturated (f : Flow N) (S : Finset V)
    (hsat : ∀ u ∈ S, ∀ v ∈ Finset.univ \ S,
      f.amount u v = (N.capacity u v : ℤ)) :
    f.cutFlux S = N.cutCapacity S := by
  unfold Flow.cutFlux Network.cutCapacity
  apply Finset.sum_congr rfl
  intro u hu
  exact Finset.sum_congr rfl (fun v hv => hsat u hu v hv)

private theorem Flow.internalFlux_eq_zero (f : Flow N) (S : Finset V) :
    (∑ u ∈ S, ∑ v ∈ S, f.amount u v) = 0 := by
  have hswap : (∑ u ∈ S, ∑ v ∈ S, f.amount u v) =
      (∑ u ∈ S, ∑ v ∈ S, f.amount v u) := by
    rw [Finset.sum_comm]
  have hneg : (∑ u ∈ S, ∑ v ∈ S, f.amount v u) =
      -(∑ u ∈ S, ∑ v ∈ S, f.amount u v) := by
    calc
      (∑ u ∈ S, ∑ v ∈ S, f.amount v u) =
          (∑ u ∈ S, ∑ v ∈ S, -f.amount u v) := by
            apply Finset.sum_congr rfl
            intro u hu
            apply Finset.sum_congr rfl
            intro v hv
            exact f.antisymm v u
      _ = -(∑ u ∈ S, ∑ v ∈ S, f.amount u v) := by
            simp only [Finset.sum_neg_distrib]
  omega
/-- Flow conservation identifies the value of a flow with its net flux
across every source--sink cut. -/
theorem Flow.value_eq_cutFlux (f : Flow N) (S : Finset V)
    (hsource : N.source ∈ S) (hsink : N.sink ∉ S) :
    f.value = f.cutFlux S := by
  have hconservation : (∑ u ∈ S, ∑ v, f.amount u v) = f.value := by
    calc
      (∑ u ∈ S, ∑ v, f.amount u v) =
          ∑ u ∈ S, if u = N.source then f.value else 0 := by
            apply Finset.sum_congr rfl
            intro u hu
            by_cases hs : u = N.source
            · subst u
              simp only [↓reduceIte]
              rfl
            · simp only [hs, ↓reduceIte]
              exact f.balanced u hs (fun ht => hsink (ht ▸ hu))
      _ = f.value := by simp [hsource]
  have hpartition (u : V) :
      (∑ v, f.amount u v) =
      (∑ v ∈ S, f.amount u v) +
        (∑ v ∈ Finset.univ \ S, f.amount u v) := by
    have hd : Disjoint S (Finset.univ \ S) := Finset.disjoint_sdiff
    have hu : S ∪ (Finset.univ \ S) = Finset.univ :=
      Finset.union_sdiff_of_subset (Finset.subset_univ S)
    calc
      (∑ v, f.amount u v) =
          (∑ v ∈ S ∪ (Finset.univ \ S), f.amount u v) := by rw [hu]
      _ = (∑ v ∈ S, f.amount u v) +
          (∑ v ∈ Finset.univ \ S, f.amount u v) := Finset.sum_union hd
  calc
    f.value = ∑ u ∈ S, ∑ v, f.amount u v := hconservation.symm
    _ = (∑ u ∈ S, ∑ v ∈ S, f.amount u v) +
          (∑ u ∈ S, ∑ v ∈ Finset.univ \ S, f.amount u v) := by
          simp_rw [hpartition]
          rw [Finset.sum_add_distrib]
    _ = f.cutFlux S := by rw [f.internalFlux_eq_zero]; simp [Flow.cutFlux]

/-- Every flow is bounded by the capacity of every source--sink cut. -/
theorem Flow.value_le_cutCapacity (f : Flow N) (S : Finset V)
    (hsource : N.source ∈ S) (hsink : N.sink ∉ S) :
    f.value ≤ N.cutCapacity S := by
  rw [f.value_eq_cutFlux S hsource hsink]
  exact f.cutFlux_le_cutCapacity S

/-- A saturated cut certifies that a flow has maximum value. -/
theorem Flow.maximal_of_saturated_cut (f : Flow N) (S : Finset V)
    (hsource : N.source ∈ S) (hsink : N.sink ∉ S)
    (hsat : ∀ u ∈ S, ∀ v ∈ Finset.univ \ S,
      f.amount u v = (N.capacity u v : ℤ)) (g : Flow N) :
    g.value ≤ f.value := by
  calc
    g.value ≤ N.cutCapacity S := g.value_le_cutCapacity S hsource hsink
    _ = f.cutFlux S := (f.cutFlux_eq_cutCapacity_of_saturated S hsat).symm
    _ = f.value := (f.value_eq_cutFlux S hsource hsink).symm
/-- An arc has residual capacity if its net flow can be increased by one. -/
def Flow.ResidualArc (f : Flow N) (u v : V) : Prop :=
  f.amount u v < (N.capacity u v : ℤ)

/-- Directed reachability from the source through residual arcs. -/
def Flow.ResidualReachable (f : Flow N) (v : V) : Prop :=
  Relation.ReflTransGen f.ResidualArc N.source v

/-- The set of vertices reachable from the source in the residual network. -/
noncomputable def Flow.reachableCut (f : Flow N) : Finset V := by
  classical
  exact Finset.univ.filter f.ResidualReachable

theorem Flow.source_mem_reachableCut (f : Flow N) :
    N.source ∈ f.reachableCut := by
  classical
  simp only [Flow.reachableCut, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Relation.ReflTransGen.refl

theorem Flow.reachableCut_closed (f : Flow N) {u v : V}
    (hu : u ∈ f.reachableCut) (hres : f.ResidualArc u v) :
    v ∈ f.reachableCut := by
  classical
  simp only [Flow.reachableCut, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  exact Relation.ReflTransGen.tail hu hres

theorem Flow.reachableCut_saturated (f : Flow N) :
    ∀ u ∈ f.reachableCut, ∀ v ∈ Finset.univ \ f.reachableCut,
      f.amount u v = (N.capacity u v : ℤ) := by
  intro u hu v hv
  have hvnot : v ∉ f.reachableCut := (Finset.mem_sdiff.mp hv).2
  have hnot : ¬ f.ResidualArc u v := by
    intro hres
    exact hvnot (f.reachableCut_closed hu hres)
  exact le_antisymm (f.bound u v) (le_of_not_gt hnot)

/-- If no residual source--sink path exists, the reachable cut witnesses the
max-flow/min-cut equality for this particular flow. -/
theorem Flow.value_eq_reachableCut_capacity (f : Flow N)
    (hsink : N.sink ∉ f.reachableCut) :
    f.value = N.cutCapacity f.reachableCut := by
  rw [f.value_eq_cutFlux f.reachableCut f.source_mem_reachableCut hsink]
  exact f.cutFlux_eq_cutCapacity_of_saturated f.reachableCut
    f.reachableCut_saturated
/-- The zero flow is feasible on every network. -/
def Flow.zero (N : Network V) : Flow N where
  amount := fun _ _ => 0
  antisymm := by intro u v; simp
  bound := by intro u v; exact Int.natCast_nonneg _
  balanced := by intro u hu ht; simp

@[simp] theorem Flow.value_zero : (Flow.zero N).value = 0 := by
  simp [Flow.value, Flow.zero]

/-- The natural source-capacity bound on every flow value. -/
theorem Flow.value_toNat_le_source_capacity (f : Flow N) :
    f.value.toNat ≤ ∑ v, N.capacity N.source v := by
  have h := f.value_le_source_capacity
  have hn := f.value_nonneg
  have hc : (∑ v, (N.capacity N.source v : ℤ)) =
      ((∑ v, N.capacity N.source v : ℕ) : ℤ) := by
    simp
  rw [hc] at h
  omega

/-- A finite integer network has a flow with maximum value. This uses only
bounded integer values, so it does not need compactness or linear programming. -/
theorem Network.exists_maximum_flow (N : Network V) :
    ∃ f : Flow N, ∀ g : Flow N, g.value ≤ f.value := by
  classical
  let B : ℕ := ∑ v, N.capacity N.source v
  let P : ℕ → Prop := fun n => ∃ f : Flow N, f.value = (n : ℤ)
  have hzero : P 0 := ⟨Flow.zero N, by simp⟩
  have hspec : P (Nat.findGreatest P B) :=
    Nat.findGreatest_spec (Nat.zero_le B) hzero
  obtain ⟨f, hf⟩ := hspec
  refine ⟨f, ?_⟩
  intro g
  have hgB : g.value.toNat ≤ B := g.value_toNat_le_source_capacity
  have hgP : P g.value.toNat := by
    refine ⟨g, ?_⟩
    exact (Int.toNat_of_nonneg g.value_nonneg).symm
  have hmax : g.value.toNat ≤ Nat.findGreatest P B :=
    Nat.le_findGreatest hgB hgP
  have hgnonneg := g.value_nonneg
  omega
/-- A finite directed path built by appending a fresh vertex at every step.
The list contains both endpoints. -/
inductive DirectedSimplePath (r : V → V → Prop) (s : V) :
    V → List V → Type u where
  | nil : DirectedSimplePath r s s [s]
  | snoc {u v : V} {l : List V} :
      DirectedSimplePath r s u l → r u v → v ∉ l →
      DirectedSimplePath r s v (l ++ [v])

namespace DirectedSimplePath

variable {r : V → V → Prop} {s t : V} {l : List V}

/-- Every vertex already on a simple directed path is itself reachable by
the prefix ending at that vertex. -/
theorem prefix_of_mem (p : DirectedSimplePath r s t l) :
    ∀ v ∈ l, ∃ l', Nonempty (DirectedSimplePath r s v l') := by
  induction p with
  | nil =>
      intro v hv
      have hv' : v = s := by simpa using hv
      subst v
      exact ⟨[s], ⟨.nil⟩⟩
  | @snoc u v l p hres hfresh ih =>
      intro w hw
      rcases List.mem_append.mp hw with h_old | h_new
      · exact ih w h_old
      · have hwv : w = v := by simpa using h_new
        subst w
        exact ⟨l ++ [v], ⟨.snoc p hres hfresh⟩⟩

/-- A reflexive transitive directed connection can always be shortened to
a path with no repeated vertices. -/
theorem exists_of_reflTransGen {t : V}
    (h : Relation.ReflTransGen r s t) :
    ∃ l, Nonempty (DirectedSimplePath r s t l) := by
  induction h with
  | refl =>
      exact ⟨[s], ⟨.nil⟩⟩
  | @tail u v h hres ih =>
      obtain ⟨l, ⟨p⟩⟩ := ih
      by_cases hv : v ∈ l
      · exact p.prefix_of_mem v hv
      · exact ⟨l ++ [v], ⟨.snoc p hres hv⟩⟩

end DirectedSimplePath
namespace DirectedSimplePath

variable {r : V → V → Prop} {s t : V} {l : List V}

theorem end_mem (p : DirectedSimplePath r s t l) : t ∈ l := by
  induction p with
  | nil => simp
  | snoc p hres hfresh ih => simp

/-- Signed incidence of a directed simple path on ordered vertex pairs. -/
def delta {r : V → V → Prop} {s : V} :
    {t : V} → {l : List V} → DirectedSimplePath r s t l → V → V → ℤ
  | _, _, .nil => fun _ _ => 0
  | _, _, .snoc (u := u) (v := v) p _ _ =>
      fun x y => p.delta x y +
        (if x = u ∧ y = v then 1 else 0) -
        (if x = v ∧ y = u then 1 else 0)

theorem delta_left_zero (p : DirectedSimplePath r s t l)
    {x y : V} (hx : x ∉ l) : p.delta x y = 0 := by
  induction p with
  | nil => simp [delta]
  | @snoc u v l p hres hfresh ih =>
      have hxOld : x ∉ l := by
        intro h
        exact hx (List.mem_append.mpr (Or.inl h))
      have hxV : x ≠ v := by
        intro h
        exact hx (by simp [h])
      have hxU : x ≠ u := by
        intro h
        exact hxOld (h ▸ p.end_mem)
      simp [delta, ih hxOld, hxV, hxU]

theorem delta_right_zero (p : DirectedSimplePath r s t l)
    {x y : V} (hy : y ∉ l) : p.delta x y = 0 := by
  induction p with
  | nil => simp [delta]
  | @snoc u v l p hres hfresh ih =>
      have hyOld : y ∉ l := by
        intro h
        exact hy (List.mem_append.mpr (Or.inl h))
      have hyV : y ≠ v := by
        intro h
        exact hy (by simp [h])
      have hyU : y ≠ u := by
        intro h
        exact hyOld (h ▸ p.end_mem)
      simp [delta, ih hyOld, hyV, hyU]

theorem delta_antisymm (p : DirectedSimplePath r s t l) (x y : V) :
    p.delta x y = -p.delta y x := by
  induction p generalizing x y with
  | nil => simp [delta]
  | @snoc u v l p hres hfresh ih =>
      simp only [delta]
      have h := ih x y
      have hA :
          (if y = v ∧ x = u then (1 : ℤ) else 0) =
          (if x = u ∧ y = v then 1 else 0) := by
        by_cases hxu : x = u
        · by_cases hyv : y = v <;> simp [hxu, hyv]
        · simp [hxu]
      have hB :
          (if y = u ∧ x = v then (1 : ℤ) else 0) =
          (if x = v ∧ y = u then 1 else 0) := by
        by_cases hxv : x = v
        · by_cases hyu : y = u <;> simp [hxv, hyu]
        · simp [hxv]
      rw [hA, hB]
      omega

/-- Path incidence is nonnegative on an arc whose reverse is unavailable. -/
theorem delta_nonneg_of_no_reverse (p : DirectedSimplePath r s t l)
    {x y : V} (hrev : ¬ r y x) : 0 ≤ p.delta x y := by
  induction p with
  | nil => simp [delta]
  | @snoc u v l p huv hfresh ih =>
      have hback : ¬ (x = v ∧ y = u) := by
        intro h
        exact hrev (by simpa [h.1, h.2] using huv)
      simp only [delta, if_neg hback, sub_zero]
      split_ifs <;> omega
/-- The signed path incidence has one unit of divergence at its start
and minus one at its current endpoint. -/
theorem delta_divergence (p : DirectedSimplePath r s t l) (x : V) :
    (∑ y, p.delta x y) =
      (if x = s then (1 : ℤ) else 0) -
      (if x = t then (1 : ℤ) else 0) := by
  induction p generalizing x with
  | nil => simp [delta]
  | @snoc u v l p hres hfresh ih =>
      have hforward :
          (∑ y, (if x = u ∧ y = v then (1 : ℤ) else 0)) =
            (if x = u then 1 else 0) := by
        by_cases hx : x = u <;> simp [hx]
      have hbackward :
          (∑ y, (if x = v ∧ y = u then (1 : ℤ) else 0)) =
            (if x = v then 1 else 0) := by
        by_cases hx : x = v <;> simp [hx]
      simp only [delta, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [hforward, hbackward, ih x]
      omega
end DirectedSimplePath
/-- Increasing flow by the signed incidence of a simple residual path respects
every arc capacity. -/
theorem Flow.augmented_bound (f : Flow N)
    {t : V} {l : List V}
    (p : DirectedSimplePath f.ResidualArc N.source t l) :
    ∀ x y, f.amount x y + p.delta x y ≤ (N.capacity x y : ℤ) := by
  induction p with
  | nil =>
      intro x y
      simpa [DirectedSimplePath.delta] using f.bound x y
  | @snoc u v l p hres hfresh ih =>
      intro x y
      have huv : u ≠ v := by
        intro h
        exact hfresh (h ▸ p.end_mem)
      by_cases hforward : x = u ∧ y = v
      · obtain ⟨hxu, hyv⟩ := hforward
        subst x
        subst y
        have hbackward : ¬ (u = v ∧ v = u) := by
          intro h
          exact huv h.1
        simp only [DirectedSimplePath.delta, hbackward, ↓reduceIte]
        rw [p.delta_right_zero hfresh]
        dsimp [Flow.ResidualArc] at hres
        omega
      · by_cases hbackward : x = v ∧ y = u
        · obtain ⟨hxv, hyu⟩ := hbackward
          subst x
          subst y
          have hforward' : ¬ (v = u ∧ u = v) := by
            intro h
            exact huv h.2
          simp only [DirectedSimplePath.delta, hforward', ↓reduceIte]
          rw [p.delta_left_zero hfresh]
          have hb := f.bound v u
          omega
        · simpa only [DirectedSimplePath.delta, hforward, hbackward,
            ↓reduceIte, add_zero, sub_zero] using ih x y
/-- Augment one unit along a simple residual source--sink path. -/
def Flow.augment (f : Flow N) {l : List V}
    (p : DirectedSimplePath f.ResidualArc N.source N.sink l) : Flow N where
  amount := fun x y => f.amount x y + p.delta x y
  antisymm := by
    intro x y
    rw [f.antisymm x y, p.delta_antisymm x y]
    omega
  bound := f.augmented_bound p
  balanced := by
    intro x hxsource hxsink
    simp only [Finset.sum_add_distrib]
    rw [f.balanced x hxsource hxsink, p.delta_divergence x]
    simp [hxsource, hxsink]

theorem Flow.augment_value (f : Flow N) {l : List V}
    (p : DirectedSimplePath f.ResidualArc N.source N.sink l) :
    (f.augment p).value = f.value + 1 := by
  simp only [Flow.value, Flow.augment, Finset.sum_add_distrib]
  rw [p.delta_divergence N.source]
  simp [N.source_ne_sink]

/-- The residual sink of a maximum integer flow is unreachable. -/
theorem Flow.sink_not_reachable_of_maximal (f : Flow N)
    (hmax : ∀ g : Flow N, g.value ≤ f.value) :
    N.sink ∉ f.reachableCut := by
  intro hsink
  have hreach : f.ResidualReachable N.sink := by
    simpa [Flow.reachableCut] using hsink
  obtain ⟨l, ⟨p⟩⟩ :=
    DirectedSimplePath.exists_of_reflTransGen hreach
  have h := hmax (f.augment p)
  rw [f.augment_value p] at h
  omega

/-- Finite integral max flow equals minimum cut. Both a maximum flow and
a minimum cut are returned, with equality of their integer values. -/
theorem Network.exists_max_flow_min_cut (N : Network V) :
    ∃ (f : Flow N) (S : Finset V),
      N.source ∈ S ∧ N.sink ∉ S ∧
      f.value = N.cutCapacity S ∧
      (∀ g : Flow N, g.value ≤ f.value) ∧
      (∀ T : Finset V, N.source ∈ T → N.sink ∉ T →
        N.cutCapacity S ≤ N.cutCapacity T) := by
  obtain ⟨f, hmax⟩ := N.exists_maximum_flow
  let S := f.reachableCut
  have hsink : N.sink ∉ S := f.sink_not_reachable_of_maximal hmax
  refine ⟨f, S, f.source_mem_reachableCut, hsink,
    f.value_eq_reachableCut_capacity hsink, hmax, ?_⟩
  intro T hsource hsnk
  rw [← f.value_eq_reachableCut_capacity hsink]
  exact f.value_le_cutCapacity T hsource hsnk
/-- A positive-flow arc is oriented in the direction of the net flow. -/
def Flow.PositiveArc (f : Flow N) (u v : V) : Prop :=
  0 < f.amount u v

/-- Positive value forces a source--sink path of positive-flow arcs. -/
theorem Flow.exists_positive_path_of_value_pos (f : Flow N)
    (hpos : 0 < f.value) :
    ∃ l, Nonempty
      (DirectedSimplePath f.PositiveArc N.source N.sink l) := by
  classical
  let R : Finset V :=
    Finset.univ.filter
      (fun v => Relation.ReflTransGen f.PositiveArc N.source v)
  have hsource : N.source ∈ R := by
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.refl
  have hsink : N.sink ∈ R := by
    by_contra hsnk
    have hflux : f.cutFlux R ≤ 0 := by
      unfold Flow.cutFlux
      apply Finset.sum_nonpos
      intro u hu
      apply Finset.sum_nonpos
      intro v hv
      have hu' : Relation.ReflTransGen f.PositiveArc N.source u := by
        simpa [R] using hu
      have hvnot : v ∉ R := (Finset.mem_sdiff.mp hv).2
      have hnot : ¬ f.PositiveArc u v := by
        intro huv
        apply hvnot
        simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Relation.ReflTransGen.tail hu' huv
      exact le_of_not_gt hnot
    have hval := f.value_eq_cutFlux R hsource hsnk
    omega
  have hreach : Relation.ReflTransGen f.PositiveArc N.source N.sink := by
    simpa [R] using hsink
  exact DirectedSimplePath.exists_of_reflTransGen hreach
/-- Subtracting a simple positive-flow path preserves all capacities. -/
theorem Flow.reduced_bound (f : Flow N)
    {t : V} {l : List V}
    (p : DirectedSimplePath f.PositiveArc N.source t l) :
    ∀ x y, f.amount x y - p.delta x y ≤ (N.capacity x y : ℤ) := by
  induction p with
  | nil =>
      intro x y
      simpa [DirectedSimplePath.delta] using f.bound x y
  | @snoc u v l p hpos hfresh ih =>
      intro x y
      have huv : u ≠ v := by
        intro h
        exact hfresh (h ▸ p.end_mem)
      by_cases hforward : x = u ∧ y = v
      · obtain ⟨hxu, hyv⟩ := hforward
        subst x
        subst y
        have hbackward : ¬ (u = v ∧ v = u) := by
          intro h
          exact huv h.1
        simp only [DirectedSimplePath.delta, hbackward, ↓reduceIte]
        rw [p.delta_right_zero hfresh]
        have hb := f.bound u v
        omega
      · by_cases hbackward : x = v ∧ y = u
        · obtain ⟨hxv, hyu⟩ := hbackward
          subst x
          subst y
          have hforward' : ¬ (v = u ∧ u = v) := by
            intro h
            exact huv h.2
          simp only [DirectedSimplePath.delta, hforward', ↓reduceIte]
          rw [p.delta_left_zero hfresh]
          have ha := f.antisymm u v
          have hc : 0 ≤ (N.capacity v u : ℤ) := Int.natCast_nonneg _
          dsimp [Flow.PositiveArc] at hpos
          omega
        · simpa only [DirectedSimplePath.delta, hforward, hbackward,
            ↓reduceIte, add_zero, sub_zero] using ih x y

/-- Remove one unit of flow along a positive source--sink path. -/
def Flow.reduce (f : Flow N) {l : List V}
    (p : DirectedSimplePath f.PositiveArc N.source N.sink l) : Flow N where
  amount := fun x y => f.amount x y - p.delta x y
  antisymm := by
    intro x y
    rw [f.antisymm x y, p.delta_antisymm x y]
    omega
  bound := f.reduced_bound p
  balanced := by
    intro x hxsource hxsink
    simp only [Finset.sum_sub_distrib]
    rw [f.balanced x hxsource hxsink, p.delta_divergence x]
    simp [hxsource, hxsink]

theorem Flow.reduce_value (f : Flow N) {l : List V}
    (p : DirectedSimplePath f.PositiveArc N.source N.sink l) :
    (f.reduce p).value = f.value - 1 := by
  simp only [Flow.value, Flow.reduce, Finset.sum_sub_distrib]
  rw [p.delta_divergence N.source]
  simp [N.source_ne_sink]
namespace DirectedSimplePath

variable {r q : V → V → Prop} {s t : V} {l : List V}

/-- Transport a simple directed path along inclusion of arc relations. -/
def map {r q : V → V → Prop} {s : V} :
    {t : V} → {l : List V} → DirectedSimplePath r s t l →
    (∀ u v, r u v → q u v) → DirectedSimplePath q s t l
  | _, _, .nil, _ => .nil
  | _, _, .snoc (u := u) (v := v) p huv hfresh, h =>
      .snoc (p.map h) (h u v huv) hfresh

theorem delta_map (p : DirectedSimplePath r s t l)
    (h : ∀ u v, r u v → q u v) (x y : V) :
    (p.map h).delta x y = p.delta x y := by
  induction p with
  | nil => simp [map, delta]
  | @snoc u v l p huv hfresh ih =>
      simp only [map, delta, ih]

end DirectedSimplePath

/-- Every positive-flow arc has positive network capacity. -/
theorem Flow.positiveArc_capacity_pos (f : Flow N) {u v : V}
    (h : f.PositiveArc u v) : 0 < N.capacity u v := by
  have hb := f.bound u v
  dsimp [Flow.PositiveArc] at h
  omega
/-- A source--sink path using only arcs of positive capacity. -/
abbrev Network.CapacityPath (N : Network V) :=
  Σ l : List V,
    DirectedSimplePath (fun u v => 0 < N.capacity u v)
      N.source N.sink l

/-- Signed sum of the path incidences in a finite list. -/
def Network.pathFlux (N : Network V) :
    List N.CapacityPath → V → V → ℤ
  | [], _, _ => 0
  | p :: ps, x, y => p.2.delta x y + N.pathFlux ps x y

/-- Every integer flow is a sum of source--sink path incidences and a
zero-value residual flow. The path list has length equal to the flow value. -/
theorem Flow.exists_path_decomposition (f : Flow N) :
    ∃ (ps : List N.CapacityPath) (g : Flow N),
      ps.length = f.value.toNat ∧ g.value = 0 ∧
      ∀ x y, f.amount x y = g.amount x y + N.pathFlux ps x y := by
  let P : ℕ → Prop := fun n =>
    ∀ f : Flow N, f.value.toNat = n →
      ∃ (ps : List N.CapacityPath) (g : Flow N),
        ps.length = f.value.toNat ∧ g.value = 0 ∧
        ∀ x y, f.amount x y = g.amount x y + N.pathFlux ps x y
  have hall : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hfval
      by_cases hzero : n = 0
      · have hfv : f.value = 0 := by
          have hn := f.value_nonneg
          omega
        refine ⟨[], f, ?_, hfv, ?_⟩
        · simp [hfv]
        · intro x y
          simp [Network.pathFlux]
      · have hpos : 0 < f.value := by
          have hn := f.value_nonneg
          omega
        obtain ⟨l, ⟨p⟩⟩ := f.exists_positive_path_of_value_pos hpos
        let g := f.reduce p
        have hgv : g.value = f.value - 1 := f.reduce_value p
        have hgsmall : g.value.toNat < n := by
          have hgn := g.value_nonneg
          omega
        obtain ⟨ps, residual, hlen, hresval, hamount⟩ :=
          ih g.value.toNat hgsmall g rfl
        let hcap : ∀ u v, f.PositiveArc u v →
            0 < N.capacity u v :=
          fun u v huv => f.positiveArc_capacity_pos huv
        let q : N.CapacityPath := ⟨l, p.map hcap⟩
        refine ⟨q :: ps, residual, ?_, hresval, ?_⟩
        · simp only [List.length_cons, hlen]
          omega
        · intro x y
          have hmap : q.2.delta x y = p.delta x y :=
            p.delta_map hcap x y
          have hred : g.amount x y = f.amount x y - p.delta x y := rfl
          have hd := hamount x y
          change f.amount x y =
            residual.amount x y + (q.2.delta x y + N.pathFlux ps x y)
          omega
  exact hall f.value.toNat f rfl
/-- Every crossing arc's capacity is at most the total cut capacity. -/
theorem Network.arcCapacity_le_cutCapacity (N : Network V)
    (S : Finset V) {x y : V} (hx : x ∈ S) (hy : y ∉ S) :
    (N.capacity x y : ℤ) ≤ N.cutCapacity S := by
  have hy' : y ∈ Finset.univ \ S :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hy⟩
  have hinner :
      (N.capacity x y : ℤ) ≤
        ∑ v ∈ Finset.univ \ S, (N.capacity x v : ℤ) :=
    Finset.single_le_sum
      (fun v hv => Int.natCast_nonneg _) hy'
  have houter :
      (∑ v ∈ Finset.univ \ S, (N.capacity x v : ℤ)) ≤
        N.cutCapacity S := by
    unfold Network.cutCapacity
    exact Finset.single_le_sum
      (fun u hu => Finset.sum_nonneg (fun v hv => Int.natCast_nonneg _)) hx
  exact hinner.trans houter
end FiniteFlow
end HadwigerLean
