import HadwigerLean.Graph.CliqueDensity.Theorem
import HadwigerLean.Graph.SimplicialElimination
import Mathlib.Tactic

/-!
# Coloring consequences of the coefficient-30 clique-minor density bound
-/

namespace HadwigerLean

variable {V : Type*} [Fintype V]

/-- The standard degree-elimination coloring argument, phrased for every
nonempty induced vertex set. -/
theorem colorable_of_induced_low_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (helim : ∀ s : Finset V, s.Nonempty →
      ∃ v : (s : Set V), (G.induce (s : Set V)).degree v < d) :
    G.Colorable d := by
  classical
  have aux : ∀ s : Finset V, (G.induce (s : Set V)).Colorable d := by
    intro s
    refine Finset.strongInductionOn (p := fun s => (G.induce (s : Set V)).Colorable d) s ?_
    intro s ih
    by_cases hs : s.Nonempty
    · obtain ⟨⟨v, hv⟩, hdeg⟩ := helim s hs
      let t : Finset V := s.erase v
      have ht : t ⊂ s := Finset.erase_ssubset hv
      let C : (G.induce (t : Set V)).Coloring (Fin d) :=
        Classical.choice (ih t ht)
      let N : Finset V := G.neighborFinset v ∩ s
      have hNmap : N =
          ((G.induce (s : Set V)).neighborFinset ⟨v, hv⟩).map
            (.subtype (· ∈ (s : Set V))) := by
        ext x
        simp [N, SimpleGraph.mem_neighborFinset, and_comm, and_left_comm]
      have hNcard : N.card < d := by
        rw [hNmap, Finset.card_map]
        simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdeg
      have hNa {x : V} (hx : x ∈ N) : G.Adj v x := by
        exact (G.mem_neighborFinset v x).mp (Finset.mem_inter.mp hx).1
      have hNs {x : V} (hx : x ∈ N) : x ∈ s :=
        (Finset.mem_inter.mp hx).2
      have hNt {x : V} (hx : x ∈ N) : x ∈ t := by
        exact Finset.mem_erase.mpr ⟨(G.ne_of_adj (hNa hx)).symm, hNs hx⟩
      let neighborColor : N → Fin d := fun x => C ⟨x.1, hNt x.2⟩
      let used : Finset (Fin d) := Finset.univ.image neighborColor
      have hused : used.card ≤ N.card := by
        simpa [used] using
          (Finset.card_image_le (s := (Finset.univ : Finset N)) (f := neighborColor))
      have hmissing : ∃ a : Fin d, a ∉ used := by
        by_contra h
        push Not at h
        have hsubset : (Finset.univ : Finset (Fin d)) ⊆ used := by
          intro a _
          exact h a
        have hcard := Finset.card_le_card hsubset
        simp only [Finset.card_univ, Fintype.card_fin] at hcard
        omega
      obtain ⟨a, ha⟩ := hmissing
      let color : {x : V // x ∈ (s : Set V)} → Fin d := fun x =>
        if hx : x.1 = v then a
        else C ⟨x.1, Finset.mem_erase.mpr ⟨hx, x.2⟩⟩
      refine ⟨SimpleGraph.Coloring.mk color ?_⟩
      intro x y hxy
      change G.Adj x.1 y.1 at hxy
      by_cases hx : x.1 = v
      · by_cases hy : y.1 = v
        · rw [hx, hy] at hxy
          exact False.elim (G.irrefl hxy)
        · have hyN : y.1 ∈ N := by
            apply Finset.mem_inter.mpr
            exact ⟨(G.mem_neighborFinset v y.1).mpr (by simpa only [hx] using hxy), y.2⟩
          have hcy : C ⟨y.1, hNt hyN⟩ ∈ used := by
            apply Finset.mem_image.mpr
            exact ⟨⟨y.1, hyN⟩, Finset.mem_univ _, rfl⟩
          intro heq
          have heq' : a = C ⟨y.1, hNt hyN⟩ := by
            simpa only [color, dif_pos hx, dif_neg hy] using heq
          exact ha (heq' ▸ hcy)
      · by_cases hy : y.1 = v
        · have hxN : x.1 ∈ N := by
            apply Finset.mem_inter.mpr
            exact ⟨(G.mem_neighborFinset v x).mpr (by simpa only [hy] using hxy.symm), x.2⟩
          have hcx : C ⟨x.1, hNt hxN⟩ ∈ used := by
            apply Finset.mem_image.mpr
            exact ⟨⟨x.1, hxN⟩, Finset.mem_univ _, rfl⟩
          intro heq
          have heq' : C ⟨x.1, hNt hxN⟩ = a := by
            simpa only [color, dif_neg hx, dif_pos hy] using heq
          exact ha (heq' ▸ hcx)
        · have hxy' : (G.induce (t : Set V)).Adj
              ⟨x.1, Finset.mem_erase.mpr ⟨hx, x.2⟩⟩
              ⟨y.1, Finset.mem_erase.mpr ⟨hy, y.2⟩⟩ := hxy
          simpa only [color, dif_neg hx, dif_neg hy] using C.valid hxy'
    · have hEmpty : IsEmpty {x : V // x ∈ (s : Set V)} := by
        constructor
        intro x
        exact hs ⟨x.1, x.2⟩
      letI := hEmpty
      exact SimpleGraph.Colorable.of_isEmpty d
  let C : (G.induce ((Finset.univ : Finset V) : Set V)).Coloring (Fin d) :=
    Classical.choice (aux Finset.univ)
  refine ⟨SimpleGraph.Coloring.mk (fun v => C ⟨v, Finset.mem_univ v⟩) ?_⟩
  intro v w hvw
  exact C.valid hvw


/-- A strict edge-per-vertex bound yields a vertex below twice that bound. -/
theorem exists_degree_lt_twice_of_edgeCount_lt
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ)
    (hcard : 0 < Fintype.card V)
    (hedges : (edgeCount G : ℝ) < c * (Fintype.card V : ℝ)) :
    ∃ v : V, (G.degree v : ℝ) < 2 * c := by
  classical
  have hsum : (∑ v : V, (G.degree v : ℝ)) = 2 * (edgeCount G : ℝ) := by
    exact_mod_cast sum_degree_eq_two_edgeCount G
  have hconst : (∑ _v : V, 2 * c) = (Fintype.card V : ℝ) * (2 * c) := by simp
  have hlt : (∑ v : V, (G.degree v : ℝ)) < ∑ _v : V, 2 * c := by
    rw [hsum, hconst]
    nlinarith [hedges]
  obtain ⟨v, _hv, hdegree⟩ := Finset.exists_lt_of_sum_lt hlt
  exact ⟨v, hdegree⟩

/-- The coefficient-30 density theorem gives a vertex of degree below
`60 r sqrt(log r)` in every nonempty minor-free graph. -/
theorem exists_degree_lt_kt_color_threshold
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 2 ≤ r)
    (hminor : ¬ HasCliqueMinor G r) (hcard : 0 < Fintype.card V) :
    ∃ v : V, (G.degree v : ℝ) <
      60 * (r : ℝ) * Real.sqrt (Real.log (r : ℝ)) := by
  have hdensity : edgeDensity G <
      30 * (r : ℝ) * Real.sqrt (Real.log (r : ℝ)) := by
    by_contra h
    exact hminor (hasCliqueMinor_of_edgeDensity_ge G r hr (le_of_not_gt h))
  have hcardR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hcard
  have hedges : (edgeCount G : ℝ) <
      (30 * (r : ℝ) * Real.sqrt (Real.log (r : ℝ))) *
        (Fintype.card V : ℝ) := by
    have h := mul_lt_mul_of_pos_right hdensity hcardR
    rw [edgeDensity, div_mul_cancel₀ _ hcardR.ne'] at h
    exact h
  obtain ⟨v, hv⟩ := exists_degree_lt_twice_of_edgeCount_lt G
    (30 * (r : ℝ) * Real.sqrt (Real.log (r : ℝ))) hcard hedges
  exact ⟨v, by nlinarith [hv]⟩


/-- The coefficient-30 density theorem yields the corresponding greedy
coloring bound, with a natural ceiling on the number of colors. -/
theorem colorable_of_no_clique_minor_kt
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 2 ≤ r)
    (hminor : ¬ HasCliqueMinor G r) :
    G.Colorable ⌈60 * (r : ℝ) * Real.sqrt (Real.log (r : ℝ))⌉₊ := by
  classical
  apply colorable_of_induced_low_degree G _
  intro s hs
  have hminorS : ¬ HasCliqueMinor (G.induce (s : Set V)) r := by
    intro h
    let e : G.induce (s : Set V) ↪g G := SimpleGraph.Embedding.induce _
    exact hminor (hasCliqueMinor_map e.toHom e.injective h)
  have hcardS : 0 < Fintype.card (s : Set V) := by
    letI : Nonempty (s : Set V) := ⟨⟨hs.choose, hs.choose_spec⟩⟩
    exact Fintype.card_pos
  obtain ⟨v, hv⟩ := exists_degree_lt_kt_color_threshold
    (G.induce (s : Set V)) r hr hminorS hcardS
  exact ⟨v, Nat.lt_ceil.mpr hv⟩

/-- Real-valued form of the coefficient-30 clique-minor coloring bound. -/
theorem chromatic_lt_kt_color_threshold
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 2 ≤ r)
    (hminor : ¬ HasCliqueMinor G r) :
    (chromatic G : ℝ) <
      60 * (r : ℝ) * Real.sqrt (Real.log (r : ℝ)) + 1 := by
  have hcolor := colorable_of_no_clique_minor_kt G r hr hminor
  have hχ : chromatic G ≤
      ⌈60 * (r : ℝ) * Real.sqrt (Real.log (r : ℝ))⌉₊ :=
    (chromatic_le_iff_colorable G _).mpr hcolor
  have hχR : (chromatic G : ℝ) ≤
      (⌈60 * (r : ℝ) * Real.sqrt (Real.log (r : ℝ))⌉₊ : ℝ) := by
    exact_mod_cast hχ
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
  have hlog : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hrR
  exact hχR.trans_lt (Nat.ceil_lt_add_one (by positivity))

end HadwigerLean
