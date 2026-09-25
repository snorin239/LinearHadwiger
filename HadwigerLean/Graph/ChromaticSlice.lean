import HadwigerLean.Graph.Finite
import Mathlib.Tactic
import Mathlib.Data.Nat.Find

/-!
# Exact chromatic slices of finite graphs
-/

namespace HadwigerLean

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Chromatic number decreases when the induced vertex set shrinks. -/
theorem chromatic_induce_mono_finset
    (G : SimpleGraph V) {S T : Finset V} (hST : S ⊆ T) :
    chromatic (G.induce (S : Set V)) ≤ chromatic (G.induce (T : Set V)) := by
  classical
  obtain ⟨C⟩ := colorable_chromatic (G.induce (T : Set V))
  apply (chromatic_le_iff_colorable _ _).mpr
  refine ⟨SimpleGraph.Coloring.mk (fun x => C ⟨x.1, hST x.2⟩) ?_⟩
  intro x y hxy
  exact C.valid hxy

/-- Inducing on the full vertex set preserves the finite chromatic number. -/
theorem chromatic_induce_univ_finset (G : SimpleGraph V) :
    chromatic (G.induce ((Finset.univ : Finset V) : Set V)) = chromatic G := by
  change ENat.toNat (G.induce ((Finset.univ : Finset V) : Set V)).chromaticNumber =
    ENat.toNat G.chromaticNumber
  rw [show ((Finset.univ : Finset V) : Set V) = Set.univ by ext; simp]
  exact congrArg ENat.toNat (SimpleGraph.chromaticNumber_congr (SimpleGraph.induceUnivIso G))

/-- Removing one vertex reduces the chromatic number by at most one. -/
theorem chromatic_induce_le_erase_add_one
    (G : SimpleGraph V) (S : Finset V) (v : V) (hv : v ∈ S) :
    chromatic (G.induce (S : Set V)) ≤
      chromatic (G.induce (S.erase v : Set V)) + 1 := by
  classical
  let n := chromatic (G.induce (S.erase v : Set V))
  let C : (G.induce (S.erase v : Set V)).Coloring (Fin n) :=
    Classical.choice (colorable_chromatic _)
  let color : ↥(S : Set V) → Fin (n + 1) := fun x =>
    if hx : x.1 = v then Fin.last n
    else (C ⟨x.1, Finset.mem_erase.mpr ⟨hx, x.2⟩⟩).castSucc
  apply (chromatic_le_iff_colorable _ _).mpr
  refine ⟨SimpleGraph.Coloring.mk color ?_⟩
  intro x y hxy
  change G.Adj x.1 y.1 at hxy
  by_cases hx : x.1 = v
  · by_cases hy : y.1 = v
    · rw [hx, hy] at hxy
      exact False.elim (G.irrefl hxy)
    · intro heq
      have hval := congrArg Fin.val heq
      simp [color, hx, hy] at hval
      have hsmall := (C ⟨y.1, Finset.mem_erase.mpr ⟨hy, y.2⟩⟩).isLt
      omega
  · by_cases hy : y.1 = v
    · intro heq
      have hval := congrArg Fin.val heq
      simp [color, hx, hy] at hval
      have hsmall := (C ⟨x.1, Finset.mem_erase.mpr ⟨hx, x.2⟩⟩).isLt
      omega
    · have hxy' : (G.induce (S.erase v : Set V)).Adj
          ⟨x.1, Finset.mem_erase.mpr ⟨hx, x.2⟩⟩
          ⟨y.1, Finset.mem_erase.mpr ⟨hy, y.2⟩⟩ := hxy
      intro heq
      have heq' : C ⟨x.1, Finset.mem_erase.mpr ⟨hx, x.2⟩⟩ =
          C ⟨y.1, Finset.mem_erase.mpr ⟨hy, y.2⟩⟩ := by
        exact Fin.castSucc_injective n (by simpa [color, hx, hy] using heq)
      exact C.valid hxy' heq'

/-- Every integer from zero to the chromatic number occurs as the
chromatic number of an induced subgraph. -/
theorem exists_induced_chromatic_eq
    (G : SimpleGraph V) (n : ℕ) (hn : n ≤ chromatic G) :
    ∃ S : Finset V, chromatic (G.induce (S : Set V)) = n := by
  classical
  let P (m : ℕ) : Prop := ∃ S : Finset V,
    S.card = m ∧ n ≤ chromatic (G.induce (S : Set V))
  have hP : ∃ m, P m := by
    refine ⟨Fintype.card V, Finset.univ, by simp, ?_⟩
    rw [chromatic_induce_univ_finset]
    exact hn
  obtain ⟨S, hScard, hSχ⟩ := Nat.find_spec hP
  refine ⟨S, Nat.le_antisymm ?_ hSχ⟩
  by_contra hnot
  have hbig : n + 1 ≤ chromatic (G.induce (S : Set V)) := by omega
  have hS : S.Nonempty := by
    by_contra h
    have hEmpty : IsEmpty (S : Set V) := by
      constructor
      intro x
      exact h ⟨x.1, x.2⟩
    have hz : chromatic (G.induce (S : Set V)) = 0 :=
      (chromatic_eq_zero_iff _).mpr hEmpty
    omega
  obtain ⟨v, hv⟩ := hS
  have hcard : (S.erase v).card < Nat.find hP := by
    simpa [← hScard] using Finset.card_erase_lt_of_mem hv
  have hsmall : chromatic (G.induce (S.erase v : Set V)) < n := by
    by_contra h
    exact Nat.find_min hP hcard
      ⟨S.erase v, rfl, Nat.le_of_not_gt h⟩
  have hstep := chromatic_induce_le_erase_add_one G S v hv
  omega

end HadwigerLean
