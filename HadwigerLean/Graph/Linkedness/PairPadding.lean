import HadwigerLean.Graph.Linkedness.PairSlots
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

/-!
# Padding a partial pairing to exactly k pairs
-/

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Extend `n ≤ k` prescribed disjoint pairs to `k` disjoint pairs whose
terminals include every vertex of `Y`. The original pairs occupy the first
`n` indices. -/
theorem exists_padded_pairs
    (k n : ℕ) (hk : 0 < k)
    (Q : IndexedPairs (Fin n) V)
    (hQ : Q.DisjointTerminals)
    (hne : ∀ i, Q.start i ≠ Q.finish i)
    (Y : Finset V)
    (hQY : ∀ i, Q.terminals i ⊆ (Y : Set V))
    (hY : Y.card ≤ 2 * k)
    (hV : 2 * k ≤ Fintype.card V) :
    ∃ (hn : n ≤ k) (P : IndexedPairs (Fin k) V),
      P.DisjointTerminals ∧
      (∀ i, P.start i ≠ P.finish i) ∧
      (∀ i : Fin n, P.start (Fin.castLE hn i) = Q.start i) ∧
      (∀ i : Fin n, P.finish (Fin.castLE hn i) = Q.finish i) ∧
      Y ⊆ terminalFinset P := by
  classical
  have hQterm : terminalFinset Q ⊆ Y := by
    intro v hv
    rcases (mem_terminalFinset Q v).mp hv with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact hQY i (by simp [IndexedPairs.terminals, hi])
    · exact hQY i (by simp [IndexedPairs.terminals, hi])
  have hn : n ≤ k := by
    have hc := terminalFinset_card_eq_two_mul n Q hQ hne
    have hcard := Finset.card_le_card hQterm
    omega
  obtain ⟨Z, hYZ, _hZV, hZcard⟩ :=
    Finset.exists_subsuperset_card_eq (s := Y) (t := Finset.univ)
      (n := 2 * k) (Finset.subset_univ Y) hY (by simpa using hV)
  have hVpos : 0 < Fintype.card V := by omega
  haveI : Nonempty V := Fintype.card_pos_iff.mp hVpos
  let v₀ : V := Classical.choice inferInstance
  let S : Finset (Fin k × Fin 2) :=
    Finset.univ.filter (fun z => (z.1 : ℕ) < n)
  let f : Fin k × Fin 2 → V := fun z =>
    if hz : (z.1 : ℕ) < n then
      pairOccurrence Q (⟨z.1.1,hz⟩,z.2)
    else v₀
  have hSmem (z : Fin k × Fin 2) : z ∈ S ↔ (z.1 : ℕ) < n := by
    simp [S]
  have hSmap : S.image f ⊆ Z := by
    intro x hx
    obtain ⟨z, hzS, rfl⟩ := Finset.mem_image.mp hx
    have hz : (z.1 : ℕ) < n := (hSmem z).mp hzS
    have hf : f z = pairOccurrence Q (⟨z.1.1,hz⟩,z.2) := by
      simp [f, hz]
    rw [hf]
    apply hYZ
    by_cases hd : z.2 = 0
    · simpa [pairOccurrence, hd] using hQY ⟨z.1.1,hz⟩
        (show Q.start ⟨z.1.1,hz⟩ ∈ Q.terminals ⟨z.1.1,hz⟩ by
          simp [IndexedPairs.terminals])
    · simpa [pairOccurrence, hd] using hQY ⟨z.1.1,hz⟩
        (show Q.finish ⟨z.1.1,hz⟩ ∈ Q.terminals ⟨z.1.1,hz⟩ by
          simp [IndexedPairs.terminals])
  have hSinj : Set.InjOn f S := by
    intro x hx y hy heq
    have hx' : (x.1 : ℕ) < n := (hSmem x).mp hx
    have hy' : (y.1 : ℕ) < n := (hSmem y).mp hy
    have hocc :
        pairOccurrence Q (⟨x.1.1,hx'⟩,x.2) =
        pairOccurrence Q (⟨y.1.1,hy'⟩,y.2) := by
      simpa [f, hx', hy'] using heq
    have hroles := pairOccurrence_injective Q hQ hne hocc
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun z : Fin n × Fin 2 => z.1.1) hroles
    · exact congrArg (fun z : Fin n × Fin 2 => z.2) hroles
  have hcard : Fintype.card (Fin k × Fin 2) = Z.card := by
    simp [Fintype.card_prod, hZcard]
    omega
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq hcard hSmap hSinj
  let P : IndexedPairs (Fin k) V :=
    ⟨fun i => (g (i,0) : V), fun i => (g (i,1) : V)⟩
  have hPocc (z : Fin k × Fin 2) : pairOccurrence P z = (g z : V) := by
    rcases z with ⟨i,d⟩
    fin_cases d <;> simp [pairOccurrence, P]
  have hPinj : Function.Injective (pairOccurrence P) := by
    intro x y hxy
    rw [hPocc, hPocc] at hxy
    exact g.injective (Subtype.val_injective hxy)
  obtain ⟨hPdisj, hPne⟩ := pair_properties_of_occurrence_injective P hPinj
  have hPstart (i : Fin n) : P.start (Fin.castLE hn i) = Q.start i := by
    have hs : ((Fin.castLE hn i, (0 : Fin 2)) : Fin k × Fin 2) ∈ S :=
      (hSmem _).mpr i.isLt
    have heq := hg _ hs
    simpa [P, f, pairOccurrence, i.isLt] using heq
  have hPfinish (i : Fin n) : P.finish (Fin.castLE hn i) = Q.finish i := by
    have hs : ((Fin.castLE hn i, (1 : Fin 2)) : Fin k × Fin 2) ∈ S :=
      (hSmem _).mpr i.isLt
    have heq := hg _ hs
    simpa [P, f, pairOccurrence, i.isLt] using heq
  have hcover : Y ⊆ terminalFinset P := by
    intro y hy
    have hyZ : y ∈ Z := hYZ hy
    obtain ⟨z, hz⟩ := g.surjective ⟨y,hyZ⟩
    have hzy : (g z : V) = y := congrArg Subtype.val hz
    rcases z with ⟨i,d⟩
    fin_cases d
    · exact (mem_terminalFinset P y).mpr (Or.inl ⟨i, by simpa [P] using hzy⟩)
    · exact (mem_terminalFinset P y).mpr (Or.inr ⟨i, by simpa [P] using hzy⟩)
  exact ⟨hn, P, hPdisj, hPne, hPstart, hPfinish, hcover⟩

end Linkedness
end HadwigerLean
