import HadwigerLean.Graph.Linkedness.Massed
import Mathlib.Tactic

/-!
# Assigning the two occurrences of every prescribed pair to distinct
members of an enumerated root set
-/

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertex used by one terminal occurrence. -/
def pairOccurrence {n : ℕ} (Q : IndexedPairs (Fin n) V)
    (z : Fin n × Fin 2) : V :=
  if z.2 = 0 then Q.start z.1 else Q.finish z.1

/-- Distinct nontrivial pairs have distinct terminal occurrences. -/
theorem pairOccurrence_injective {n : ℕ}
    (Q : IndexedPairs (Fin n) V)
    (hQ : Q.DisjointTerminals)
    (hne : ∀ i, Q.start i ≠ Q.finish i) :
    Function.Injective (pairOccurrence Q) := by
  intro x y hxy
  rcases x with ⟨i,d⟩
  rcases y with ⟨j,e⟩
  fin_cases d <;> fin_cases e
  · have hij : i = j := IndexedPairs.start_injective hQ (by simpa [pairOccurrence] using hxy)
    subst j
    rfl
  · have heq : Q.start i = Q.finish j := by simpa [pairOccurrence] using hxy
    by_cases hij : i = j
    · subst j
      exact False.elim ((hne i) heq)
    · have hdis := Set.disjoint_left.mp (hQ hij)
      exact False.elim (hdis
        (show Q.start i ∈ Q.terminals i from Or.inl rfl)
        (show Q.start i ∈ Q.terminals j from Or.inr heq))
  · have heq : Q.finish i = Q.start j := by simpa [pairOccurrence] using hxy
    by_cases hij : i = j
    · subst j
      exact False.elim ((hne i) heq.symm)
    · have hdis := Set.disjoint_left.mp (hQ hij)
      exact False.elim (hdis
        (show Q.finish i ∈ Q.terminals i from Or.inr rfl)
        (show Q.finish i ∈ Q.terminals j from Or.inl heq))
  · have hij : i = j := IndexedPairs.finish_injective hQ (by simpa [pairOccurrence] using hxy)
    subst j
    rfl

/-- An injective occurrence map certifies disjoint, nontrivial pairs. -/
theorem pair_properties_of_occurrence_injective {n : ℕ}
    (Q : IndexedPairs (Fin n) V)
    (hinj : Function.Injective (pairOccurrence Q)) :
    Q.DisjointTerminals ∧ (∀ i, Q.start i ≠ Q.finish i) := by
  constructor
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    rcases hi with hi0 | hi1 <;> rcases hj with hj0 | hj1
    · have heq := hinj (show pairOccurrence Q (i,0) = pairOccurrence Q (j,0) by
        simpa [pairOccurrence] using hi0.symm.trans hj0)
      exact hij (congrArg Prod.fst heq)
    · have heq := hinj (show pairOccurrence Q (i,0) = pairOccurrence Q (j,1) by
        simpa [pairOccurrence] using hi0.symm.trans hj1)
      exact hij (congrArg Prod.fst heq)
    · have heq := hinj (show pairOccurrence Q (i,1) = pairOccurrence Q (j,0) by
        simpa [pairOccurrence] using hi1.symm.trans hj0)
      exact hij (congrArg Prod.fst heq)
    · have heq := hinj (show pairOccurrence Q (i,1) = pairOccurrence Q (j,1) by
        simpa [pairOccurrence] using hi1.symm.trans hj1)
      exact hij (congrArg Prod.fst heq)
  · intro i heq
    have h := hinj (show pairOccurrence Q (i,0) = pairOccurrence Q (i,1) by
      simpa [pairOccurrence] using heq)
    exact (show (0 : Fin 2) ≠ 1 by decide) (congrArg Prod.snd h)
/-- Every pairing inside the enumerated root set determines an injective
assignment of its terminal occurrences to root indices. -/
theorem exists_pair_slots
    {r n : ℕ} (P : IndexedPairs (Fin r) V)
    (Q : IndexedPairs (Fin n) V)
    (hQ : Q.DisjointTerminals)
    (hne : ∀ i, Q.start i ≠ Q.finish i)
    (hX : ∀ i, Q.terminals i ⊆
      (Finset.univ.image P.start : Finset V)) :
    ∃ slot : Fin n × Fin 2 → Fin r,
      Function.Injective slot ∧
      (∀ i, Q.start i = P.start (slot (i,0))) ∧
      (∀ i, Q.finish i = P.start (slot (i,1))) := by
  classical
  let X : Finset V := Finset.univ.image P.start
  have hmem (z : Fin n × Fin 2) : pairOccurrence Q z ∈ X := by
    by_cases hd : z.2 = 0
    · simpa [pairOccurrence, hd, X] using
        hX z.1 (show Q.start z.1 ∈ Q.terminals z.1 by
          simp [IndexedPairs.terminals])
    · simpa [pairOccurrence, hd, X] using
        hX z.1 (show Q.finish z.1 ∈ Q.terminals z.1 by
          simp [IndexedPairs.terminals])
  let index (v : V) (hv : v ∈ X) : Fin r :=
    (Finset.mem_image.mp hv).choose
  have hindex (v : V) (hv : v ∈ X) : P.start (index v hv) = v :=
    (Finset.mem_image.mp hv).choose_spec.2
  let slot (z : Fin n × Fin 2) : Fin r :=
    index (pairOccurrence Q z) (hmem z)
  have hslot : Function.Injective slot := by
    intro x y hxy
    apply pairOccurrence_injective Q hQ hne
    calc
      pairOccurrence Q x = P.start (slot x) := (hindex (pairOccurrence Q x) (hmem x)).symm
      _ = P.start (slot y) := congrArg P.start hxy
      _ = pairOccurrence Q y := hindex (pairOccurrence Q y) (hmem y)
  refine ⟨slot, hslot, ?_, ?_⟩
  · intro i
    simpa [slot, pairOccurrence] using (hindex (Q.start i) (hmem (i,0))).symm
  · intro i
    simpa [slot, pairOccurrence] using (hindex (Q.finish i) (hmem (i,1))).symm

end Linkedness
end HadwigerLean
