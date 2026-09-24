import HadwigerLean.ReedSeymour.Initial

/-!
# Closing the maximal-support argument

The remaining local improvement theorem must turn each non-egg block of a
partial decomposition into a strictly larger egg support. Once that theorem is
available, finite maximization yields an all-egg decomposition. This file
checks the final contradiction step without treating the improvement theorem
as an axiom.
-/

namespace HadwigerLean

variable {V : Type*} [Fintype V]

/-- The local improvement obligation in the Reed--Seymour proof. -/
def HasEggSupportImprovement (G : SimpleGraph V) (w : V → ℝ) : Prop :=
  ∀ n : ℕ, ∀ P : ConnectedPartition G (Fin n),
    IsPartialEggDecomposition P w →
    ∀ i : Fin n, ¬ IsEgg G w (P.block i) →
      ∃ m : ℕ, ∃ Q : ConnectedPartition G (Fin m),
        IsPartialEggDecomposition Q w ∧ eggSupport P w ⊂ eggSupport Q w

/-- Every local improvement rule yields an egg partition with a chordal
(simplicial-elimination) touching quotient. -/
theorem exists_all_egg_partition_of_improvement
    (G : SimpleGraph V) (w : V → ℝ)
    (hImprove : HasEggSupportImprovement G w) :
    ∃ n : ℕ, ∃ P : ConnectedPartition G (Fin n),
      (∀ i, IsEgg G w (P.block i)) ∧
        HasSimplicialElimination P.touchingQuotient := by
  obtain ⟨n, P, hP, hmax⟩ := exists_maximal_partial_egg_support_any G w
  have hall : ∀ i, IsEgg G w (P.block i) := by
    intro i
    by_contra hnot
    obtain ⟨m, Q, hQ, hstrict⟩ := hImprove n P hP i hnot
    exact (Nat.not_lt_of_ge (hmax m Q hQ)) (Finset.card_lt_card hstrict)
  exact ⟨n, P, hall, hP.1⟩

end HadwigerLean
