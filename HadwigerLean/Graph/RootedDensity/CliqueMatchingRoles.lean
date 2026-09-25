import HadwigerLean.Graph.RootedDensity.CliqueMatching
import HadwigerLean.Woven.SparseTargetRoles

/-! Canonical root and matching role labels in the recursive target. -/

namespace HadwigerLean.RootedDensity

/-- The clique vertex with label `i` in `K_a + b K₂`. -/
def cliqueMatchingRootLabel (a : ℕ) :
    (b : ℕ) → Fin a → CliqueMatchingLabels a b
  | 0, i => i
  | b + 1, i => Sum.inl (cliqueMatchingRootLabel a b i)

/-- Endpoint `e` of matching edge `i` in `K_a + b K₂`. In the successor
step, edge zero is new and successor indices refer to old edges. -/
def cliqueMatchingPairLabel (a : ℕ) :
    (b : ℕ) → Fin b → Fin 2 → CliqueMatchingLabels a b
  | 0, i, _ => i.elim0
  | b + 1, i, e =>
      Fin.cases (Sum.inr e)
        (fun k => Sum.inl (cliqueMatchingPairLabel a b k e)) i

/-- The clique vertices are pairwise adjacent. -/
theorem cliqueMatching_root_adj (a b : ℕ) (i k : Fin a) (hik : i ≠ k) :
    (cliqueMatchingGraph a b).Adj
      (cliqueMatchingRootLabel a b i) (cliqueMatchingRootLabel a b k) := by
  induction b with
  | zero => simpa [cliqueMatchingGraph, cliqueMatchingRootLabel] using hik
  | succ b ih =>
      simpa [cliqueMatchingGraph, cliqueMatchingRootLabel] using ih

/-- Each added matching edge joins its two endpoint labels. -/
theorem cliqueMatching_pair_adj (a b : ℕ) (i : Fin b) :
    (cliqueMatchingGraph a b).Adj
      (cliqueMatchingPairLabel a b i 0)
      (cliqueMatchingPairLabel a b i 1) := by
  induction b with
  | zero => exact i.elim0
  | succ b ih =>
      induction i using Fin.cases with
      | zero => simp [cliqueMatchingPairLabel, cliqueMatchingGraph]
      | succ k =>
          simpa [cliqueMatchingPairLabel, cliqueMatchingGraph] using ih k


/-- Different clique labels remain distinct at every matching depth. -/
theorem cliqueMatching_root_injective (a b : ℕ) :
    Function.Injective (cliqueMatchingRootLabel a b) := by
  induction b with
  | zero => intro i k h; exact h
  | succ b ih =>
      intro i k h
      exact ih (Sum.inl_injective h)

/-- No clique label is a matching endpoint label. -/
theorem cliqueMatching_root_ne_pair (a b : ℕ)
    (i : Fin a) (k : Fin b) (e : Fin 2) :
    cliqueMatchingRootLabel a b i ≠ cliqueMatchingPairLabel a b k e := by
  induction b with
  | zero => exact k.elim0
  | succ b ih =>
      induction k using Fin.cases with
      | zero => simp [cliqueMatchingRootLabel, cliqueMatchingPairLabel]
      | succ k =>
          intro h
          exact ih k (Sum.inl_injective h)

/-- All ordered matching endpoints have different target labels. -/
theorem cliqueMatching_pair_injective (a b : ℕ) :
    Function.Injective (fun p : Fin b × Fin 2 =>
      cliqueMatchingPairLabel a b p.1 p.2) := by
  induction b with
  | zero => intro p; exact p.1.elim0
  | succ b ih =>
      rintro ⟨i, e⟩ ⟨k, f⟩ h
      induction i using Fin.cases with
      | zero =>
          induction k using Fin.cases with
          | zero =>
              have hef : e = f := Sum.inr_injective h
              simp [hef]
          | succ k =>
              simp [cliqueMatchingPairLabel] at h
      | succ i =>
          induction k using Fin.cases with
          | zero =>
              simp [cliqueMatchingPairLabel] at h
          | succ k =>
              have h' : cliqueMatchingPairLabel a b i e =
                  cliqueMatchingPairLabel a b k f := Sum.inl_injective h
              have hpair : (i, e) = (k, f) := ih (show
                (fun p : Fin b × Fin 2 => cliqueMatchingPairLabel a b p.1 p.2) (i, e) =
                (fun p : Fin b × Fin 2 => cliqueMatchingPairLabel a b p.1 p.2) (k, f)
                from h')
              rcases Prod.mk.inj hpair with ⟨hik, hef⟩
              simp [hik, hef]
/-- Map the clique roots and two endpoints of every requested pair to
exactly the corresponding roles of `K_a + b K₂`. -/
def cliqueMatchingRoleLabel (a b : ℕ) :
    Woven.DistinctRoleIndex a b → CliqueMatchingLabels a b
  | .inl i => cliqueMatchingRootLabel a b i
  | .inr (.inl i) => cliqueMatchingPairLabel a b i 0
  | .inr (.inr i) => cliqueMatchingPairLabel a b i 1

/-- Every root and pair-endpoint role receives a distinct target label. -/
theorem cliqueMatchingRoleLabel_injective (a b : ℕ) :
    Function.Injective (cliqueMatchingRoleLabel a b) := by
  have pairEq (i k : Fin b) (e f : Fin 2)
      (h : cliqueMatchingPairLabel a b i e = cliqueMatchingPairLabel a b k f) :
      (i, e) = (k, f) := by
    exact (cliqueMatching_pair_injective a b)
      (a₁ := (i, e)) (a₂ := (k, f)) h
  intro p q h
  cases p with
  | inl i =>
      cases q with
      | inl k =>
          have hik := (cliqueMatching_root_injective a b)
            (by simpa [cliqueMatchingRoleLabel] using h)
          simpa [hik]
      | inr q =>
          cases q with
          | inl k => exact False.elim ((cliqueMatching_root_ne_pair a b i k 0)
              (by simpa [cliqueMatchingRoleLabel] using h))
          | inr k => exact False.elim ((cliqueMatching_root_ne_pair a b i k 1)
              (by simpa [cliqueMatchingRoleLabel] using h))
  | inr p =>
      cases p with
      | inl i =>
          cases q with
          | inl k => exact False.elim ((cliqueMatching_root_ne_pair a b k i 0)
              (by simpa [cliqueMatchingRoleLabel] using h.symm))
          | inr q =>
              cases q with
              | inl k =>
                  have hpair : (i, (0 : Fin 2)) = (k, (0 : Fin 2)) :=
                    pairEq i k 0 0 (by simpa [cliqueMatchingRoleLabel] using h)
                  simpa using congrArg Prod.fst hpair
              | inr k =>
                  have hpair : (i, (0 : Fin 2)) = (k, (1 : Fin 2)) :=
                    pairEq i k 0 1 (by simpa [cliqueMatchingRoleLabel] using h)
                  exact False.elim ((by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.snd hpair))
      | inr i =>
          cases q with
          | inl k => exact False.elim ((cliqueMatching_root_ne_pair a b k i 1)
              (by simpa [cliqueMatchingRoleLabel] using h.symm))
          | inr q =>
              cases q with
              | inl k =>
                  have hpair : (i, (1 : Fin 2)) = (k, (0 : Fin 2)) :=
                    pairEq i k 1 0 (by simpa [cliqueMatchingRoleLabel] using h)
                  exact False.elim ((by decide : (1 : Fin 2) ≠ 0) (congrArg Prod.snd hpair))
              | inr k =>
                  have hpair : (i, (1 : Fin 2)) = (k, (1 : Fin 2)) :=
                    pairEq i k 1 1 (by simpa [cliqueMatchingRoleLabel] using h)
                  simpa using congrArg Prod.fst hpair

/-- The canonical role map is a bijection onto the target labels. -/
noncomputable def cliqueMatchingRoleEquiv (a b : ℕ) :
    Woven.DistinctRoleIndex a b ≃ CliqueMatchingLabels a b := by
  apply Equiv.ofBijective (cliqueMatchingRoleLabel a b)
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · exact cliqueMatchingRoleLabel_injective a b
  · calc
      Fintype.card (Woven.DistinctRoleIndex a b) = a + 2 * b := by
        simpa using Fintype.card_congr (Woven.distinctRoleEquiv a b)
      _ = Fintype.card (CliqueMatchingLabels a b) :=
        (cliqueMatchingLabels_card a b).symm

/-- A rooted model of the clique-plus-matching target yields a compatible
woven solution at its canonical root and matching roles. -/
theorem wovenSolution_of_cliqueMatching_model
    {V : Type*} {G : SimpleGraph V} {role : CliqueMatchingLabels a b → V}
    (M : RootedMinorModel (cliqueMatchingGraph a b) G role) :
    Nonempty (WovenSolution G
      (Woven.sparseSelectedRoots (cliqueMatchingRoleLabel a b) role)
      (Woven.sparseSelectedPairs (cliqueMatchingRoleLabel a b) role)) := by
  apply Woven.exists_solution_of_sparse_target_model M
    (cliqueMatchingRoleLabel a b) (cliqueMatchingRoleLabel_injective a b)
  · intro i k hik
    exact cliqueMatching_root_adj a b i k hik
  · intro i
    exact cliqueMatching_pair_adj a b i
end HadwigerLean.RootedDensity







