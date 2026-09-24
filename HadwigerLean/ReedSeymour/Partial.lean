import HadwigerLean.ReedSeymour.Egg
import HadwigerLean.Graph.SimplicialElimination
import Mathlib.Data.Finset.Max

/-!
# Partial egg decompositions and maximal support

Reed and Seymour first allow non-egg blocks provided they are simplicial in the
touching quotient and all their neighbors are eggs. Their proof chooses such a
decomposition with maximal egg support. Finiteness of the vertex set suffices
for this choice even though the index type and number of blocks may vary.
-/

namespace HadwigerLean

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I]
  {G : SimpleGraph V}

/-- The invariant used in the maximal-support argument. -/
def IsPartialEggDecomposition (P : ConnectedPartition G I) (w : V → ℝ) : Prop :=
  HasSimplicialElimination P.touchingQuotient ∧
  ∀ i, IsEgg G w (P.block i) ∨
    (IsSimplicialOn P.touchingQuotient Finset.univ i ∧
      ∀ j, P.touchingQuotient.Adj i j → IsEgg G w (P.block j))

/-- Vertices covered by egg blocks of a connected partition. -/
noncomputable def eggSupport (P : ConnectedPartition G I) (w : V → ℝ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∃ i, v ∈ P.block i ∧ IsEgg G w (P.block i))

omit [DecidableEq I] in
@[simp] theorem mem_eggSupport (P : ConnectedPartition G I) (w : V → ℝ) (v : V) :
    v ∈ eggSupport P w ↔ ∃ i, v ∈ P.block i ∧ IsEgg G w (P.block i) := by
  classical
  simp [eggSupport]

/-- A support realized by some partial egg decomposition, using `Fin n` labels. -/
def IsPartialEggSupport (G : SimpleGraph V) (w : V → ℝ) (S : Finset V) : Prop :=
  ∃ n : ℕ, ∃ P : ConnectedPartition G (Fin n),
    IsPartialEggDecomposition P w ∧ eggSupport P w = S

/-- Among any nonempty collection of partial egg decompositions, one has
support of maximal cardinality. The index type may change between candidates. -/
theorem exists_maximal_partial_egg_support (G : SimpleGraph V) (w : V → ℝ)
    (hinit : ∃ n : ℕ, ∃ P : ConnectedPartition G (Fin n),
      IsPartialEggDecomposition P w) :
    ∃ n : ℕ, ∃ P : ConnectedPartition G (Fin n),
      IsPartialEggDecomposition P w ∧
        ∀ m : ℕ, ∀ Q : ConnectedPartition G (Fin m),
          IsPartialEggDecomposition Q w →
            (eggSupport Q w).card ≤ (eggSupport P w).card := by
  classical
  let candidates : Finset (Finset V) :=
    Finset.univ.filter (IsPartialEggSupport G w)
  have hne : candidates.Nonempty := by
    obtain ⟨n, P, hP⟩ := hinit
    refine ⟨eggSupport P w, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨n, P, hP, rfl⟩
  obtain ⟨S, hS, hmax⟩ := candidates.exists_max_image Finset.card hne
  have hrealized : IsPartialEggSupport G w S := by
    simpa only [candidates, Finset.mem_filter, Finset.mem_univ, true_and] using hS
  obtain ⟨n, P, hP, hsupport⟩ := hrealized
  refine ⟨n, P, hP, ?_⟩
  intro m Q hQ
  have hQmem : eggSupport Q w ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨m, Q, hQ, rfl⟩
  simpa only [hsupport] using hmax (eggSupport Q w) hQmem

namespace ConnectedPartition

variable {J : Type*} [Fintype J]

/-- Relabel the blocks of a connected partition. -/
def relabel (P : ConnectedPartition G I) (e : J ≃ I) :
    ConnectedPartition G J where
  block j := P.block (e j)
  connected j := P.connected (e j)
  disjoint := by
    intro a b hab
    exact P.disjoint (by intro he; exact hab (e.injective he))
  cover := by
    intro v
    obtain ⟨i, hi⟩ := P.cover v
    exact ⟨e.symm i, by simpa using hi⟩

/-- Relabeling gives an isomorphic touching quotient. -/
def touchingQuotientIso (P : ConnectedPartition G I) (e : J ≃ I) :
    (P.relabel e).touchingQuotient ≃g P.touchingQuotient where
  toEquiv := e
  map_rel_iff' := by
    intro a b
    change (e a ≠ e b ∧ ∃ x ∈ P.block (e a), ∃ y ∈ P.block (e b), G.Adj x y) ↔
      (a ≠ b ∧ ∃ x ∈ P.block (e a), ∃ y ∈ P.block (e b), G.Adj x y)
    constructor
    · rintro ⟨hne, hw⟩
      exact ⟨fun he => hne (congrArg e he), hw⟩
    · rintro ⟨hne, hw⟩
      exact ⟨fun he => hne (e.injective he), hw⟩

omit [DecidableEq I] in
/-- Relabeling preserves the exact set of vertices in egg blocks. -/
theorem eggSupport_relabel [DecidableEq J]
    (P : ConnectedPartition G I) (e : J ≃ I) (w : V → ℝ) :
    eggSupport (P.relabel e) w = eggSupport P w := by
  classical
  ext v
  simp only [mem_eggSupport]
  constructor
  · rintro ⟨j, hv, hEgg⟩
    exact ⟨e j, hv, hEgg⟩
  · rintro ⟨i, hv, hEgg⟩
    exact ⟨e.symm i, by simpa [relabel] using hv,
      by simpa [relabel] using hEgg⟩

end ConnectedPartition
/-- A connected graph has the one-block connected partition. -/
def oneBlockPartition {U : Type*} [Fintype U] {H : SimpleGraph U}
    (hconn : H.Connected) : ConnectedPartition H (Fin 1) where
  block _ := Set.univ
  connected _ := (SimpleGraph.induceUnivIso H).connected_iff.mpr hconn
  disjoint := by
    intro i j hij
    exact False.elim (hij (Subsingleton.elim i j))
  cover v := ⟨0, Set.mem_univ v⟩

/-- A connected graph supplies an initial partial decomposition, possibly with
empty egg support. This avoids a separate positive-support construction. -/
theorem exists_initial_partial_egg_decomposition
    {U : Type*} [Fintype U] {H : SimpleGraph U}
    (hconn : H.Connected) (w : U → ℝ) :
    ∃ n : ℕ, ∃ P : ConnectedPartition H (Fin n),
      IsPartialEggDecomposition P w := by
  classical
  let P := oneBlockPartition hconn
  refine ⟨1, P, ?_⟩
  constructor
  · intro s hs
    obtain ⟨i, hi⟩ := hs
    refine ⟨i, hi, ?_⟩
    intro x y hx hy hix hiy hxy
    exact False.elim (hxy (Subsingleton.elim x y))
  · intro i
    right
    constructor
    · intro x y hx hy hix hiy hxy
      exact False.elim (hxy (Subsingleton.elim x y))
    · intro j hadj
      have hij : i = j := Subsingleton.elim i j
      subst j
      exact False.elim (P.touchingQuotient.irrefl hadj)
end HadwigerLean
