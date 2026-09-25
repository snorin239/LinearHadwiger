import HadwigerLean.Woven.NormalizedSolution
import HadwigerLean.Graph.NeighborProxies

/-!
# Occupied roles and normalized proxy selection

Roots and terminal occurrences are enumerated with exactly `a + 2*j`
slots. The occupied original vertices may repeat across slots. A degree
bound supplies a distinct adjacent proxy outside all occupied originals.
-/

namespace HadwigerLean

universe v

namespace Woven

variable {V : Type v} [Fintype V] [DecidableEq V]
  {a j : ℕ}

/-- Original vertices indexed by the canonical finite role-slot order. -/
noncomputable def originalRoleFin
    (root : Fin a → V) (P : IndexedPairs (Fin j) V) :
    Fin (a + 2 * j) → V :=
  originalRole root P ∘ (distinctRoleEquiv a j).symm

/-- Every vertex occupied by any original role. -/
noncomputable def occupiedRoles
    (root : Fin a → V) (P : IndexedPairs (Fin j) V) : Finset V := by
  classical
  exact Finset.univ.image (originalRoleFin root P)

/-- The normalized vertex set after all original roles are deleted. -/
def normalizedSet
    (root : Fin a → V) (P : IndexedPairs (Fin j) V) : Set V :=
  (occupiedRoles root P : Set V)ᶜ

theorem originalRole_mem_occupied
    (root : Fin a → V) (P : IndexedPairs (Fin j) V)
    (slot : DistinctRoleIndex a j) :
    originalRole root P slot ∈ occupiedRoles root P := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨(distinctRoleEquiv a j) slot, Finset.mem_univ _, ?_⟩
  simp [originalRoleFin]

theorem occupiedRoles_card_le
    (root : Fin a → V) (P : IndexedPairs (Fin j) V) :
    (occupiedRoles root P).card ≤ a + 2 * j := by
  classical
  calc
    (occupiedRoles root P).card ≤
        (Finset.univ : Finset (Fin (a + 2 * j))).card :=
      Finset.card_image_le
    _ = a + 2 * j := by simp

theorem root_not_normalized
    (root : Fin a → V) (P : IndexedPairs (Fin j) V)
    (i : Fin a) : root i ∉ normalizedSet root P := by
  simpa [normalizedSet, originalRole] using
    (originalRole_mem_occupied root P (Sum.inl i))

theorem terminals_not_normalized
    (root : Fin a → V) (P : IndexedPairs (Fin j) V)
    (i : Fin j) :
    P.start i ∉ normalizedSet root P ∧
      P.finish i ∉ normalizedSet root P := by
  constructor
  · simpa [normalizedSet, originalRole] using
      (originalRole_mem_occupied root P (Sum.inr (Sum.inl i)))
  · simpa [normalizedSet, originalRole] using
      (originalRole_mem_occupied root P (Sum.inr (Sum.inr i)))

/-- Select one distinct proxy in the normalized graph for each original
role occurrence. -/
theorem exists_normalized_proxies
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (root : Fin a → V) (P : IndexedPairs (Fin j) V)
    (hdegree : ∀ i, 2 * (a + 2 * j) ≤ G.degree (originalRoleFin root P i)) :
    ∃ proxy : Fin (a + 2 * j) → normalizedSet root P,
      Function.Injective proxy ∧
      ∀ i, G.Adj (originalRoleFin root P i) (proxy i).1 := by
  classical
  let U := occupiedRoles root P
  obtain ⟨proxy, hinj, hadj, hout⟩ :=
    exists_distinct_neighbor_proxies G (a + 2 * j)
      (originalRoleFin root P) U
      (occupiedRoles_card_le root P) hdegree
  let proxy' : Fin (a + 2 * j) → normalizedSet root P :=
    fun i => ⟨proxy i, hout i⟩
  refine ⟨proxy', ?_, ?_⟩
  · intro i k hik
    exact hinj (congrArg Subtype.val hik)
  · exact hadj

/-- If the normalized graph has a rooted clique model at the selected
proxies, the original arbitrary roles admit a woven solution. Repeated
original roles and singleton terminal pairs are allowed. -/
theorem exists_solution_of_normalized_proxy_minor
    (G : SimpleGraph V)
    (root : Fin a → V) (P : IndexedPairs (Fin j) V)
    (hroot : Function.Injective root)
    (hP : P.DisjointTerminals)
    (proxy : Fin (a + 2 * j) → normalizedSet root P)
    (hadj : ∀ i, G.Adj (originalRoleFin root P i) (proxy i).1)
    (hminor : HasRootedCliqueMinor
      (G.induce (normalizedSet root P)) proxy) :
    Nonempty (WovenSolution G root P) := by
  let f : DistinctRoleIndex a j ↪ Fin (a + 2 * j) :=
    (distinctRoleEquiv a j).toEmbedding
  apply exists_solution_of_normalized_minor proxy f hminor root P hroot
    (root_not_normalized root P) hP
    (terminals_not_normalized root P)
  · intro i
    simpa [f, originalRoleFin, originalRole, selectedRoots] using
      hadj (f (Sum.inl i))
  · intro i
    simpa [f, originalRoleFin, originalRole, selectedPairs] using
      hadj (f (Sum.inr (Sum.inl i)))
  · intro i
    simpa [f, originalRoleFin, originalRole, selectedPairs] using
      (hadj (f (Sum.inr (Sum.inr i)))).symm
end Woven

end HadwigerLean
