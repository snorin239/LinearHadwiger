import HadwigerLean.Inseparability.RawModelAttachment
import Mathlib.Tactic

/-!
# Exact tangency of grouped CI paths to the next chromatic region

Each group has one final path starting in H3. If every path meets H3
only at its designated owner's root, their union has exactly one H3
vertex. The terminal-index partition identifies the final path for
each old and new branch.
-/

namespace HadwigerLean.Inseparability

def ciFinalIndex (p x : ℕ) :
    CIRawIndex p x → CIPathIndex p x
  | .inl (i,r) =>
      finProdFinEquiv
        ((⟨3 * p + i.val, by omega⟩ : Fin (4 * p + 1)), r)
  | .inr r =>
      finProdFinEquiv
        ((⟨4 * p, by omega⟩ : Fin (4 * p + 1)), r)

theorem pathOwner_finalIndex (p x : ℕ)
    (z : CIRawIndex p x) :
    pathOwner p x (ciFinalIndex p x z) = z := by
  cases z with
  | inl z =>
      obtain ⟨i,r⟩ := z
      exact pathOwner_old_final p x i r
  | inr r =>
      exact pathOwner_new_final p x r

theorem ci_root_mem_assignedPaths
    {V : Type*} (p x : ℕ)
    (P : CIPathIndex p x → Set V)
    (root : CIRawIndex p x → V)
    (hFinalPath : ∀ z, root z ∈ P (ciFinalIndex p x z)) :
    ∀ z, root z ∈ assignedPaths (pathOwner p x) P z := by
  intro z
  change root z ∈ ⋃ k ∈ Finset.univ.filter
    (fun k => pathOwner p x k = z), P k
  exact Set.mem_iUnion.mpr ⟨ciFinalIndex p x z,
    Set.mem_iUnion.mpr
      ⟨by simp [pathOwner_finalIndex],hFinalPath z⟩⟩

theorem ci_assignedPaths_tangent
    {V : Type*} (p x : ℕ)
    (P : CIPathIndex p x → Set V)
    (root : CIRawIndex p x → V) (H : Set V)
    (hFinalPath : ∀ z, root z ∈ P (ciFinalIndex p x z))
    (hRootH : ∀ z, root z ∈ H)
    (hPathClean : ∀ k v, v ∈ P k → v ∈ H →
      v = root (pathOwner p x k)) :
    ∀ z, assignedPaths (pathOwner p x) P z ∩ H = {root z} := by
  intro z
  apply Set.Subset.antisymm
  · intro v hv
    obtain ⟨k,hk,hvP⟩ : ∃ k, pathOwner p x k = z ∧ v ∈ P k := by
      simpa [assignedPaths] using hv.1
    have heq := hPathClean k v hvP hv.2
    simpa [hk] using heq
  · intro v hv
    have heq : v = root z := by simpa using hv
    subst v
    exact ⟨ci_root_mem_assignedPaths p x P root hFinalPath z,
      hRootH z⟩

end HadwigerLean.Inseparability
