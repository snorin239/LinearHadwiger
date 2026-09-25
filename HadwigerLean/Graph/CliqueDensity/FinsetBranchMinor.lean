import HadwigerLean.Graph.Minor
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite connected branch sets as a clique minor

This converts an unordered finite family of pairwise disjoint, pairwise
adjacent connected vertex sets into the indexed branch-set model used by
`HasCliqueMinor`.
-/

namespace HadwigerLean

variable {V : Type*} [DecidableEq V]

/-- A finite family of connected, disjoint, mutually adjacent branch
sets forms a clique minor of the same order. -/
theorem hasCliqueMinor_of_finset_branches
    (G : SimpleGraph V) (S : Finset (Finset V)) (r : ℕ)
    (hcard : S.card = r)
    (hconn : ∀ Q ∈ S, (G.induce (Q : Set V)).Connected)
    (hdis : Set.Pairwise (S : Set (Finset V))
      (fun Q T => Disjoint Q T))
    (hadj : Set.Pairwise (S : Set (Finset V))
      (fun Q T => ∃ x ∈ Q, ∃ y ∈ T, G.Adj x y)) :
    HasCliqueMinor G r := by
  classical
  let e : Fin r ≃ S := (S.equivFinOfCardEq hcard).symm
  let M : MinorModel (SimpleGraph.completeGraph (Fin r)) G := {
    branch := fun i => (e i).1
    connected := by
      intro i
      exact hconn (e i).1 (e i).2
    disjoint := by
      intro i j hij
      have hne : (e i).1 ≠ (e j).1 := by
        intro heq
        exact hij (e.injective (Subtype.ext heq))
      simpa only [Finset.disjoint_coe] using hdis (e i).2 (e j).2 hne
    adjacent := by
      intro i j hij
      have hij' : i ≠ j := by simpa using hij
      have hne : (e i).1 ≠ (e j).1 := by
        intro heq
        exact hij' (e.injective (Subtype.ext heq))
      exact hadj (e i).2 (e j).2 hne
  }
  exact ⟨M⟩

end HadwigerLean
