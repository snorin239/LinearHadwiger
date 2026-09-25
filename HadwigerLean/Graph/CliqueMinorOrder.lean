import HadwigerLean.Graph.Minor
import Mathlib.Tactic

/-!
# Decreasing the order of a complete minor
-/

namespace HadwigerLean

/-- A complete minor of order `n` contains one of every smaller order. -/
theorem hasCliqueMinor_of_le
    {V : Type*} {G : SimpleGraph V} {m n : ℕ}
    (h : HasCliqueMinor G n) (hm : m ≤ n) :
    HasCliqueMinor G m := by
  obtain ⟨M⟩ := h
  let f : Fin m ↪ Fin n := Fin.castLEEmb hm
  exact ⟨{
    branch := fun i => M.branch (f i)
    connected := fun i => M.connected (f i)
    disjoint := by
      intro i j hij
      exact M.disjoint (f.injective.ne hij)
    adjacent := by
      intro i j hij
      exact M.adjacent (f.injective.ne hij)
  }⟩

end HadwigerLean
