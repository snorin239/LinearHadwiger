import HadwigerLean.Inseparability.RawModelCI
import Mathlib.Tactic

/-!
# Attaching each old or child branch to its assigned CI path

The terminal partition gives a specific path for every supplementary
model piece. The prescribed root of that piece is the shared vertex.
-/

namespace HadwigerLean.Inseparability

def ciOldStartIndex (p x : ℕ) (i : Fin p) (r : Fin x) :
    CIPathIndex p x :=
  finProdFinEquiv ((⟨i.val, by omega⟩ : Fin (4 * p + 1)), r)

def ciOldMiddleIndex (p x : ℕ) (i : Fin p) (r : Fin x) :
    CIPathIndex p x :=
  finProdFinEquiv ((⟨p + 2 * i.val, by omega⟩ : Fin (4 * p + 1)), r)

def ciNewMiddleIndex (p x : ℕ) (i : Fin p) (r : Fin x) :
    CIPathIndex p x :=
  finProdFinEquiv ((⟨p + 2 * i.val + 1, by omega⟩ : Fin (4 * p + 1)), r)

theorem ci_extra_piece_meets_assigned_path
    {V : Type*} (p x : ℕ) (G : SimpleGraph V)
    (oldRoot : Fin p × Fin x → V)
    (A : RootedMinorModel
      (SimpleGraph.completeGraph (Fin p × Fin x)) G oldRoot)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (M : ∀ i, RootedMinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G (childRoot i))
    (P : CIPathIndex p x → Set V)
    (hOldPath : ∀ i r,
      oldRoot (i,r) ∈ P (ciOldStartIndex p x i r))
    (hChildOldPath : ∀ i r,
      childRoot i (0,r) ∈ P (ciOldMiddleIndex p x i r))
    (hChildNewPath : ∀ i r,
      childRoot i (1,r) ∈ P (ciNewMiddleIndex p x i r)) :
    ∀ z j, j ∈ ciExtraIndex p x z →
      ∃ k : CIPathIndex p x,
        pathOwner p x k = z ∧
        ∃ v, v ∈ P k ∧
          v ∈ ciExtraPiece p x A.toMinorModel
            (fun i => (M i).toMinorModel) z j := by
  intro z j hj
  cases z with
  | inl z =>
      obtain ⟨i,r⟩ := z
      have hslot : j = none ∨ j = some i := by
        simpa [ciExtraIndex] using hj
      rcases hslot with rfl | rfl
      · refine ⟨ciOldStartIndex p x i r, ?_,
          oldRoot (i,r), hOldPath i r, ?_⟩
        · exact pathOwner_old_start p x i r
        · simpa [ciExtraPiece] using A.root_mem (i,r)
      · refine ⟨ciOldMiddleIndex p x i r, ?_,
          childRoot i (0,r), hChildOldPath i r, ?_⟩
        · exact pathOwner_old_middle p x i r
        · change childRoot i (0,r) ∈
            if i = i then (M i).branch (0,r) else ∅
          rw [if_pos rfl]
          exact (M i).root_mem (0,r)
  | inr r =>
      cases j with
      | none => simp [ciExtraIndex] at hj
      | some i =>
          refine ⟨ciNewMiddleIndex p x i r, ?_,
            childRoot i (1,r), hChildNewPath i r, ?_⟩
          · exact pathOwner_new_middle p x i r
          · exact (M i).root_mem (1,r)

end HadwigerLean.Inseparability
