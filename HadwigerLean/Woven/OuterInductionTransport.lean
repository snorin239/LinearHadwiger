import HadwigerLean.Woven.OuterInduction
import HadwigerLean.Woven.ThreeChildGNIso

/-!
# Heredity of the outer induction claim

The induction predicate is stated for induced subgraphs of one fixed host.
This theorem makes it available again after changing the vertex type to
an induced subset, as required for the nested normalized residual.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def outerNestedIso
    (G : SimpleGraph V) (S : Set V) [Fintype S]
    (F : Finset S) :
    ((G.induce S).induce (F : Set S)) ≃g
      G.induce (F.image Subtype.val : Set V) := by
  classical
  have hset : (F.image Subtype.val : Set V) =
      Subtype.val '' (F : Set S) := by
    ext x
    simp
  rw [hset]
  exact {
    toEquiv := Equiv.Set.image (fun x : S => (x : V))
      (F : Set S) Subtype.val_injective
    map_rel_iff' := by
      intro x y
      rfl
  }

/-- A checked outer-scale induction claim remains valid for every induced
host, with the same scale and thresholds. -/
theorem outerAt_induce
    (G : SimpleGraph V) (m i K U B : ℕ)
    (h : OuterAt G m i K U B)
    (S : Set V) [Fintype S] :
    OuterAt (G.induce S) m i K U B := by
  classical
  intro F hconn hχ
  let T : Finset V := F.image Subtype.val
  let e := outerNestedIso G S F
  have hconnT : VertexConnected (G.induce (T : Set V))
      (K * outerScale m i) :=
    VertexConnected.of_iso e (K * outerScale m i) hconn
  have hχeq :
      chromatic ((G.induce S).induce (F : Set S)) =
        chromatic (G.induce (T : Set V)) := by
    unfold chromatic
    exact congrArg ENat.toNat (SimpleGraph.chromaticNumber_congr e)
  have hχT : U + B * outerScale m i ≤
      chromatic (G.induce (T : Set V)) := by
    rw [← hχeq]
    exact hχ
  exact Woven.of_iso e.symm (h T hconnT hχT)

end Woven
end HadwigerLean
