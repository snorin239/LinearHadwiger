import HadwigerLean.Woven.ThreeChildGNIso
import HadwigerLean.Woven.OuterChromaticSeparation
import HadwigerLean.Graph.ChromaticConnectivity.Theorem

/-!
# GN extraction inside an induced child

GN returns a vertex set in the type of the current induced graph. We map
that set back to the ambient vertex type, preserving its chromatic lower
bound, connectivity, and the induced graph's woven property.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ambient image of a finite subset of an induced graph. -/
def nestedImageFinset (J : Finset V)
    (W : Finset (↥(J : Set V))) : Finset V :=
  W.image Subtype.val

@[simp] theorem nestedImageFinset_coe (J : Finset V)
    (W : Finset (↥(J : Set V))) :
    (nestedImageFinset J W : Set V) =
      Subtype.val '' (W : Set (↥(J : Set V))) := by
  ext x
  simp [nestedImageFinset]

theorem nestedImageFinset_subset (J : Finset V)
    (W : Finset (↥(J : Set V))) :
    nestedImageFinset J W ⊆ J := by
  intro x hx
  obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hx
  exact y.property

/-- The nested and ambient induced graphs are naturally isomorphic. -/
noncomputable def nestedInducedIso (G : SimpleGraph V) (J : Finset V)
    (W : Finset (↥(J : Set V))) :
    ((G.induce (J : Set V)).induce (W : Set (↥(J : Set V)))) ≃g
      G.induce (nestedImageFinset J W : Set V) := by
  classical
  rw [nestedImageFinset_coe]
  exact {
    toEquiv := Equiv.Set.image (fun r : (J : Set V) => (r : V))
      (W : Set (↥(J : Set V))) Subtype.val_injective
    map_rel_iff' := by
      intro x y
      rfl
  }

/-- Transfer GN extraction from an induced child back to the ambient
vertex type. -/
theorem exists_chromatic_connected_inside
    (G : SimpleGraph V) (J : Finset V)
    (k : ℕ) (hk : 0 < k)
    (hχ : 7 * k ≤ chromatic (G.induce (J : Set V))) :
    ∃ H : Finset V,
      H ⊆ J ∧
      VertexConnected (G.induce (H : Set V)) k ∧
      chromatic (G.induce (J : Set V)) ≤
        chromatic (G.induce (H : Set V)) + 6 * k := by
  classical
  obtain ⟨W,hconn,hchrom⟩ :=
    exists_chromatic_connected_induced (G.induce (J : Set V))
      k hk hχ
  let H := nestedImageFinset J W
  have hconnH : VertexConnected (G.induce (H : Set V)) k :=
    VertexConnected.of_iso (nestedInducedIso G J W) k hconn
  have hchromH : chromatic ((G.induce (J : Set V)).induce
      (W : Set (↥(J : Set V)))) =
      chromatic (G.induce (H : Set V)) := by
    change chromatic ((G.induce (J : Set V)).induce
      (W : Set (↥(J : Set V)))) =
      chromatic (G.induce (nestedImageFinset J W : Set V))
    rw [nestedImageFinset_coe]
    exact
      chromatic_nested_image G (J : Set V)
        (W : Set (↥(J : Set V)))
  refine ⟨H, nestedImageFinset_subset J W, hconnH, ?_⟩
  rw [← hchromH]
  exact hchrom

/-- Wovenness of a GN-selected nested child is equivalent to wovenness of
its ambient induced representation. -/
theorem woven_nested_to_ambient
    (G : SimpleGraph V) (J : Finset V)
    (W : Finset (↥(J : Set V))) {a b : ℕ}
    (hW : Woven ((G.induce (J : Set V)).induce
      (W : Set (↥(J : Set V)))) a b) :
    Woven (G.induce (nestedImageFinset J W : Set V)) a b :=
  Woven.of_iso (nestedInducedIso G J W) hW

end Woven
end HadwigerLean
