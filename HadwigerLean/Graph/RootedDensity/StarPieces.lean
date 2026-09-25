import HadwigerLean.Graph.RootedDensity.StarForest
import Mathlib.Tactic

/-!
# Connectivity of star-decomposition pieces

The components left after deleting the prescribed adhesion star are
connected in the real graph. Any nonempty union of such components is
connected in the torso, since their adhesion vertices form a clique.
The latter observation lets one remove an arbitrary hanging component
while retaining the component containing the root.
-/

namespace HadwigerLean.RootedDensity

universe u

def starPiece {V : Type u} (F : SimpleGraph V) (z : V) : Set V :=
  (F.connectedComponentMk z).supp

theorem mem_starPiece_iff
    {V : Type u} (F : SimpleGraph V) (v z : V) :
    v ∈ starPiece F z ↔ F.Reachable v z := by
  rw [starPiece, SimpleGraph.ConnectedComponent.mem_supp_iff,
    SimpleGraph.ConnectedComponent.eq]

theorem starPiece_self {V : Type u} (F : SimpleGraph V) (z : V) :
    z ∈ starPiece F z :=
  (mem_starPiece_iff F z z).2 (.refl z)

theorem starPiece_connected
    {V : Type u} (K F : SimpleGraph V) (hFK : F ≤ K)
    (z : V) :
    (K.induce (starPiece F z)).Connected := by
  have hF : (F.induce (starPiece F z)).Connected :=
    (F.connectedComponentMk z).connected_toSimpleGraph
  exact hF.mono (fun _ _ h => hFK h)

theorem starPiece_boundary_unique
    {V : Type u} (F : SimpleGraph V) (Z : Set V)
    (hUnique : ∀ v, ∃! z, z ∈ Z ∧ F.Reachable v z)
    {z w : V} (hz : z ∈ Z) (hw : w ∈ Z)
    (hwp : w ∈ starPiece F z) : w = z := by
  obtain ⟨a,ha,honly⟩ := hUnique w
  have hwa : w = a := honly w ⟨hw,SimpleGraph.Reachable.refl w⟩
  have hza : z = a := honly z ⟨hz,(mem_starPiece_iff F w z).1 hwp⟩
  exact hwa.trans hza.symm

theorem starPiece_pairwise_disjoint
    {V : Type u} (F : SimpleGraph V) (Z : Set V)
    (hUnique : ∀ v, ∃! z, z ∈ Z ∧ F.Reachable v z)
    {z w : V} (hz : z ∈ Z) (hw : w ∈ Z) (hzw : z ≠ w) :
    Disjoint (starPiece F z) (starPiece F w) := by
  refine Set.disjoint_left.mpr ?_
  intro v hvz hvw
  obtain ⟨a,ha,honly⟩ := hUnique v
  have hza : z = a :=
    honly z ⟨hz,(mem_starPiece_iff F v z).1 hvz⟩
  have hwa : w = a :=
    honly w ⟨hw,(mem_starPiece_iff F v w).1 hvw⟩
  exact hzw (hza.trans hwa.symm)

theorem starPiece_cover
    {V : Type u} (F : SimpleGraph V) (Z : Set V)
    (hUnique : ∀ v, ∃! z, z ∈ Z ∧ F.Reachable v z) :
    ∀ v, ∃ z ∈ Z, v ∈ starPiece F z := by
  intro v
  obtain ⟨z,⟨hz,hvz⟩,_⟩ := hUnique v
  exact ⟨z,hz,(mem_starPiece_iff F v z).2 hvz⟩

/-- In a graph containing the forest, a union of forest components
whose distinguished boundary vertices form a clique is connected. -/
theorem starPiece_union_connected
    {V : Type u} (K F : SimpleGraph V) (R : Set V)
    (hFK : F ≤ K)
    (c : V) (hc : c ∈ R)
    (hclique : ∀ z ∈ R, ∀ w ∈ R, z ≠ w → K.Adj z w) :
    (K.induce {v | ∃ z ∈ R, v ∈ starPiece F z}).Connected := by
  let U : Set V := {v | ∃ z ∈ R, v ∈ starPiece F z}
  have hcU : c ∈ U := ⟨c,hc,starPiece_self F c⟩
  apply K.induce_connected_of_patches c hcU
  intro v hv
  obtain ⟨z,hz,hvPiece⟩ := hv
  let C := starPiece F c
  let D := starPiece F z
  by_cases hcz : c = z
  · subst z
    refine ⟨C, ?_, starPiece_self F c, hvPiece, ?_⟩
    · intro w hw
      exact ⟨c,hc,hw⟩
    · exact (starPiece_connected K F hFK c).preconnected _ _
  · refine ⟨C ∪ D, ?_, Or.inl (starPiece_self F c),
      Or.inr hvPiece, ?_⟩
    · intro w hw
      rcases hw with hw | hw
      · exact ⟨c,hc,hw⟩
      · exact ⟨z,hz,hw⟩
    · have hconn := K.connected_induce_union
        (starPiece_connected K F hFK c).preconnected
        (starPiece_connected K F hFK z).preconnected
        (starPiece_self F c) (starPiece_self F z)
        (hclique c hc z hz hcz)
      exact hconn.preconnected _ _

/-- Removing one non-root component preserves torso connectivity. -/
theorem starPiece_delete_connected
    {V : Type u} (K F : SimpleGraph V) (Z : Set V)
    (hFK : F ≤ K)
    (hclique : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → K.Adj z w)
    (center drop : V) (hc : center ∈ Z)
    (hneq : center ≠ drop) :
    (K.induce {v | ∃ z ∈ Z, z ≠ drop ∧
      v ∈ starPiece F z}).Connected := by
  let R : Set V := {z | z ∈ Z ∧ z ≠ drop}
  have hR : center ∈ R := ⟨hc,hneq⟩
  have hcliqueR : ∀ z ∈ R, ∀ w ∈ R, z ≠ w →
      K.Adj z w := by
    intro z hz w hw hzw
    exact hclique z hz.1 w hw.1 hzw
  have hset : {v | ∃ z ∈ R, v ∈ starPiece F z} =
      {v | ∃ z ∈ Z, z ≠ drop ∧ v ∈ starPiece F z} := by
    ext v
    constructor
    · rintro ⟨z,⟨hz,hne⟩,hv⟩
      exact ⟨z,hz,hne,hv⟩
    · rintro ⟨z,hz,hne,hv⟩
      exact ⟨z,⟨hz,hne⟩,hv⟩
  rw [← hset]
  exact starPiece_union_connected K F R hFK center hR hcliqueR


/-- The union of every forest piece except one equals the complement
of that piece when each component has a unique adhesion vertex. -/
theorem starPiece_delete_eq_compl
    {V : Type u} (F : SimpleGraph V) (Z : Set V)
    (hUnique : ∀ v, ∃! z, z ∈ Z ∧ F.Reachable v z)
    (drop : V) (hdrop : drop ∈ Z) :
    {v | ∃ z ∈ Z, z ≠ drop ∧ v ∈ starPiece F z} =
      (starPiece F drop)ᶜ := by
  ext v
  constructor
  · rintro ⟨z,hz,hne,hvz⟩ hvd
    have hzd : z = drop := by
      obtain ⟨a,ha,honly⟩ := hUnique v
      exact (honly z ⟨hz,(mem_starPiece_iff F v z).1 hvz⟩).trans
        (honly drop ⟨hdrop,(mem_starPiece_iff F v drop).1 hvd⟩).symm
    exact hne hzd
  · intro hvd
    obtain ⟨z,hz,hvz⟩ := starPiece_cover F Z hUnique v
    refine ⟨z,hz,?_,hvz⟩
    intro hzd
    exact hvd (hzd ▸ hvz)

/-- The connected complement of one non-root star piece is the
branch left after deleting that hanging piece in the torso. -/
theorem starPiece_complement_connected
    {V : Type u} (K F : SimpleGraph V) (Z : Set V)
    (hFK : F ≤ K)
    (hUnique : ∀ v, ∃! z, z ∈ Z ∧ F.Reachable v z)
    (hclique : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → K.Adj z w)
    (center drop : V) (hc : center ∈ Z) (hd : drop ∈ Z)
    (hneq : center ≠ drop) :
    (K.induce (starPiece F drop)ᶜ).Connected := by
  rw [← starPiece_delete_eq_compl F Z hUnique drop hd]
  exact starPiece_delete_connected K F Z hFK hclique
    center drop hc hneq
end HadwigerLean.RootedDensity
