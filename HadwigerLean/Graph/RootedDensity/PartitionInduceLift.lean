import HadwigerLean.Graph.RootedMinor
import HadwigerLean.Graph.Linkedness.Massed
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-! Lift rooted models from an induced touching quotient into the
corresponding induced original graph. -/

namespace HadwigerLean.RootedDensity

universe u v w

/-- Inducing a connected graph on a set already contained in a larger
induced vertex set preserves its connectivity. -/
theorem connected_induce_inside_of_subset
    {V : Type v} (G : SimpleGraph V) (T C : Set V)
    (hCT : C ⊆ T) (hC : (G.induce C).Connected) :
    ((G.induce T).induce {x : T | (x : V) ∈ C}).Connected := by
  let f : C → {x : T | (x : V) ∈ C} :=
    fun x => ⟨⟨x, hCT x.property⟩, x.property⟩
  have hfInj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : {x : T | (x : V) ∈ C} => ((z : T) : V)) hxy
  have hfSurj : Function.Surjective f := by
    intro y
    refine ⟨⟨((y : T) : V), y.property⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl
  let e : G.induce C ≃g (G.induce T).induce {x : T | (x : V) ∈ C} := {
    toEquiv := Equiv.ofBijective f ⟨hfInj, hfSurj⟩
    map_rel_iff' := by intro x y; rfl
  }
  exact hC.map e.toHom e.surjective

/-- Every quotient block over `S` is connected inside the induced
preimage of `S`. -/
theorem connected_partition_block_inside
    {V : Type v} [Fintype V] [DecidableEq V] {I : Type u} {G : SimpleGraph V}
    (P : ConnectedPartition G I) (S : Set I) (i : S) :
    let T := Linkedness.partitionIndex P ⁻¹' S
    ((G.induce T).induce
      {x : T | (x : V) ∈ P.block (i : I)}).Connected := by
  dsimp
  have hsub : P.block (i : I) ⊆ Linkedness.partitionIndex P ⁻¹' S := by
    intro x hx
    change Linkedness.partitionIndex P x ∈ S
    rw [Linkedness.partitionIndex_eq_of_mem P x i hx]
    exact i.property
  exact connected_induce_inside_of_subset G _ _ hsub (P.connected i)

/-- The original graph induced on a quotient shore contains the quotient
induced graph as a minor, with each quotient vertex represented by its
partition block inside that shore. -/
def partitionInduceMinorModel
    {V : Type v} [Fintype V] [DecidableEq V] {I : Type u} {G : SimpleGraph V}
    (P : ConnectedPartition G I) (S : Set I) :
    let T := Linkedness.partitionIndex P ⁻¹' S
    MinorModel (P.touchingQuotient.induce S) (G.induce T) := by
  intro T
  refine {
    branch := fun i => {x : T | (x : V) ∈ P.block (i : I)}
    connected := ?_
    disjoint := ?_
    adjacent := ?_
  }
  · intro i
    exact connected_partition_block_inside P S i
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hneq : (i : I) ≠ (j : I) := fun heq => hij (Subtype.ext heq)
    exact (Set.disjoint_left.mp (P.disjoint hneq)) hxi hxj
  · intro i j hij
    obtain ⟨hne, x, hxi, y, hyj, hxy⟩ := hij
    have hxT : x ∈ T := by
      change Linkedness.partitionIndex P x ∈ S
      rw [Linkedness.partitionIndex_eq_of_mem P x i hxi]
      exact i.property
    have hyT : y ∈ T := by
      change Linkedness.partitionIndex P y ∈ S
      rw [Linkedness.partitionIndex_eq_of_mem P y j hyj]
      exact j.property
    exact ⟨⟨x, hxT⟩, hxi, ⟨y, hyT⟩, hyj, hxy⟩

/-- A rooted model in an induced touching quotient lifts to the induced
preimage shore, retaining each chosen original root in its quotient block. -/
def rootedMinor_liftPartitionInduce
    {W : Type w} {V : Type v} [Fintype V] [DecidableEq V] {I : Type u}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (P : ConnectedPartition G I) (S : Set I)
    (r : W → S)
    (M : RootedMinorModel H (P.touchingQuotient.induce S) r)
    (root : W → (Linkedness.partitionIndex P ⁻¹' S))
    (hroot : ∀ i, (root i : V) ∈ P.block (r i : I)) :
    RootedMinorModel H (G.induce (Linkedness.partitionIndex P ⁻¹' S)) root where
  toMinorModel := M.toMinorModel.comp (partitionInduceMinorModel P S)
  root_mem := by
    intro i
    change ∃ j ∈ M.branch i,
      root i ∈ (partitionInduceMinorModel P S).branch j
    exact ⟨r i, M.root_mem i, hroot i⟩

end HadwigerLean.RootedDensity

