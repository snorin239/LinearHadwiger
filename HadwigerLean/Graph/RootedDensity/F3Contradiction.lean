import HadwigerLean.Graph.RootedDensity.FBEdgeTight
import HadwigerLean.Graph.RootedDensity.FBNonisolated
import HadwigerLean.Graph.RootedDensity.UniversalDichotomy

/-! The F.2–F.3 contradiction for an extremal bad massed pair. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- With at least three roots, the F.b edge estimates, F.3 incidence
identity, and F.2 dense core contradict a nonuniversal extremal pair
having no rigid far shore. -/
theorem no_extremal_bad_massed_of_three_roots
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (c : ℝ) (hc : 1 < c) (hforces : DensityForcesMinor.{u,v} H c)
    (hh : 3 ≤ Fintype.card W)
    (B : BadMassedWitness.{u,v} H
      (12 * c + 5000 * (Fintype.card W : ℝ)))
    (hmin : ∀ B' : BadMassedWitness.{u,v} H
        (12 * c + 5000 * (Fintype.card W : ℝ)),
      B.order ≤ B'.order ∧
        (B.order = B'.order →
          B.outsideIncidence ≤ B'.outsideIncidence))
    (hno : letI : Fintype B.Vertex := B.fintype;
      ∀ T : VertexSeparation B.graph,
        (B.roots : Set B.Vertex) ⊆ T.left →
        ¬ RigidSeparation H T)
    (hX3 : 3 ≤ B.roots.card) : False := by
  classical
  letI : Fintype B.Vertex := B.fintype
  letI : DecidableEq B.Vertex := Classical.decEq _
  letI : DecidableRel B.graph.Adj := Classical.decRel _
  let α : ℝ := 12 * c + 5000 * (Fintype.card W : ℝ)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hXfloor : B.roots.card ≤ Nat.floor α := by
    have hle : (B.roots.card : ℝ) ≤ α := by
      have hroot : (B.roots.card : ℝ) ≤ (Fintype.card W : ℝ) := by
        exact_mod_cast B.root_card
      dsimp [α]
      nlinarith [show (0 : ℝ) ≤ Fintype.card W from Nat.cast_nonneg _]
    exact Nat.le_floor hle
  obtain ⟨x, hx⟩ : B.roots.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨y, hy, hxy⟩ :=
    Linkedness.root_has_outside_neighbor B.graph B.roots α B.massed x hx
  have htight := B.floor_edge_tight H hmin hno hα hXfloor hxy (Or.inr hy)
  obtain ⟨z, hz, hzdeg⟩ :=
    exists_outside_degree_lt_twice_of_massed_floor_tight
      B.graph B.roots α hα hX3 B.massed htight
  have hznot : z ∉ B.roots := by simpa using hz
  have hznbr : ∃ w : B.Vertex, B.graph.Adj z w :=
    B.outside_has_neighbor hmin hα z hznot
  have hzdeg' : ((B.graph.neighborSet z).ncard : ℝ) ≤ 2 * α := by
    have hle : (B.graph.degree z : ℝ) ≤ 2 * α := le_of_lt hzdeg
    simpa only [SimpleGraph.degree, ← Set.ncard_coe_finset,
      SimpleGraph.coe_neighborFinset] using hle
  obtain ⟨J, hJ⟩ :=
    B.exists_ambient_universal_induced_of_low_degree H c hc hforces hh
      hmin hno z hznot hzdeg' hznbr
  rcases universalAt_or_rigid_shore_of_universal_core H B.graph
    B.roots J B.root_card (by omega) hJ with huni | ⟨S, hroot, hfar, hsep, hfarUni⟩
  · exact B.not_universal huni
  · exact hno S hroot ⟨hfar, (Nat.le_of_lt hsep).trans B.root_card, hfarUni⟩

end HadwigerLean.RootedDensity

