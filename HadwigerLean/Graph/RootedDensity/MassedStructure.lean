import HadwigerLean.Graph.RootedDensity.Reduction
import HadwigerLean.Graph.Linkedness.MinimalCounterexample
import Mathlib.Tactic

/-!
# Extremal structure for Appendix F massed counterexamples

The same dense-shore calculation used for linkedness applies to arbitrary
targets. We expose its massed-pair and smaller-order universality forms.
-/

namespace HadwigerLean.RootedDensity

universe u v

/-- A counterexample to the massed universality principle, packaged with
its finite vertex type so that graph order can be minimized across types. -/
structure BadMassedWitness {W : Type v} [Fintype W]
    (H : SimpleGraph W) (α : ℝ) where
  Vertex : Type u
  fintype : Fintype Vertex
  graph : SimpleGraph Vertex
  roots : Finset Vertex
  root_card : roots.card ≤ Fintype.card W
  massed : MassedPair graph (roots : Set Vertex) α
  not_universal : letI : Fintype Vertex := fintype; ¬ UniversalAt graph H roots

noncomputable def BadMassedWitness.order
    {W : Type v} [Fintype W] {H : SimpleGraph W} {α : ℝ}
    (B : BadMassedWitness.{u,v} H α) : ℕ :=
  @Fintype.card B.Vertex B.fintype

noncomputable def BadMassedWitness.outsideIncidence
    {W : Type v} [Fintype W] {H : SimpleGraph W} {α : ℝ}
    (B : BadMassedWitness.{u,v} H α) : ℕ :=
  edgeIncidenceSetCount B.graph (B.roots : Set B.Vertex)ᶜ

/-- If the massed universality principle fails, choose a counterexample
minimizing first its order and then its outside-root edge incidence. -/
theorem exists_extremal_bad_massed_witness
    {W : Type v} [Fintype W] (H : SimpleGraph W) (α : ℝ)
    (hfail : ¬ MassedUniversalPrinciple.{u,v} H α) :
    ∃ B : BadMassedWitness.{u,v} H α,
      ∀ B' : BadMassedWitness.{u,v} H α,
        B.order ≤ B'.order ∧
          (B.order = B'.order →
            B.outsideIncidence ≤ B'.outsideIncidence) := by
  classical
  have hex : ∃ B : BadMassedWitness.{u,v} H α, True := by
    by_contra hnone
    apply hfail
    intro V inst G X hX hm
    by_contra hbad
    exact hnone ⟨{
      Vertex := V
      fintype := inst
      graph := G
      roots := X
      root_card := hX
      massed := hm
      not_universal := hbad
    }, trivial⟩
  let P : ℕ → Prop := fun n =>
    ∃ B : BadMassedWitness.{u,v} H α, B.order = n
  have hP : ∃ n, P n := by
    obtain ⟨B, _⟩ := hex
    exact ⟨B.order, B, rfl⟩
  let n := Nat.find hP
  have hPn : P n := Nat.find_spec hP
  let Q : ℕ → Prop := fun m =>
    ∃ B : BadMassedWitness.{u,v} H α,
      B.order = n ∧ B.outsideIncidence = m
  have hQ : ∃ m, Q m := by
    obtain ⟨B, hBn⟩ := hPn
    exact ⟨B.outsideIncidence, B, hBn, rfl⟩
  obtain ⟨B, hBn, hBm⟩ := Nat.find_spec hQ
  refine ⟨B, ?_⟩
  intro B'
  constructor
  · have hmin := Nat.find_min' hP
      (show P B'.order from ⟨B', rfl⟩)
    simpa only [hBn] using hmin
  · intro heq
    have hB'n : B'.order = n := heq.symm.trans hBn
    have hmin := Nat.find_min' hQ
      (show Q B'.outsideIncidence from ⟨B', hB'n, rfl⟩)
    simpa only [hBm] using hmin


/-- The extremal choice makes every smaller massed pair universal. -/
theorem BadMassedWitness.universal_of_smaller_order
    {W : Type v} [Fintype W] {H : SimpleGraph W} {α : ℝ}
    (B : BadMassedWitness.{u,v} H α)
    (hmin : ∀ B' : BadMassedWitness.{u,v} H α,
      B.order ≤ B'.order ∧
        (B.order = B'.order →
          B.outsideIncidence ≤ B'.outsideIncidence))
    {U : Type u} [Fintype U] (J : SimpleGraph U) (Y : Finset U)
    (horder : Fintype.card U < B.order)
    (hY : Y.card ≤ Fintype.card W)
    (hm : MassedPair J (Y : Set U) α) :
    UniversalAt J H Y := by
  classical
  by_contra hnot
  let B' : BadMassedWitness.{u,v} H α := {
    Vertex := U
    fintype := inferInstance
    graph := J
    roots := Y
    root_card := hY
    massed := hm
    not_universal := hnot
  }
  have hle := (hmin B').1
  change B.order ≤ Fintype.card U at hle
  omega

/-- At the extremal order, a smaller outside-edge incidence also forces
universality. -/
theorem BadMassedWitness.universal_of_lower_incidence
    {W : Type v} [Fintype W] {H : SimpleGraph W} {α : ℝ}
    (B : BadMassedWitness.{u,v} H α)
    (hmin : ∀ B' : BadMassedWitness.{u,v} H α,
      B.order ≤ B'.order ∧
        (B.order = B'.order →
          B.outsideIncidence ≤ B'.outsideIncidence))
    (J : SimpleGraph B.Vertex) (Y : Finset B.Vertex)
    (hY : Y.card ≤ Fintype.card W)
    (hm : MassedPair J (Y : Set B.Vertex) α)
    (hinc : edgeIncidenceSetCount J (Y : Set B.Vertex)ᶜ <
      B.outsideIncidence) :
    (letI : Fintype B.Vertex := B.fintype; UniversalAt J H Y) := by
  classical
  letI : Fintype B.Vertex := B.fintype
  by_contra hnot
  let B' : BadMassedWitness.{u,v} H α := {
    Vertex := B.Vertex
    fintype := B.fintype
    graph := J
    roots := Y
    root_card := hY
    massed := hm
    not_universal := hnot
  }
  have hle := (hmin B').2 (by rfl)
  change B.outsideIncidence ≤
    edgeIncidenceSetCount J (Y : Set B.Vertex)ᶜ at hle
  omega

/-- A minimal dense F.2 violation exposes an induced massed far shore
of strictly smaller graph order. This is the Appendix F.1 observation. -/
theorem exists_massed_dense_shore_of_violation
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Set V) (α : ℝ)
    (hex : ∃ S : VertexSeparation G,
      R ⊆ S.left ∧ Nat.card S.separator < Nat.card R ∧
      α * (Nat.card S.strictRight : ℝ) <
        (edgeIncidenceSetCount G S.strictRight : ℝ)) :
    ∃ S : VertexSeparation G,
      R ⊆ S.left ∧ Nat.card S.separator < Nat.card R ∧
      α * (Nat.card S.strictRight : ℝ) <
        (edgeIncidenceSetCount G S.strictRight : ℝ) ∧
      MassedPair (G.induce S.right)
        {x : S.right | (x : V) ∈ S.left} α ∧
      Nat.card S.right < Fintype.card V := by
  classical
  obtain ⟨S, hroot, hsep, hdense, hmin⟩ :=
    Linkedness.exists_minimal_violating_shore G R α hex
  letI : Fintype S.right := Fintype.ofFinite S.right
  have hm : MassedPair (G.induce S.right)
      {x : S.right | (x : V) ∈ S.left} α :=
    Linkedness.massed_far_shore_of_minimal_violation G R α
      S hroot hsep hdense hmin
  exact ⟨S, hroot, hsep, hdense, hm,
    Linkedness.right_card_lt_of_root_sep R S hroot hsep⟩

/-- Universality of an induced right shore, rooted at its adhesion. -/
noncomputable def UniversalAtRightShore
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {G : SimpleGraph V} (H : SimpleGraph W)
    (S : VertexSeparation G) : Prop := by
  letI : Fintype S.right := Fintype.ofFinite S.right
  exact UniversalAt (G.induce S.right) H
    (Linkedness.separationBoundaryFinset S)

/-- In a graph-order extremal counterexample, every minimal dense
violation of the shore condition is universal at its adhesion. -/
theorem BadMassedWitness.exists_universal_dense_shore
    {W : Type v} [Fintype W] {H : SimpleGraph W} {α : ℝ}
    (B : BadMassedWitness.{u,v} H α)
    (hmin : ∀ B' : BadMassedWitness.{u,v} H α,
      B.order ≤ B'.order ∧
        (B.order = B'.order →
          B.outsideIncidence ≤ B'.outsideIncidence))
    (hex : letI : Fintype B.Vertex := B.fintype;
      ∃ S : VertexSeparation B.graph,
        (B.roots : Set B.Vertex) ⊆ S.left ∧
        Nat.card S.separator < B.roots.card ∧
        α * (Nat.card S.strictRight : ℝ) <
          (edgeIncidenceSetCount B.graph S.strictRight : ℝ)) :
    (letI : Fintype B.Vertex := B.fintype;
     ∃ S : VertexSeparation B.graph,
      (B.roots : Set B.Vertex) ⊆ S.left ∧
      Nat.card S.separator < B.roots.card ∧
      α * (Nat.card S.strictRight : ℝ) <
        (edgeIncidenceSetCount B.graph S.strictRight : ℝ) ∧
      UniversalAtRightShore H S) := by
  classical
  letI : Fintype B.Vertex := B.fintype
  letI : DecidableEq B.Vertex := Classical.decEq _
  letI : DecidableRel B.graph.Adj := Classical.decRel _
  have hRcard : Nat.card (B.roots : Set B.Vertex) = B.roots.card := by
    simp
  have hex' : ∃ S : VertexSeparation B.graph,
      (B.roots : Set B.Vertex) ⊆ S.left ∧
      Nat.card S.separator < Nat.card (B.roots : Set B.Vertex) ∧
      α * (Nat.card S.strictRight : ℝ) <
        (edgeIncidenceSetCount B.graph S.strictRight : ℝ) := by
    simpa only [hRcard] using hex
  obtain ⟨S, hroot, hsep, hdense, hmS, horder⟩ :=
    exists_massed_dense_shore_of_violation B.graph
      (B.roots : Set B.Vertex) α hex'
  letI : Fintype S.right := Fintype.ofFinite S.right
  let Y : Finset S.right := Linkedness.separationBoundaryFinset S
  have hYcard : Y.card ≤ Fintype.card W := by
    have hc : Y.card = Nat.card S.separator :=
      Linkedness.separationBoundaryFinset_card_eq S
    have hsep' : Nat.card S.separator < B.roots.card := by
      simpa only [hRcard] using hsep
    exact (le_of_lt (hc ▸ hsep')).trans B.root_card
  have hmY : MassedPair (B.graph.induce S.right)
      (Y : Set S.right) α := by
    simpa [Y, Linkedness.separationBoundaryFinset] using hmS
  have horder' : Fintype.card S.right < B.order := by
    simpa [BadMassedWitness.order, Nat.card_eq_fintype_card] using horder
  have huni := B.universal_of_smaller_order hmin
    (B.graph.induce S.right) Y horder' hYcard hmY
  refine ⟨S, hroot, ?_, hdense, ?_⟩
  · simpa only [hRcard] using hsep
  · change UniversalAt (B.graph.induce S.right) H Y
    exact huni

/-- An arbitrary-target rigid separation: the proper far shore is
universal at its adhesion. -/
def RigidSeparation
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {G : SimpleGraph V} (H : SimpleGraph W)
    (S : VertexSeparation G) : Prop :=
  S.strictRight.Nonempty ∧ Nat.card S.separator ≤ Fintype.card W ∧
    UniversalAtRightShore H S

/-- The extremal dense-shore lemma produces an H-rigid separation. -/
theorem BadMassedWitness.exists_rigid_of_shore_violation
    {W : Type v} [Fintype W] {H : SimpleGraph W} {α : ℝ}
    (B : BadMassedWitness.{u,v} H α)
    (hmin : ∀ B' : BadMassedWitness.{u,v} H α,
      B.order ≤ B'.order ∧
        (B.order = B'.order →
          B.outsideIncidence ≤ B'.outsideIncidence))
    (hex : letI : Fintype B.Vertex := B.fintype;
      ∃ S : VertexSeparation B.graph,
        (B.roots : Set B.Vertex) ⊆ S.left ∧
        Nat.card S.separator < B.roots.card ∧
        α * (Nat.card S.strictRight : ℝ) <
          (edgeIncidenceSetCount B.graph S.strictRight : ℝ)) :
    (letI : Fintype B.Vertex := B.fintype;
      ∃ S : VertexSeparation B.graph,
        (B.roots : Set B.Vertex) ⊆ S.left ∧
        Nat.card S.separator < B.roots.card ∧
        RigidSeparation H S) := by
  classical
  letI : Fintype B.Vertex := B.fintype
  obtain ⟨S, hroot, hsep, hdense, huni⟩ :=
    B.exists_universal_dense_shore hmin hex
  have hfar : S.strictRight.Nonempty := by
    by_contra hnot
    have hempty : S.strictRight = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hnot
    rw [hempty] at hdense
    simp [edgeIncidenceSetCount, edgeIncidenceSet] at hdense
  have hseph : Nat.card S.separator ≤ Fintype.card W := by
    have hrootcard := B.root_card
    omega
  exact ⟨S, hroot, hsep, hfar, hseph, huni⟩
end HadwigerLean.RootedDensity