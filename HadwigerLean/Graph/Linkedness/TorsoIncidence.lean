import HadwigerLean.Graph.Linkedness.Massed

namespace HadwigerLean
namespace Linkedness
variable {V : Type*} [Fintype V] [DecidableEq V]

def torsoIncidentEdges (G : SimpleGraph V) (U : Set V) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ ∃ v ∈ U, v ∈ e}

private theorem edgeIncidenceSetCount_eq_torsoIncidentEdges
    (G : SimpleGraph V) (U : Set V) :
    edgeIncidenceSetCount G U = (torsoIncidentEdges G U).ncard := by
  let e : edgeIncidenceSet G U ≃ torsoIncidentEdges G U := {
    toFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
    invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
  }
  exact Nat.card_congr e

/-- Every edge incident with U either meets F or survives deletion of F-incident edges. -/
theorem incidence_le_far_add_near
    (G : SimpleGraph V) (U F : Set V) :
    edgeIncidenceSetCount G U ≤
      edgeIncidenceSetCount G F +
        edgeIncidenceSetCount
          (G.deleteEdges (torsoIncidentEdges G F)) U := by
  classical
  let H := G.deleteEdges (torsoIncidentEdges G F)
  have hcover : torsoIncidentEdges G U ⊆
      torsoIncidentEdges G F ∪ torsoIncidentEdges H U := by
    intro e he
    by_cases hF : e ∈ torsoIncidentEdges G F
    · exact Or.inl hF
    · right
      refine ⟨?_, he.2⟩
      change e ∈ H.edgeSet
      rw [SimpleGraph.edgeSet_deleteEdges]
      exact ⟨he.1,hF⟩
  rw [edgeIncidenceSetCount_eq_torsoIncidentEdges,
    edgeIncidenceSetCount_eq_torsoIncidentEdges,
    edgeIncidenceSetCount_eq_torsoIncidentEdges]
  exact (Set.ncard_le_ncard hcover).trans
    (Set.ncard_union_le _ _)

/-- Removing all far-shore incident edges leaves a graph supported on the near side. -/
theorem support_delete_far_subset_left
    (G : SimpleGraph V) (S : VertexSeparation G) :
    (G.deleteEdges (torsoIncidentEdges G S.strictRight)).support ⊆ S.left := by
  intro x hx
  obtain ⟨y,hxy⟩ := (G.deleteEdges (torsoIncidentEdges G S.strictRight)).mem_support.mp hx
  have hxy' := (SimpleGraph.deleteEdges_adj.mp hxy)
  by_contra hxNotL
  have hxR : x ∈ S.right := by
    have hc : x ∈ S.left ∪ S.right := by rw [S.cover]; trivial
    exact hc.resolve_left hxNotL
  have hxe : s(x,y) ∈ torsoIncidentEdges G S.strictRight := by
    refine ⟨G.mem_edgeSet.mpr hxy'.1, ?_⟩
    exact ⟨x, ⟨hxR,hxNotL⟩, by simp⟩
  exact hxy'.2 hxe

/-- Deleting far-shore incident edges preserves exactly the induced near-side graph. -/
theorem induce_delete_far_eq
    (G : SimpleGraph V) (S : VertexSeparation G) :
    (G.deleteEdges (torsoIncidentEdges G S.strictRight)).induce S.left =
      G.induce S.left := by
  ext x y
  change (G.deleteEdges (torsoIncidentEdges G S.strictRight)).Adj
      (x : V) (y : V) ↔ G.Adj (x : V) (y : V)
  constructor
  · intro h
    exact (SimpleGraph.deleteEdges_adj.mp h).1
  · intro h
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨h, ?_⟩
    rintro ⟨he, z, hzF, hzMem⟩
    have hz : z = (x : V) ∨ z = (y : V) := by
      simpa using hzMem
    rcases hz with rfl | rfl
    · exact hzF.2 x.property
    · exact hzF.2 y.property

/-- Incidence surviving far-edge deletion is exactly incidence in the induced near side. -/
theorem incidence_delete_far_eq_induce_left
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : VertexSeparation G) (R : Set V) :
    edgeIncidenceSetCount
      (G.deleteEdges (torsoIncidentEdges G S.strictRight)) Rᶜ =
    edgeIncidenceSetCount (G.induce S.left)
      {u : S.left | (u : V) ∉ R} := by
  classical
  let H := G.deleteEdges (torsoIncidentEdges G S.strictRight)
  let U : Set S.left := {u | (u : V) ∉ R}
  have hImg : Subtype.val '' U = Rᶜ ∩ S.left := by
    ext v
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨hu,u.property⟩
    · rintro ⟨hvR,hvL⟩
      exact ⟨⟨v,hvL⟩,hvR,rfl⟩
  have hSupport : H.support ⊆ S.left :=
    support_delete_far_subset_left G S
  letI : Fintype S.left := Fintype.ofFinite S.left
  have hinc := incidenceSetCount_induce_eq_of_support_subset
    H S.left hSupport U
  rw [induce_delete_far_eq G S, hImg] at hinc
  have hinter := incidence_inter_support_subset H S.left hSupport Rᶜ
  exact hinter.symm.trans hinc.symm

/-- The exact incidence decomposition needed for D.1. -/
theorem incidence_near_far_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : VertexSeparation G) (R : Set V) :
    edgeIncidenceSetCount G Rᶜ ≤
      edgeIncidenceSetCount G S.strictRight +
        edgeIncidenceSetCount (G.induce S.left)
          {u : S.left | (u : V) ∉ R} := by
  have h := incidence_le_far_add_near G Rᶜ S.strictRight
  rw [incidence_delete_far_eq_induce_left G S R] at h
  exact h

/-- The exterior root count splits into the far shore and the near-side exterior. -/
theorem outside_card_near_add_far
    {G : SimpleGraph V} (R : Set V) (S : VertexSeparation G)
    (hroot : R ⊆ S.left) :
    Nat.card {v : V // v ∉ R} =
      Nat.card {u : S.left // (u : V) ∉ R} +
        Nat.card S.strictRight := by
  classical
  let U : Set S.left := {u | (u : V) ∉ R}
  have hImg : Subtype.val '' U = S.left ∩ Rᶜ := by
    ext v
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u.property,hu⟩
    · rintro ⟨hvL,hvR⟩
      exact ⟨⟨v,hvL⟩,hvR,rfl⟩
  have hUcard : U.ncard = (S.left ∩ Rᶜ).ncard := by
    rw [← hImg, Set.ncard_image_of_injective _ Subtype.val_injective]
  have hdecomp : Rᶜ = S.strictRight ∪ (S.left ∩ Rᶜ) := by
    ext v
    constructor
    · intro hv
      have hc : v ∈ S.left ∪ S.right := by rw [S.cover]; trivial
      rcases hc with hvL | hvR
      · exact Or.inr ⟨hvL,hv⟩
      · by_cases hvL : v ∈ S.left
        · exact Or.inr ⟨hvL,hv⟩
        · exact Or.inl ⟨hvR,hvL⟩
    · rintro (hv | hv)
      · exact fun hR => hv.2 (hroot hR)
      · exact hv.2
  have hdis : Disjoint S.strictRight (S.left ∩ Rᶜ) := by
    apply Set.disjoint_left.mpr
    intro v hvF hvN
    exact hvF.2 hvN.1
  change (Rᶜ).ncard = U.ncard + S.strictRight.ncard
  rw [hdecomp, Set.ncard_union_eq hdis, hUcard]
  omega

/-- D.1: removing a sparse far shore leaves strict global mass on the induced near side. -/
theorem dense_induced_near_of_massed
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Set V) (α : ℝ) (hm : MassedPair G R α)
    (S : VertexSeparation G)
    (hroot : R ⊆ S.left)
    (hsep : Nat.card S.separator < Nat.card R) :
    α * (Nat.card {u : S.left // (u : V) ∉ R} : ℝ) <
      (edgeIncidenceSetCount (G.induce S.left)
        {u : S.left | (u : V) ∉ R} : ℝ) := by
  have hcard := outside_card_near_add_far R S hroot
  have hinc := incidence_near_far_bound G S R
  have hshore := hm.shore S hroot hsep
  have hglobal := hm.global
  rw [hcard] at hglobal
  have hincR : (edgeIncidenceSetCount G Rᶜ : ℝ) ≤
      (edgeIncidenceSetCount G S.strictRight : ℝ) +
        (edgeIncidenceSetCount (G.induce S.left)
          {u : S.left | (u : V) ∉ R} : ℝ) := by
    exact_mod_cast hinc
  push_cast at hglobal
  nlinarith

/-- Near-side torso: add all clique edges among the adhesion vertices. -/
def torsoGraph (G : SimpleGraph V) (S : VertexSeparation G) :
    SimpleGraph S.left where
  Adj u v := G.Adj (u : V) (v : V) ∨
    ((u : V) ∈ S.right ∧ (v : V) ∈ S.right ∧ u ≠ v)
  symm := by
    constructor
    intro u v h
    rcases h with h | ⟨hu,hv,huv⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hv,hu,huv.symm⟩
  loopless := by
    constructor
    intro u h
    rcases h with h | h
    · exact G.irrefl h
    · exact h.2.2 rfl

/-- The induced near side is a subgraph of its torso. -/
theorem induce_le_torso
    (G : SimpleGraph V) (S : VertexSeparation G) :
    G.induce S.left ≤ torsoGraph G S := by
  intro u v h
  exact Or.inl h

/-- Every adhesion vertex pair is adjacent in the torso. -/
theorem torso_boundary_clique
    (G : SimpleGraph V) (S : VertexSeparation G) :
    ({u : S.left | (u : V) ∈ S.right} : Set S.left).Pairwise
      (torsoGraph G S).Adj := by
  intro u hu v hv huv
  exact Or.inr ⟨hu,hv,huv⟩

/-- D.1 for the completed near-side torso. -/
theorem torso_global_of_massed
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Set V) (α : ℝ) (hm : MassedPair G R α)
    (S : VertexSeparation G)
    (hroot : R ⊆ S.left)
    (hsep : Nat.card S.separator < Nat.card R) :
    α * (Nat.card {u : S.left // (u : V) ∉ R} : ℝ) <
      (edgeIncidenceSetCount (torsoGraph G S)
        {u : S.left | (u : V) ∉ R} : ℝ) := by
  classical
  letI : Fintype S.left := Fintype.ofFinite S.left
  have hnear := dense_induced_near_of_massed G R α hm S hroot hsep
  have hmono := edgeIncidenceSetCount_mono (induce_le_torso G S)
    {u : S.left | (u : V) ∉ R}
  have hmonoR :
      (edgeIncidenceSetCount (G.induce S.left)
        {u : S.left | (u : V) ∉ R} : ℝ) ≤
      (edgeIncidenceSetCount (torsoGraph G S)
        {u : S.left | (u : V) ∉ R} : ℝ) := by
    exact_mod_cast hmono
  exact hnear.trans_le hmonoR

/-- Artificial torso edges have no effect on incidence away from the adhesion. -/
theorem torso_incidence_eq_induce_near
    (G : SimpleGraph V) (S : VertexSeparation G)
    (U : Set S.left)
    (hU : ∀ u ∈ U, (u : V) ∉ S.right) :
    edgeIncidenceSetCount (torsoGraph G S) U =
      edgeIncidenceSetCount (G.induce S.left) U := by
  classical
  letI : Fintype S.left := Fintype.ofFinite S.left
  apply incidence_eq_of_agree_on_incident_edges U (induce_le_torso G S)
  intro e he hmeet
  induction e using Sym2.ind with | h x y =>
    have hxy : (torsoGraph G S).Adj x y :=
      (torsoGraph G S).mem_edgeSet.mp he
    rcases hxy with hG | ⟨hxR,hyR,hne⟩
    · exact (G.induce S.left).mem_edgeSet.mpr hG
    · obtain ⟨w,hwU,hwMem⟩ := hmeet
      have hw : w = x ∨ w = y := by simpa using hwMem
      rcases hw with rfl | rfl
      · exact False.elim ((hU w hwU) hxR)
      · exact False.elim ((hU w hwU) hyR)


/-- Reversing a separation exchanges near and far sides. -/
def swapSeparation {G : SimpleGraph V} (S : VertexSeparation G) :
    VertexSeparation G where
  left := S.right
  right := S.left
  cover := by simpa only [Set.union_comm] using S.cover
  no_cross := by
    intro x y hxR hxNotL hyL hyNotR hxy
    exact (S.no_cross hyL hyNotR hxR hxNotL) hxy.symm

/-- Torso incidence away from the adhesion equals ambient graph incidence. -/
theorem torso_incidence_eq_ambient_far
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : VertexSeparation G) (U : Set S.left)
    (hU : ∀ u ∈ U, (u : V) ∉ S.right) :
    edgeIncidenceSetCount (torsoGraph G S) U =
      edgeIncidenceSetCount G (Subtype.val '' U) := by
  classical
  letI : Fintype S.left := Fintype.ofFinite S.left
  rw [torso_incidence_eq_induce_near G S U hU]
  exact incidenceSetCount_induce_right G (swapSeparation S) U hU


/-- A separation of the torso is also a separation of the induced near side. -/
def torsoSeparationInduced
    {G : SimpleGraph V} (S : VertexSeparation G)
    (T : VertexSeparation (torsoGraph G S)) :
    VertexSeparation (G.induce S.left) where
  left := T.left
  right := T.right
  cover := T.cover
  no_cross := by
    intro x y hxL hxNR hyR hyNL hxy
    exact T.no_cross hxL hxNR hyR hyNL ((induce_le_torso G S) hxy)

/-- Glue a torso separation to the original graph through the original far side. -/
def glueTorsoLeft
    {G : SimpleGraph V} (S : VertexSeparation G)
    (T : VertexSeparation (torsoGraph G S))
    (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.left) :
    VertexSeparation G :=
  glueRightInduced (swapSeparation S) (torsoSeparationInduced S T)
    hBoundary

/-- Gluing a torso separation preserves its adhesion order. -/
theorem glueTorsoLeft_separator_card
    {G : SimpleGraph V} (S : VertexSeparation G)
    (T : VertexSeparation (torsoGraph G S))
    (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.left) :
    Nat.card (glueTorsoLeft S T hBoundary).separator =
      Nat.card T.separator := by
  exact glueRightInduced_separator_card (swapSeparation S)
    (torsoSeparationInduced S T) hBoundary

/-- The glued far shore is the torso far shore viewed in the original vertex type. -/
theorem glueTorsoLeft_strictRight
    {G : SimpleGraph V} (S : VertexSeparation G)
    (T : VertexSeparation (torsoGraph G S))
    (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.left) :
    (glueTorsoLeft S T hBoundary).strictRight =
      Subtype.val '' T.strictRight := by
  exact glueRightInduced_strictRight (swapSeparation S)
    (torsoSeparationInduced S T) hBoundary

/-- Root cardinality is unchanged when roots are placed in the induced near-side type. -/
theorem lifted_roots_card
    {G : SimpleGraph V} (R : Set V) (S : VertexSeparation G)
    (hroot : R ⊆ S.left) :
    Nat.card {u : S.left | (u : V) ∈ R} = Nat.card R := by
  let Y : Set S.left := {u | (u : V) ∈ R}
  have hImg : Subtype.val '' Y = R := by
    ext x
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact hu
    · intro hx
      exact ⟨⟨x,hroot hx⟩,hx,rfl⟩
  change Y.ncard = R.ncard
  rw [← hImg, Set.ncard_image_of_injective _ Subtype.val_injective]

/-- A dense torso shore cannot put the completed adhesion on its near side. -/
theorem no_dense_torso_shore_of_boundary_near
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Set V) (α : ℝ)
    (hm : MassedPair G R α)
    (S : VertexSeparation G) (hrootS : R ⊆ S.left)
    (T : VertexSeparation (torsoGraph G S))
    (hrootT : {u : S.left | (u : V) ∈ R} ⊆ T.left)
    (hsmallT : Nat.card T.separator <
      Nat.card {u : S.left | (u : V) ∈ R})
    (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.left)
    (hdense : α * (Nat.card T.strictRight : ℝ) <
      (edgeIncidenceSetCount (torsoGraph G S) T.strictRight : ℝ)) :
    False := by
  classical
  let Q := glueTorsoLeft S T hBoundary
  have hrootQ : R ⊆ Q.left := by
    intro x hx
    exact Or.inr ⟨⟨x,hrootS hx⟩,hrootT hx,rfl⟩
  have hsmallQ : Nat.card Q.separator < Nat.card R := by
    rw [glueTorsoLeft_separator_card S T hBoundary]
    rw [lifted_roots_card R S hrootS] at hsmallT
    exact hsmallT
  have hfarAvoid : ∀ u ∈ T.strictRight, (u : V) ∉ S.right := by
    intro u hu huR
    exact hu.2 (hBoundary u huR)
  have hinc := torso_incidence_eq_ambient_far G S T.strictRight hfarAvoid
  have hcard : Nat.card (Subtype.val '' T.strictRight) =
      Nat.card T.strictRight := by
    simp only [Nat.card_coe_set_eq]
    rw [Set.ncard_image_of_injective _ Subtype.val_injective]
  have hbound := hm.shore Q hrootQ hsmallQ
  rw [glueTorsoLeft_strictRight S T hBoundary, hcard,
    ← hinc] at hbound
  exact (not_lt_of_ge hbound) hdense


/-- Every dense torso shore of order below the root set contains the whole adhesion on its far side. -/
theorem boundary_far_of_dense_torso_shore
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Set V) (α : ℝ) (hm : MassedPair G R α)
    (S : VertexSeparation G) (hrootS : R ⊆ S.left)
    (T : VertexSeparation (torsoGraph G S))
    (hrootT : {u : S.left | (u : V) ∈ R} ⊆ T.left)
    (hsmallT : Nat.card T.separator <
      Nat.card {u : S.left | (u : V) ∈ R})
    (hdense : α * (Nat.card T.strictRight : ℝ) <
      (edgeIncidenceSetCount (torsoGraph G S) T.strictRight : ℝ)) :
    {u : S.left | (u : V) ∈ S.right} ⊆ T.right := by
  classical
  letI : Fintype S.left := Fintype.ofFinite S.left
  rcases clique_on_one_separation_side
      ({u : S.left | (u : V) ∈ S.right} : Set S.left)
      (torso_boundary_clique G S) T with hnear | hfar
  · have hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.left :=
      fun u hu => hnear hu
    exact False.elim (no_dense_torso_shore_of_boundary_near
      G R α hm S hrootS T hrootT hsmallT hBoundary hdense)
  · exact hfar


/-- Glue a torso separation with its adhesion on the torso far side. -/
def glueTorsoFar {G : SimpleGraph V}
    (S : VertexSeparation G)
    (T : VertexSeparation (torsoGraph G S))
    (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right) :
    VertexSeparation G :=
  swapSeparation (glueRightInduced (swapSeparation S)
    (swapSeparation (torsoSeparationInduced S T)) hBoundary)

theorem glueTorsoFar_left {G : SimpleGraph V}
    (S : VertexSeparation G)
    (T : VertexSeparation (torsoGraph G S))
    (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right) :
    (glueTorsoFar S T hBoundary).left =
      Subtype.val '' T.left := by
  rfl

theorem glueTorsoFar_right {G : SimpleGraph V}
    (S : VertexSeparation G)
    (T : VertexSeparation (torsoGraph G S))
    (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right) :
    (glueTorsoFar S T hBoundary).right =
      S.right ∪ Subtype.val '' T.right := by
  rfl

theorem swapSeparation_separator {G : SimpleGraph V}
    (S : VertexSeparation G) :
    (swapSeparation S).separator = S.separator := by
  ext x
  exact and_comm

theorem glueTorsoFar_separator_card {G : SimpleGraph V}
    (S : VertexSeparation G)
    (T : VertexSeparation (torsoGraph G S))
    (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right) :
    Nat.card (glueTorsoFar S T hBoundary).separator =
      Nat.card T.separator := by
  classical
  letI : Fintype S.left := Fintype.ofFinite S.left
  unfold glueTorsoFar
  rw [swapSeparation_separator,
    glueRightInduced_separator_card]
  rw [swapSeparation_separator]
  rfl

/-- A nonempty torso far shore strictly shrinks the new near side. -/
theorem glueTorsoFar_left_card_lt {G : SimpleGraph V}
    (S : VertexSeparation G)
    (T : VertexSeparation (torsoGraph G S))
    (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right)
    (hfar : T.strictRight.Nonempty) :
    Nat.card (glueTorsoFar S T hBoundary).left <
      Nat.card S.left := by
  classical
  let Q := glueTorsoFar S T hBoundary
  obtain ⟨u,huR,huNotL⟩ := hfar
  have hsub : Q.left ⊆ S.left := by
    rw [glueTorsoFar_left]
    rintro x ⟨w,hw,rfl⟩
    exact w.property
  have hnot : (u : V) ∉ Q.left := by
    rw [glueTorsoFar_left]
    rintro ⟨w,hw,hEq⟩
    have hwu : w = u := Subtype.val_injective hEq
    exact huNotL (hwu ▸ hw)
  have hss : Q.left ⊂ S.left := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨hsub, ?_⟩
    intro heq
    exact hnot (heq.symm ▸ u.property)
  have hc := Set.ncard_lt_ncard hss
  simpa only [Nat.card_coe_set_eq] using hc

/-- The original strict far shore survives far-side torso gluing. -/
theorem glueTorsoFar_strictRight_nonempty {G : SimpleGraph V}
    (S : VertexSeparation G)
    (T : VertexSeparation (torsoGraph G S))
    (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right)
    (hfarS : S.strictRight.Nonempty) :
    (glueTorsoFar S T hBoundary).strictRight.Nonempty := by
  obtain ⟨x,hxR,hxNotL⟩ := hfarS
  refine ⟨x, ?_⟩
  constructor
  · rw [glueTorsoFar_right]
    exact Or.inl hxR
  · rw [glueTorsoFar_left]
    rintro ⟨u,hu,hEq⟩
    exact hxNotL (hEq ▸ u.property)


end Linkedness
end HadwigerLean
