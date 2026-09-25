import HadwigerLean.Graph.Linkedness.TorsoLinkageGlue

/-! The minimal rigid-separation reduction for the near-side torso. -/

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Roots viewed as vertices of the near-side torso. -/
noncomputable def torsoRootFinset {G : SimpleGraph V}
    (S : VertexSeparation G) (X : Finset V) : Finset S.left := by
  classical
  exact Finset.univ.filter (fun u : S.left => (u : V) ∈ X)

@[simp] theorem mem_torsoRootFinset {G : SimpleGraph V}
    (S : VertexSeparation G) (X : Finset V) (u : S.left) :
    u ∈ torsoRootFinset S X ↔ (u : V) ∈ X := by
  simp [torsoRootFinset]

theorem torsoRootFinset_card {G : SimpleGraph V}
    (S : VertexSeparation G) (X : Finset V)
    (hX : (X : Set V) ⊆ S.left) :
    (torsoRootFinset S X).card = X.card := by
  classical
  have hs : ((torsoRootFinset S X : Finset S.left) : Set S.left) =
      {u : S.left | (u : V) ∈ X} := by
    ext u
    simp
  have hc := lifted_roots_card (X : Set V) S hX
  have hc' : Nat.card ((torsoRootFinset S X : Finset S.left) : Set S.left) =
      Nat.card (X : Set V) := by
    rw [hs]
    exact hc
  simpa only [Nat.card_coe_set_eq, Set.ncard_coe_finset] using hc'

/-- A dense violating shore in the torso creates a proper rigid far shore
with a strictly smaller near side. -/
theorem smaller_rigid_of_torso_shore_violation
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (α : ℝ)
    (hm : MassedPair G (X : Set V) α)
    (S : VertexSeparation G)
    [Fintype S.left]
    (hrootS : (X : Set V) ⊆ S.left)
    (hfarS : S.strictRight.Nonempty)
    (hsmall : ∀ T : VertexSeparation (torsoGraph G S),
      Nat.card T.right < Fintype.card S.left →
      Nat.card T.separator < (torsoRootFinset S X).card →
      MassedPair ((torsoGraph G S).induce T.right)
        {u : T.right | (u : S.left) ∈ T.left} α →
      RootedLinked ((torsoGraph G S).induce T.right)
        (separationBoundaryFinset T))
    (hglue : ∀ (T : VertexSeparation (torsoGraph G S))
      (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right),
      RootedLinked ((torsoGraph G S).induce T.right)
        (separationBoundaryFinset T) →
      RootedLinked (G.induce (glueTorsoFar S T hBoundary).right)
        (separationBoundaryFinset (glueTorsoFar S T hBoundary)))
    (hex : ∃ T : VertexSeparation (torsoGraph G S),
      (torsoRootFinset S X : Set S.left) ⊆ T.left ∧
      Nat.card T.separator < (torsoRootFinset S X).card ∧
      α * (Nat.card T.strictRight : ℝ) <
        (edgeIncidenceSetCount (torsoGraph G S) T.strictRight : ℝ)) :
    ∃ Q : VertexSeparation G,
      (X : Set V) ⊆ Q.left ∧ Q.strictRight.Nonempty ∧
      Nat.card Q.separator < X.card ∧
      RootedLinked (G.induce Q.right) (separationBoundaryFinset Q) ∧
      Nat.card Q.left < Nat.card S.left := by
  classical
  letI : DecidableEq S.left := Classical.decEq _
  letI : DecidableRel (torsoGraph G S).Adj := Classical.decRel _
  let Y := torsoRootFinset S X
  have hYcard : Y.card = X.card := torsoRootFinset_card S X hrootS
  have hYset : (Y : Set S.left) = {u : S.left | (u : V) ∈ X} := by
    ext u
    simp [Y]
  have hYnat : Nat.card (Y : Set S.left) = Y.card := by simp
  obtain ⟨T,hrootT,hsepT,hdenseT,hlinkedT⟩ :=
    exists_linked_minimal_violating_shore (torsoGraph G S)
      (Y : Set S.left) α (fun T horder hsep hmT =>
        hsmall T horder (by simpa [hYnat] using hsep) hmT) (by
        simpa only [hYnat] using hex)
  have hrootT' : {u : S.left | (u : V) ∈ X} ⊆ T.left := by
    intro u hu
    exact hrootT ((mem_torsoRootFinset S X u).mpr hu)
  have hsepTcard : Nat.card T.separator < Y.card := by
    rw [← hYnat]
    exact hsepT
  have hsepT' : Nat.card T.separator <
      Nat.card {u : S.left | (u : V) ∈ X} := by
    rw [← hYset, hYnat]
    exact hsepTcard
  have hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right :=
    fun u hu => boundary_far_of_dense_torso_shore G (X : Set V) α hm
      S hrootS T hrootT' hsepT' hdenseT hu
  have hfarT : T.strictRight.Nonempty := by
    by_contra h
    have hempty : T.strictRight = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [hempty] at hdenseT
    simp [edgeIncidenceSetCount, edgeIncidenceSet] at hdenseT
  let Q := glueTorsoFar S T hBoundary
  have hrootQ : (X : Set V) ⊆ Q.left := by
    intro x hx
    rw [glueTorsoFar_left]
    exact ⟨⟨x,hrootS hx⟩,
      hrootT ((mem_torsoRootFinset S X _).mpr hx),rfl⟩
  have hsepQ : Nat.card Q.separator < X.card := by
    rw [glueTorsoFar_separator_card]
    simpa [hYcard] using hsepTcard
  have hlinkedQ : RootedLinked (G.induce Q.right)
      (separationBoundaryFinset Q) := hglue T hBoundary hlinkedT
  exact ⟨Q,hrootQ,
    glueTorsoFar_strictRight_nonempty S T hBoundary hfarS,
    hsepQ,hlinkedQ,
    glueTorsoFar_left_card_lt S T hBoundary hfarT⟩

/-- The torso of an inclusion-minimal lower-order rigid separation is massed. -/
theorem massed_torso_of_minimal_lower_rigid
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (α : ℝ)
    (hm : MassedPair G (X : Set V) α)
    (S : VertexSeparation G) [Fintype S.left]
    (hrootS : (X : Set V) ⊆ S.left)
    (hfarS : S.strictRight.Nonempty)
    (hsepS : Nat.card S.separator < X.card)
    (hsmall : ∀ T : VertexSeparation (torsoGraph G S),
      Nat.card T.right < Fintype.card S.left →
      Nat.card T.separator < (torsoRootFinset S X).card →
      MassedPair ((torsoGraph G S).induce T.right)
        {u : T.right | (u : S.left) ∈ T.left} α →
      RootedLinked ((torsoGraph G S).induce T.right)
        (separationBoundaryFinset T))
    (hglue : ∀ (T : VertexSeparation (torsoGraph G S))
      (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right),
      RootedLinked ((torsoGraph G S).induce T.right)
        (separationBoundaryFinset T) →
      RootedLinked (G.induce (glueTorsoFar S T hBoundary).right)
        (separationBoundaryFinset (glueTorsoFar S T hBoundary)))
    (hmin : ∀ Q : VertexSeparation G,
      (X : Set V) ⊆ Q.left → Q.strictRight.Nonempty →
      Nat.card Q.separator < X.card →
      RootedLinked (G.induce Q.right) (separationBoundaryFinset Q) →
      Nat.card S.left ≤ Nat.card Q.left) :
    MassedPair (torsoGraph G S)
      (torsoRootFinset S X : Set S.left) α := by
  classical
  letI : DecidableEq S.left := Classical.decEq _
  letI : DecidableRel (torsoGraph G S).Adj := Classical.decRel _
  let Y := torsoRootFinset S X
  have hYnat : Nat.card (Y : Set S.left) = Y.card := by simp
  have hYcard : Y.card = X.card := torsoRootFinset_card S X hrootS
  refine ⟨?_, ?_⟩
  · have hglobal := torso_global_of_massed G (X : Set V) α hm S hrootS
      (by simpa using hsepS)
    have hcompl : ((Y : Set S.left)ᶜ) =
        {u : S.left | (u : V) ∉ X} := by
      ext u
      simp [Y]
    rw [hcompl]
    simpa [Y,torsoRootFinset] using hglobal
  · intro T hrootT hsepT
    by_contra hnot
    have hdense : α * (Nat.card T.strictRight : ℝ) <
        (edgeIncidenceSetCount (torsoGraph G S) T.strictRight : ℝ) :=
      lt_of_not_ge hnot
    have hsepTcard : Nat.card T.separator < Y.card := by
      rw [← hYnat]
      exact hsepT
    obtain ⟨Q,hrootQ,hfarQ,hsepQ,hlinkedQ,hlt⟩ :=
      smaller_rigid_of_torso_shore_violation G X α hm S hrootS hfarS
        hsmall hglue ⟨T,hrootT,hsepTcard,hdense⟩
    have hle := hmin Q hrootQ hfarQ hsepQ hlinkedQ
    omega
/-- A proper far shore makes the near side smaller than the whole graph. -/
theorem left_card_lt_of_strictRight_nonempty
    {G : SimpleGraph V} (S : VertexSeparation G)
    (hfar : S.strictRight.Nonempty) :
    Nat.card S.left < Fintype.card V := by
  classical
  obtain ⟨x,hxR,hxNotL⟩ := hfar
  have hss : S.left ⊂ (Set.univ : Set V) := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨Set.subset_univ _, ?_⟩
    intro heq
    exact hxNotL (heq.symm ▸ Set.mem_univ x)
  have hc := Set.ncard_lt_ncard hss
  change S.left.ncard < Fintype.card V
  simpa only [Set.ncard_univ, Nat.card_eq_fintype_card] using hc
/-- Under order-minimality, a massed pair with a lower-order rigid shore
is already rooted linked. -/
theorem rootedLinked_of_lower_rigid_and_smaller_massed
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (α : ℝ)
    (hm : MassedPair G (X : Set V) α)
    (hsmallTorso : ∀ (S : VertexSeparation G) [Fintype S.left],
      Nat.card S.left < Fintype.card V →
      MassedPair (torsoGraph G S)
        (torsoRootFinset S X : Set S.left) α →
      RootedLinked (torsoGraph G S) (torsoRootFinset S X))
    (hsmallShore : ∀ (S : VertexSeparation G) [Fintype S.left],
      Nat.card S.left < Fintype.card V →
      ∀ T : VertexSeparation (torsoGraph G S),
      Nat.card T.right < Fintype.card S.left →
      Nat.card T.separator < (torsoRootFinset S X).card →
      MassedPair ((torsoGraph G S).induce T.right)
        {u : T.right | (u : S.left) ∈ T.left} α →
      RootedLinked ((torsoGraph G S).induce T.right)
        (separationBoundaryFinset T))
    (hglue : ∀ (S : VertexSeparation G) [Fintype S.left]
      (T : VertexSeparation (torsoGraph G S))
      (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right),
      RootedLinked (G.induce S.right) (separationBoundaryFinset S) →
      RootedLinked ((torsoGraph G S).induce T.right)
        (separationBoundaryFinset T) →
      RootedLinked (G.induce (glueTorsoFar S T hBoundary).right)
        (separationBoundaryFinset (glueTorsoFar S T hBoundary)))
    (hex : ∃ S : VertexSeparation G,
      (X : Set V) ⊆ S.left ∧ S.strictRight.Nonempty ∧
      Nat.card S.separator < X.card ∧
      RootedLinked (G.induce S.right) (separationBoundaryFinset S)) :
    RootedLinked G X := by
  classical
  let P : ℕ → Prop := fun n => ∃ S : VertexSeparation G,
    (X : Set V) ⊆ S.left ∧ S.strictRight.Nonempty ∧
    Nat.card S.separator < X.card ∧
    RootedLinked (G.induce S.right) (separationBoundaryFinset S) ∧
    Nat.card S.left = n
  have hP : ∃ n, P n := by
    obtain ⟨S,hroot,hfar,hsep,hlinked⟩ := hex
    exact ⟨Nat.card S.left,S,hroot,hfar,hsep,hlinked,rfl⟩
  obtain ⟨S,hrootS,hfarS,hsepS,hlinkedS,hcardS⟩ := Nat.find_spec hP
  letI : Fintype S.left := Fintype.ofFinite S.left
  have hmin (Q : VertexSeparation G)
      (hrootQ : (X : Set V) ⊆ Q.left)
      (hfarQ : Q.strictRight.Nonempty)
      (hsepQ : Nat.card Q.separator < X.card)
      (hlinkedQ : RootedLinked (G.induce Q.right)
        (separationBoundaryFinset Q)) :
      Nat.card S.left ≤ Nat.card Q.left := by
    have hQ : P (Nat.card Q.left) :=
      ⟨Q,hrootQ,hfarQ,hsepQ,hlinkedQ,rfl⟩
    have hbound := Nat.find_min' hP hQ
    rwa [← hcardS] at hbound
  have htorso : MassedPair (torsoGraph G S)
      (torsoRootFinset S X : Set S.left) α :=
    massed_torso_of_minimal_lower_rigid G X α hm S hrootS hfarS
      hsepS (hsmallShore S (left_card_lt_of_strictRight_nonempty S hfarS)) (fun T hBoundary hT =>
        hglue S T hBoundary hlinkedS hT) hmin
  have hK : RootedLinked (torsoGraph G S) (torsoRootFinset S X) :=
    hsmallTorso S (left_card_lt_of_strictRight_nonempty S hfarS) htorso
  exact rootedLinked_of_torso_and_far G S X (torsoRootFinset S X)
    hrootS (fun u => mem_torsoRootFinset S X u) hK hlinkedS
end Linkedness
end HadwigerLean
