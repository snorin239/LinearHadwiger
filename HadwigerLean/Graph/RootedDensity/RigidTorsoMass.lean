import HadwigerLean.Graph.RootedDensity.MassedStructure
import HadwigerLean.Graph.Linkedness.RigidTorso

/-!
# Target-independent torso mass reduction for Appendix F.a

The edge-count and separation geometry follows the checked linkedness
torso argument. Universality enters only through smaller-order induction
and a transport across the rigid shore.
-/

namespace HadwigerLean.RootedDensity

universe u v

/-- A dense F.2 violating torso shore gives a rigid separation with
smaller near side, provided universality of smaller massed pairs and
transport across the original far shore are available. -/
theorem smaller_rigid_of_torso_shore_violation
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) (X : Finset V) (α : ℝ)
    (hm : MassedPair G (X : Set V) α)
    (S : VertexSeparation G) [Fintype S.left]
    (hrootS : (X : Set V) ⊆ S.left)
    (hfarS : S.strictRight.Nonempty)
    (hsmall : ∀ T : VertexSeparation (Linkedness.torsoGraph G S),
      Nat.card T.right < Fintype.card S.left →
      Nat.card T.separator <
        (Linkedness.torsoRootFinset S X).card →
      MassedPair ((Linkedness.torsoGraph G S).induce T.right)
        {u : T.right | (u : S.left) ∈ T.left} α →
      UniversalAtRightShore H T)
    (hglue : ∀ (T : VertexSeparation (Linkedness.torsoGraph G S))
      (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right),
      UniversalAtRightShore H T →
      UniversalAtRightShore H
        (Linkedness.glueTorsoFar S T hBoundary))
    (hex : ∃ T : VertexSeparation (Linkedness.torsoGraph G S),
      (Linkedness.torsoRootFinset S X : Set S.left) ⊆ T.left ∧
      Nat.card T.separator <
        (Linkedness.torsoRootFinset S X).card ∧
      α * (Nat.card T.strictRight : ℝ) <
        (edgeIncidenceSetCount (Linkedness.torsoGraph G S)
          T.strictRight : ℝ)) :
    ∃ Q : VertexSeparation G,
      (X : Set V) ⊆ Q.left ∧
      Q.strictRight.Nonempty ∧
      Nat.card Q.separator < X.card ∧
      UniversalAtRightShore H Q ∧
      Nat.card Q.left < Nat.card S.left := by
  classical
  letI : DecidableEq S.left := Classical.decEq _
  letI : DecidableRel (Linkedness.torsoGraph G S).Adj := Classical.decRel _
  let Y := Linkedness.torsoRootFinset S X
  have hYcard : Y.card = X.card :=
    Linkedness.torsoRootFinset_card S X hrootS
  have hYset : (Y : Set S.left) =
      {u : S.left | (u : V) ∈ X} := by
    ext u
    simp [Y]
  have hYnat : Nat.card (Y : Set S.left) = Y.card := by simp
  obtain ⟨T,hrootT,hsepT,hdenseT,hmT,horderT⟩ :=
    exists_massed_dense_shore_of_violation
      (Linkedness.torsoGraph G S) (Y : Set S.left) α
      (by simpa only [hYnat] using hex)
  have huniT : UniversalAtRightShore H T :=
    hsmall T horderT (by simpa only [hYnat] using hsepT) hmT
  have hrootT' : {u : S.left | (u : V) ∈ X} ⊆ T.left := by
    intro u hu
    exact hrootT ((Linkedness.mem_torsoRootFinset S X u).mpr hu)
  have hsepTcard : Nat.card T.separator < Y.card := by
    rw [← hYnat]
    exact hsepT
  have hsepT' : Nat.card T.separator <
      Nat.card {u : S.left | (u : V) ∈ X} := by
    rw [← hYset, hYnat]
    exact hsepTcard
  have hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right :=
    fun u hu => Linkedness.boundary_far_of_dense_torso_shore
      G (X : Set V) α hm S hrootS T hrootT' hsepT' hdenseT hu
  have hfarT : T.strictRight.Nonempty := by
    by_contra h
    have hempty : T.strictRight = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp h
    rw [hempty] at hdenseT
    simp [edgeIncidenceSetCount, edgeIncidenceSet] at hdenseT
  let Q := Linkedness.glueTorsoFar S T hBoundary
  have hrootQ : (X : Set V) ⊆ Q.left := by
    intro x hx
    rw [Linkedness.glueTorsoFar_left]
    exact ⟨⟨x,hrootS hx⟩,
      hrootT ((Linkedness.mem_torsoRootFinset S X _).mpr hx),rfl⟩
  have hsepQ : Nat.card Q.separator < X.card := by
    rw [Linkedness.glueTorsoFar_separator_card]
    simpa [hYcard] using hsepTcard
  have huniQ : UniversalAtRightShore H Q := hglue T hBoundary huniT
  exact ⟨Q,hrootQ,
    Linkedness.glueTorsoFar_strictRight_nonempty S T
      hBoundary hfarS,
    hsepQ,huniQ,
    Linkedness.glueTorsoFar_left_card_lt S T hBoundary hfarT⟩

/-- The near-side torso of a smallest lower-order H-rigid shore remains
massed once smaller dense shores transport their universality back to G. -/
theorem massed_torso_of_minimal_lower_rigid
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) (X : Finset V) (α : ℝ)
    (hm : MassedPair G (X : Set V) α)
    (S : VertexSeparation G) [Fintype S.left]
    (hrootS : (X : Set V) ⊆ S.left)
    (hfarS : S.strictRight.Nonempty)
    (hsepS : Nat.card S.separator < X.card)
    (hsmall : ∀ T : VertexSeparation (Linkedness.torsoGraph G S),
      Nat.card T.right < Fintype.card S.left →
      Nat.card T.separator <
        (Linkedness.torsoRootFinset S X).card →
      MassedPair ((Linkedness.torsoGraph G S).induce T.right)
        {u : T.right | (u : S.left) ∈ T.left} α →
      UniversalAtRightShore H T)
    (hglue : ∀ (T : VertexSeparation (Linkedness.torsoGraph G S))
      (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right),
      UniversalAtRightShore H T →
      UniversalAtRightShore H
        (Linkedness.glueTorsoFar S T hBoundary))
    (hmin : ∀ Q : VertexSeparation G,
      (X : Set V) ⊆ Q.left →
      Q.strictRight.Nonempty →
      Nat.card Q.separator < X.card →
      UniversalAtRightShore H Q →
      Nat.card S.left ≤ Nat.card Q.left) :
    MassedPair (Linkedness.torsoGraph G S)
      (Linkedness.torsoRootFinset S X : Set S.left) α := by
  classical
  letI : DecidableEq S.left := Classical.decEq _
  letI : DecidableRel (Linkedness.torsoGraph G S).Adj := Classical.decRel _
  let Y := Linkedness.torsoRootFinset S X
  have hYnat : Nat.card (Y : Set S.left) = Y.card := by simp
  have hYcard : Y.card = X.card :=
    Linkedness.torsoRootFinset_card S X hrootS
  refine ⟨?_, ?_⟩
  · have hglobal := Linkedness.torso_global_of_massed
      G (X : Set V) α hm S hrootS (by simpa using hsepS)
    have hcompl : ((Y : Set S.left)ᶜ) =
        {u : S.left | (u : V) ∉ X} := by
      ext u
      simp [Y]
    rw [hcompl]
    simpa [Y,Linkedness.torsoRootFinset] using hglobal
  · intro T hrootT hsepT
    by_contra hnot
    have hdense : α * (Nat.card T.strictRight : ℝ) <
        (edgeIncidenceSetCount (Linkedness.torsoGraph G S)
          T.strictRight : ℝ) := lt_of_not_ge hnot
    have hsepTcard : Nat.card T.separator < Y.card := by
      rw [← hYnat]
      exact hsepT
    obtain ⟨Q,hrootQ,hfarQ,hsepQ,huniQ,hlt⟩ :=
      smaller_rigid_of_torso_shore_violation
        G H X α hm S hrootS hfarS hsmall hglue
        ⟨T,hrootT,hsepTcard,hdense⟩
    have hle := hmin Q hrootQ hfarQ hsepQ huniQ
    omega


/-- A lower-order H-rigid shore yields full rooted universality once
smaller massed torsos are universal and the two rigid gluing transports
are supplied. This isolates the remaining model-theoretic F.a work. -/
theorem universalAt_of_lower_rigid_and_smaller_massed
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) (X : Finset V) (α : ℝ)
    (hm : MassedPair G (X : Set V) α)
    (hsmallTorso : ∀ (S : VertexSeparation G) [Fintype S.left],
      Nat.card S.left < Fintype.card V →
      MassedPair (Linkedness.torsoGraph G S)
        (Linkedness.torsoRootFinset S X : Set S.left) α →
      UniversalAt (Linkedness.torsoGraph G S) H
        (Linkedness.torsoRootFinset S X))
    (hsmallShore : ∀ (S : VertexSeparation G) [Fintype S.left],
      Nat.card S.left < Fintype.card V →
      ∀ T : VertexSeparation (Linkedness.torsoGraph G S),
      Nat.card T.right < Fintype.card S.left →
      Nat.card T.separator <
        (Linkedness.torsoRootFinset S X).card →
      MassedPair ((Linkedness.torsoGraph G S).induce T.right)
        {u : T.right | (u : S.left) ∈ T.left} α →
      UniversalAtRightShore H T)
    (hglue : ∀ (S : VertexSeparation G) [Fintype S.left]
      (T : VertexSeparation (Linkedness.torsoGraph G S))
      (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right),
      (X : Set V) ⊆ S.left →
      S.strictRight.Nonempty →
      Nat.card S.separator < X.card →
      UniversalAtRightShore H S →
      UniversalAtRightShore H T →
      UniversalAtRightShore H
        (Linkedness.glueTorsoFar S T hBoundary))
    (hreverse : ∀ (S : VertexSeparation G) [Fintype S.left],
      (X : Set V) ⊆ S.left →
      Nat.card S.separator < X.card →
      UniversalAtRightShore H S →
      UniversalAt (Linkedness.torsoGraph G S) H
        (Linkedness.torsoRootFinset S X) →
      UniversalAt G H X)
    (hex : ∃ S : VertexSeparation G,
      (X : Set V) ⊆ S.left ∧ S.strictRight.Nonempty ∧
      Nat.card S.separator < X.card ∧
      UniversalAtRightShore H S) :
    UniversalAt G H X := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ S : VertexSeparation G,
      (X : Set V) ⊆ S.left ∧
      S.strictRight.Nonempty ∧
      Nat.card S.separator < X.card ∧
      UniversalAtRightShore H S ∧
      Nat.card S.left = n
  have hP : ∃ n, P n := by
    obtain ⟨S,hroot,hfar,hsep,huni⟩ := hex
    exact ⟨Nat.card S.left,S,hroot,hfar,hsep,huni,rfl⟩
  obtain ⟨S,hrootS,hfarS,hsepS,huniS,hcardS⟩ :=
    Nat.find_spec hP
  letI : Fintype S.left := Fintype.ofFinite S.left
  have hmin (Q : VertexSeparation G)
      (hrootQ : (X : Set V) ⊆ Q.left)
      (hfarQ : Q.strictRight.Nonempty)
      (hsepQ : Nat.card Q.separator < X.card)
      (huniQ : UniversalAtRightShore H Q) :
      Nat.card S.left ≤ Nat.card Q.left := by
    have hQ : P (Nat.card Q.left) :=
      ⟨Q,hrootQ,hfarQ,hsepQ,huniQ,rfl⟩
    have hbound := Nat.find_min' hP hQ
    rwa [← hcardS] at hbound
  have hleft : Nat.card S.left < Fintype.card V :=
    Linkedness.left_card_lt_of_strictRight_nonempty S hfarS
  have htorso : MassedPair (Linkedness.torsoGraph G S)
      (Linkedness.torsoRootFinset S X : Set S.left) α :=
    massed_torso_of_minimal_lower_rigid
      G H X α hm S hrootS hfarS hsepS
      (hsmallShore S hleft)
      (fun T hBoundary hT => hglue S T hBoundary hrootS hfarS hsepS huniS hT)
      hmin
  have hK : UniversalAt (Linkedness.torsoGraph G S) H
      (Linkedness.torsoRootFinset S X) :=
    hsmallTorso S hleft htorso
  exact hreverse S hrootS hsepS huniS hK

end HadwigerLean.RootedDensity
