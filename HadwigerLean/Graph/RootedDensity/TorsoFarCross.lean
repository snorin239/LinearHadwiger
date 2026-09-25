import HadwigerLean.Graph.RootedDensity.TorsoFarIntersections

/-! The unique label at an overlap of a near piece and a far branch. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- The ambient vertex set of one rigid-side branch, empty if its target
label is absent from the partial rigid-side model. -/
def rigidFarBranchImage
    {V : Type u} {I : Type v} [DecidableEq I]
    {G : SimpleGraph V} (S : VertexSeparation G)
    {H : SimpleGraph I} (Y : Finset I)
    {q : ↥(Y : Set I) → S.right}
    (N : RootedMinorModel (H.induce (Y : Set I)) (G.induce S.right) q)
    (i : I) : Set V :=
  if hi : i ∈ Y then Subtype.val '' N.branch ⟨i, hi⟩ else ∅

theorem mem_rigidFarBranchImage_iff
    {V : Type u} {I : Type v} [DecidableEq I]
    {G : SimpleGraph V} (S : VertexSeparation G)
    {H : SimpleGraph I} (Y : Finset I)
    {q : ↥(Y : Set I) → S.right}
    (N : RootedMinorModel (H.induce (Y : Set I)) (G.induce S.right) q)
    (i : I) (x : V) :
    x ∈ rigidFarBranchImage S Y N i ↔
      ∃ hi : i ∈ Y, ∃ z : S.right,
        z ∈ N.branch ⟨i, hi⟩ ∧ (z : V) = x := by
  classical
  by_cases hi : i ∈ Y
  · simp only [rigidFarBranchImage, dif_pos hi]
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨hi,z,hz,rfl⟩
    · rintro ⟨hi',z,hz,rfl⟩
      exact ⟨z,by simpa only [proof_irrel_heq] using hz,rfl⟩
  · simp [rigidFarBranchImage, hi]

/-- The label of an overlap between a near piece and a rigid far branch
is determined by that near piece's unique adhesion vertex. -/
theorem unique_near_piece_far_overlap_label
    {V : Type u} {I : Type v} [Fintype V] [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    (H : SimpleGraph I)
    (φ : ↥(Linkedness.separationBoundaryFinset S : Set S.right) ↪ I)
    (Y : Finset I) (q : ↥(Y : Set I) → S.right)
    (N : RootedMinorModel (H.induce (Y : Set I)) (G.induce S.right) q)
    (hq : ∀ z : ↥(Linkedness.separationBoundaryFinset S : Set S.right),
      ∃ hz : φ z ∈ Y, q ⟨φ z, hz⟩ = z.1)
    (A : Set S.left) (z : S.left) (hzRight : (z : V) ∈ S.right)
    (hunique : ∀ a ∈ A, (a : V) ∈ S.right → a = z)
    (i : I) (x : V)
    (hxNear : x ∈ Subtype.val '' A)
    (hxFar : x ∈ rigidFarBranchImage S Y N i) :
    φ ⟨⟨(z : V), hzRight⟩,
      (Linkedness.mem_separationBoundaryFinset S _).mpr z.2⟩ = i := by
  classical
  obtain ⟨a,ha,rfl⟩ := hxNear
  obtain ⟨hi,b,hb,hba⟩ :=
    (mem_rigidFarBranchImage_iff S Y N i _).mp hxFar
  have haRight : (a : V) ∈ S.right := hba ▸ b.2
  have haz : a = z := hunique a ha haRight
  have hbz : b = ⟨(z : V), hzRight⟩ := by
    apply Subtype.ext
    exact hba.trans (congrArg Subtype.val haz)
  have hzFar : (⟨(z : V), hzRight⟩ : S.right) ∈
      N.branch ⟨i, hi⟩ := hbz ▸ hb
  exact rigid_far_branch_adhesion_label G S H φ Y q N hq
    ⟨i,hi⟩ ⟨⟨(z : V), hzRight⟩,
      (Linkedness.mem_separationBoundaryFinset S _).mpr z.2⟩ hzFar

end HadwigerLean.RootedDensity



