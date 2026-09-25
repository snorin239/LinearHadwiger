import HadwigerLean.Graph.RootedDensity.TorsoColoredLabels
import HadwigerLean.Graph.RootedDensity.TorsoPiecePartition
import HadwigerLean.Graph.RootedDensity.RigidLabels

/-! A near star piece and a far branch meet only at its labeled adhesion root. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- The center piece contains no other adhesion vertex. -/
theorem torsoCenterPiece_unique_adhesion
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (t : TorsoTouchIndex S M)
    {x : S.left} (hx : x ∈ torsoCenterPiece G S H root M hmin t)
    (hxZ : (x : V) ∈ S.right) :
    x = torsoCenterBoundary G S H root M hmin t := by
  let A := chosenTorsoStar G S H root M hmin t
  obtain ⟨z,hz,rfl⟩ := hx
  have hzZ : z ∈ {q : M.branch t.1 | ((q.1 : S.left) : V) ∈ S.right} := hxZ
  have hcZ : A.center ∈
      {q : M.branch t.1 | ((q.1 : S.left) : V) ∈ S.right} :=
    A.center_boundary
  have heq : z = A.center :=
    starPiece_boundary_unique A.forest
      {q : M.branch t.1 | ((q.1 : S.left) : V) ∈ S.right}
      A.unique_boundary hcZ hzZ hz
  exact congrArg Subtype.val heq

/-- A hanging piece contains no adhesion vertex other than its own
distinguished hanger. -/
theorem torsoHangerPiece_unique_adhesion
    {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (hmin : ∀ N : RootedMinorModel H (Linkedness.torsoGraph G S) root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (w : TorsoHangerIndex G S H root M hmin)
    {x : S.left} (hx : x ∈ torsoHangerPiece G S H root M hmin w)
    (hxZ : (x : V) ∈ S.right) :
    x = torsoHangerBoundary G S H root M hmin w := by
  let A := chosenTorsoStar G S H root M hmin w.1
  obtain ⟨z,hz,rfl⟩ := hx
  have hzZ : z ∈ {q : M.branch w.1.1 | ((q.1 : S.left) : V) ∈ S.right} := hxZ
  have hwZ : w.2.1 ∈
      {q : M.branch w.1.1 | ((q.1 : S.left) : V) ∈ S.right} :=
    w.2.2.1
  have heq : z = w.2.1 :=
    starPiece_boundary_unique A.forest
      {q : M.branch w.1.1 | ((q.1 : S.left) : V) ∈ S.right}
      A.unique_boundary hwZ hzZ hz
  exact congrArg Subtype.val heq

/-- In a rooted rigid-side model, any adhesion vertex in a far branch
has the unique label assigned to that vertex by the full injection. -/
theorem rigid_far_branch_adhesion_label
    {V : Type u} {I : Type v} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : VertexSeparation G)
    (H : SimpleGraph I)
    (φ : ↥(Linkedness.separationBoundaryFinset S : Set S.right) ↪ I)
    (Y : Finset I) (q : ↥(Y : Set I) → S.right)
    (N : RootedMinorModel (H.induce (Y : Set I)) (G.induce S.right) q)
    (hq : ∀ z : ↥(Linkedness.separationBoundaryFinset S : Set S.right),
      ∃ hz : φ z ∈ Y, q ⟨φ z, hz⟩ = z.1)
    (j : ↥(Y : Set I))
    (z : ↥(Linkedness.separationBoundaryFinset S : Set S.right))
    (hz : z.1 ∈ N.branch j) : φ z = j.1 := by
  obtain ⟨hφY, hroot⟩ := hq z
  by_contra hne
  have hne' : (⟨φ z, hφY⟩ : ↥(Y : Set I)) ≠ j := by
    intro heq
    exact hne (congrArg Subtype.val heq)
  exact (N.other_root_not_mem hne'.symm) (by rw [hroot]; exact hz)

end HadwigerLean.RootedDensity

