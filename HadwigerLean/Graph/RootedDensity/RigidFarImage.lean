import HadwigerLean.Graph.RootedDensity.TorsoFarCross
import HadwigerLean.Graph.RootedDensity.RigidUnion

/-! Ambient properties of far branches of the partial rigid-side model. -/

namespace HadwigerLean.RootedDensity

universe u v

theorem rigidFarBranchImage_subset_right
    {V : Type u} {I : Type v} [DecidableEq I]
    {G : SimpleGraph V} (S : VertexSeparation G)
    {H : SimpleGraph I} (Y : Finset I)
    {q : ↥(Y : Set I) → S.right}
    (N : RootedMinorModel (H.induce (Y : Set I)) (G.induce S.right) q)
    (i : I) : rigidFarBranchImage S Y N i ⊆ S.right := by
  intro x hx
  obtain ⟨_,z,_,rfl⟩ :=
    (mem_rigidFarBranchImage_iff S Y N i x).mp hx
  exact z.2

theorem rigidFarBranchImage_root_mem
    {V : Type u} {I : Type v} [DecidableEq I]
    {G : SimpleGraph V} (S : VertexSeparation G)
    {H : SimpleGraph I} (Y : Finset I)
    {q : ↥(Y : Set I) → S.right}
    (N : RootedMinorModel (H.induce (Y : Set I)) (G.induce S.right) q)
    (j : ↥(Y : Set I)) :
    (q j : V) ∈ rigidFarBranchImage S Y N j.1 := by
  exact (mem_rigidFarBranchImage_iff S Y N j.1 _).mpr
    ⟨j.2,q j,N.root_mem j,rfl⟩

theorem rigidFarBranchImage_connected
    {V : Type u} {I : Type v} [DecidableEq I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    {H : SimpleGraph I} (Y : Finset I)
    {q : ↥(Y : Set I) → S.right}
    (N : RootedMinorModel (H.induce (Y : Set I)) (G.induce S.right) q)
    (j : ↥(Y : Set I)) :
    (G.induce (rigidFarBranchImage S Y N j.1)).Connected := by
  have hset : rigidFarBranchImage S Y N j.1 =
      Subtype.val '' N.branch j := by
    simp [rigidFarBranchImage]
  rw [hset]
  exact connected_induce_subtype_image G S.right (N.branch j) (N.connected j)

theorem rigidFarBranchImage_pairwise_disjoint
    {V : Type u} {I : Type v} [DecidableEq I]
    {G : SimpleGraph V} (S : VertexSeparation G)
    {H : SimpleGraph I} (Y : Finset I)
    {q : ↥(Y : Set I) → S.right}
    (N : RootedMinorModel (H.induce (Y : Set I)) (G.induce S.right) q) :
    Pairwise (fun i j =>
      Disjoint (rigidFarBranchImage S Y N i)
        (rigidFarBranchImage S Y N j)) := by
  classical
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨hi,a,ha,hax⟩ :=
    (mem_rigidFarBranchImage_iff S Y N i x).mp hxi
  obtain ⟨hj,b,hb,hbx⟩ :=
    (mem_rigidFarBranchImage_iff S Y N j x).mp hxj
  have hab : a = b := Subtype.ext (hax.trans hbx.symm)
  subst b
  exact (Set.disjoint_left.mp (N.disjoint (by
    intro h
    exact hij (congrArg Subtype.val h)))) ha hb

theorem rigidFarBranchImage_edge
    {V : Type u} {I : Type v} [DecidableEq I]
    {G : SimpleGraph V} (S : VertexSeparation G)
    {H : SimpleGraph I} (Y : Finset I)
    {q : ↥(Y : Set I) → S.right}
    (N : RootedMinorModel (H.induce (Y : Set I)) (G.induce S.right) q)
    (i j : ↥(Y : Set I)) (hij : H.Adj i.1 j.1) :
    ∃ x ∈ rigidFarBranchImage S Y N i.1,
      ∃ y ∈ rigidFarBranchImage S Y N j.1, G.Adj x y := by
  obtain ⟨x,hx,y,hy,hxy⟩ := N.adjacent hij
  exact ⟨x.1,
    (mem_rigidFarBranchImage_iff S Y N i.1 _).mpr ⟨i.2,x,hx,rfl⟩,
    y.1,
    (mem_rigidFarBranchImage_iff S Y N j.1 _).mpr ⟨j.2,y,hy,rfl⟩,
    hxy⟩

end HadwigerLean.RootedDensity

