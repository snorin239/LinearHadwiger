import HadwigerLean.Graph.RootedDensity.UniversalFan
import HadwigerLean.Graph.RootedDensity.UniversalNestedReverse
import HadwigerLean.Graph.Linkedness.CoreFarFan

/-! A saturated boundary-to-core fan makes the far shore universal. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- A disjoint fan from every boundary vertex into an H-universal core,
confined to the far side, transfers universality to that far side at its
adhesion. -/
theorem universalAt_right_of_boundary_core_fan
    {W : Type u} [Fintype W] {V : Type v} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    (H : SimpleGraph W) (hW : 0 < Fintype.card W)
    (J : Finset V) (hJright : ∀ x ∈ J, x ∈ S.right)
    (hcore : Universal (G.induce (J : Set V)) H)
    {q : ℕ} (C : IndexedPairs (Fin q) V) (F : IndexedLinkage G C)
    (hstarts : Finset.univ.image C.start = S.separatorFinset)
    (hfinish : ∀ i, C.finish i ∈ J)
    (hpathRight : ∀ i x, x ∈ pathVertexSet (F.path i) → x ∈ S.right) :
    letI : Fintype S.right := Fintype.ofFinite S.right
    UniversalAt (G.induce S.right) H
      (Linkedness.separationBoundaryFinset S) := by
  classical
  letI : Fintype S.right := Fintype.ofFinite S.right
  let J' : Finset S.right :=
    @Finset.subtype V S.right (Classical.decPred S.right) J
  have hcore' : Universal ((G.induce S.right).induce (J' : Set S.right)) H :=
    Universal.nested_of_ambient G H S.right J hJright hcore
  let L' := Linkedness.IndexedLinkage.induce F S.right hpathRight
  let P' : IndexedPairs (Fin q) S.right :=
    ⟨(fun i => ⟨C.start i,
        hpathRight i _ (pathVertexSet.start_mem (F.path i))⟩),
     (fun i => ⟨C.finish i,
        hpathRight i _ (pathVertexSet.finish_mem (F.path i))⟩)⟩
  have hP' : L' = (L' : IndexedLinkage (G.induce S.right) P') := rfl
  have hfinish' : ∀ i, P'.finish i ∈ J' := by
    intro i
    exact (Finset.mem_subtype).2 (hfinish i)
  have hstartImage : Finset.univ.image P'.start =
      Linkedness.separationBoundaryFinset S := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, hix⟩ := Finset.mem_image.mp hx
      apply (Linkedness.mem_separationBoundaryFinset S x).mpr
      have hmem : C.start i ∈ S.separatorFinset := by
        rw [← hstarts]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      have hxval : (x : V) = C.start i :=
        (congrArg Subtype.val hix).symm
      rw [hxval]
      exact (S.mem_separatorFinset _).mp hmem |>.1
    · intro hx
      have hxsep : (x : V) ∈ S.separatorFinset :=
        (S.mem_separatorFinset _).mpr
          ⟨(Linkedness.mem_separationBoundaryFinset S x).mp hx, x.property⟩
      rw [← hstarts] at hxsep
      obtain ⟨i, _, hix⟩ := Finset.mem_image.mp hxsep
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      apply Subtype.ext
      exact hix
  have huni := universalAt_of_universal_core_and_full_fan_image
    H (G.induce S.right) J' hcore' hW P' L' hfinish'
  simpa only [hstartImage] using huni

end HadwigerLean.RootedDensity
