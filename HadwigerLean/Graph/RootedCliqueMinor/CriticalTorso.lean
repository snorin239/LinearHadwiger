import HadwigerLean.Graph.RootedCliqueMinor.DichotomyReduction
import HadwigerLean.Graph.RootedCliqueMinor.TorsoConnectivity
import Mathlib.Data.Fintype.EquivFin

/-!
# The smaller torso supplied by a critical separator

The order-r boundary is enumerated as a new root family. All original
clique branches restrict to the right torso, whose vertex type is smaller.
-/

namespace HadwigerLean

/-- Enumerate the boundary of an order-r separation as roots in its right
shore. The range of these roots is exactly the set completed in the torso. -/
theorem VertexSeparation.exists_boundary_roots
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : VertexSeparation G) {r : ℕ}
    (hX : S.separatorFinset.card = r) :
    ∃ xroot : Fin r → S.right,
      Function.Injective xroot ∧
      Set.range xroot = {x : S.right | (x : V) ∈ S.left} ∧
      (∀ x ∈ S.separatorFinset, ∃ i, (xroot i).1 = x) := by
  classical
  let X := S.separatorFinset
  have hcard : Fintype.card X = r := by
    simpa only [Fintype.card_coe] using hX
  let e : X ≃ Fin r := Fintype.equivFinOfCardEq hcard
  let xroot : Fin r → S.right := fun i =>
    ⟨(e.symm i).1, ((S.mem_separatorFinset _).mp (e.symm i).2).2⟩
  refine ⟨xroot, ?_, ?_, ?_⟩
  · intro i j hij
    have hval : (e.symm i).1 = (e.symm j).1 := by
      exact congrArg (fun z : S.right => (z : V)) hij
    have h : e.symm i = e.symm j := Subtype.ext hval
    exact e.symm.injective h
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ((S.mem_separatorFinset _).mp (e.symm i).2).1
    · intro hxL
      have hxX : (x : V) ∈ X :=
        (S.mem_separatorFinset _).mpr ⟨hxL, x.property⟩
      refine ⟨e ⟨x.1, hxX⟩, ?_⟩
      apply Subtype.ext
      simp [xroot]
  · intro x hx
    let y : X := ⟨x, hx⟩
    refine ⟨e y, ?_⟩
    change (e.symm (e y)).1 = x
    simp [y]

/-- Restrict a completed-root model using an explicit enumeration of the
boundary, retaining the original restricted branch sets definitionally. -/
noncomputable def VertexSeparation.restrictCompletedRootModel_at_roots
    {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    (R : Set V) (hR : R ⊆ S.left)
    {H : SimpleGraph W} (M : MinorModel H (completeRoots G R))
    (hmeet : ∀ i, ∃ x ∈ M.branch i, x ∈ S.right)
    {r : ℕ} (xroot : Fin r → S.right)
    (hxrange : Set.range xroot = {x : S.right | (x : V) ∈ S.left}) :
    MinorModel H (completeRoots (G.induce S.right) (Set.range xroot)) := by
  let N := S.restrictCompletedRootModel R hR M hmeet
  refine {
    branch := N.branch
    connected := ?_
    disjoint := N.disjoint
    adjacent := ?_
  }
  · intro i
    simpa only [hxrange] using N.connected i
  · intro i j hij
    simpa only [hxrange] using N.adjacent hij

@[simp] theorem VertexSeparation.restrictCompletedRootModel_at_roots_branch
    {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    (R : Set V) (hR : R ⊆ S.left)
    {H : SimpleGraph W} (M : MinorModel H (completeRoots G R))
    (hmeet : ∀ i, ∃ x ∈ M.branch i, x ∈ S.right)
    {r : ℕ} (xroot : Fin r → S.right)
    (hxrange : Set.range xroot = {x : S.right | (x : V) ∈ S.left})
    (i : W) :
    (S.restrictCompletedRootModel_at_roots R hR M hmeet xroot hxrange).branch i =
      {x : S.right | (x : V) ∈ M.branch i} := by
  rfl
/-- A critical separator gives a strictly smaller completed right torso
carrying the restricted original clique model. -/
theorem RootCliqueCriticalSeparation.smaller_torso_model
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r : ℕ}
    {root : Fin r → V}
    {M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots G (Set.range root))}
    {a b : V} (C : RootCliqueCriticalSeparation G root M a b)
    [Fintype C.sep.right]
    (hroot : Function.Injective root)
    (haR : a ∉ Set.range root) :
    ∃ xroot : Fin r → C.sep.right,
      Function.Injective xroot ∧
      Set.range xroot = {x : C.sep.right | (x : V) ∈ C.sep.left} ∧
      (∀ x ∈ C.sep.separatorFinset, ∃ i, (xroot i).1 = x) ∧
      Fintype.card C.sep.right < Fintype.card V ∧
      Nonempty (MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
        (completeRoots (G.induce C.sep.right) (Set.range xroot))) := by
  classical
  let S := C.sep
  have hR : Set.range root ⊆ S.left := by
    rintro x ⟨i, rfl⟩
    exact C.roots_left i
  obtain ⟨j, hj⟩ := C.branch_far
  have hfar : S.strictRight.Nonempty := by
    obtain ⟨x, hx⟩ := (M.connected j).nonempty
    exact ⟨x, hj hx⟩
  have hmeet := S.cliqueBranches_meet_right (Set.range root) hR M j hj
  let N := S.restrictCompletedRootModel (Set.range root) hR M hmeet
  have hleft : S.strictLeft.Nonempty :=
    S.strictLeft_nonempty_of_nonroot_boundary root hroot C.roots_left
      C.order_eq C.a_boundary haR
  have hsmaller : Fintype.card S.right < Fintype.card V :=
    S.right_order_lt_of_strictLeft_nonempty hleft
  obtain ⟨xroot, hxinj, hxrange, hxsurj⟩ := S.exists_boundary_roots C.order_eq
  refine ⟨xroot, hxinj, hxrange, hxsurj, hsmaller, ?_⟩
  rw [hxrange]
  exact ⟨N⟩

/-- Use the endpoints of a full root-to-boundary linkage as the roots of
the smaller torso. This indexing is aligned for the later splice. -/
theorem RootCliqueCriticalSeparation.torso_model_at_linkage_finishes
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r : ℕ}
    {root : Fin r → V}
    {M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots G (Set.range root))}
    {a b : V} (C : RootCliqueCriticalSeparation G root M a b)
    {P : IndexedPairs (Fin r) V} (L : IndexedLinkage G P)
    (hfinish : ∀ i, P.finish i ∈ C.sep.separatorFinset)
    (hsurj : ∀ x ∈ C.sep.separatorFinset, ∃ i, P.finish i = x) :
    ∃ xroot : Fin r → C.sep.right,
      (∀ i, P.finish i = (xroot i).1) ∧
      Function.Injective xroot ∧
      Set.range xroot = {x : C.sep.right | (x : V) ∈ C.sep.left} ∧
      Nonempty (MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
        (completeRoots (G.induce C.sep.right) (Set.range xroot))) := by
  classical
  let S := C.sep
  let xroot : Fin r → S.right := fun i =>
    ⟨P.finish i, ((S.mem_separatorFinset _).mp (hfinish i)).2⟩
  have hxinj : Function.Injective xroot := by
    intro i j hij
    apply L.finish_injective
    exact congrArg (fun z : S.right => (z : V)) hij
  have hxrange : Set.range xroot = {x : S.right | (x : V) ∈ S.left} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ((S.mem_separatorFinset _).mp (hfinish i)).1
    · intro hxL
      have hxX : (x : V) ∈ S.separatorFinset :=
        (S.mem_separatorFinset _).mpr ⟨hxL, x.property⟩
      obtain ⟨i, hi⟩ := hsurj x hxX
      refine ⟨i, ?_⟩
      apply Subtype.ext
      exact hi
  have hR : Set.range root ⊆ S.left := by
    rintro x ⟨i, rfl⟩
    exact C.roots_left i
  obtain ⟨j, hj⟩ := C.branch_far
  have hmeet := S.cliqueBranches_meet_right (Set.range root) hR M j hj
  let N := S.restrictCompletedRootModel (Set.range root) hR M hmeet
  refine ⟨xroot, (fun i => rfl), hxinj, hxrange, ?_⟩
  rw [hxrange]
  exact ⟨N⟩
end HadwigerLean
