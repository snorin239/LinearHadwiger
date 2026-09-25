import HadwigerLean.Woven.Rerouting
import HadwigerLean.Woven.ThreeChildCombinatorics
import Mathlib.Tactic

/-!
# Assemble a rooted clique minor from three woven children

Two connector paths leave each parent root. Their far endpoints are the
roots of branches in two different child clique models. The child
models meet the connector linkage exactly in their own roots.
-/

namespace HadwigerLean
namespace Woven

/-- The first connector index assigned to a parent root. -/
def firstConnector {a : ℕ} (j : Fin a) : Fin (2 * a) :=
  ⟨j, by omega⟩

/-- The second connector index assigned to a parent root. -/
def secondConnector {a : ℕ} (j : Fin a) : Fin (2 * a) :=
  ⟨a + j, by omega⟩



/-- Enumerate three consecutive child blocks of size c when the
parent has exactly 3c = 2a connector indices. -/
def scaleAssignment {a c : ℕ} (hscale : 2 * a = 3 * c) :
    Fin (2 * a) ≃ Fin 3 × Fin c :=
  (finCongr hscale).trans finProdFinEquiv.symm

theorem connector_ne_of_parent_ne {a : ℕ} {j k : Fin a}
    (hjk : j ≠ k)
    {q r : Fin (2 * a)}
    (hq : q = firstConnector j ∨ q = secondConnector j)
    (hr : r = firstConnector k ∨ r = secondConnector k) :
    q ≠ r := by
  have hv : j.val ≠ k.val := by
    intro h
    exact hjk (Fin.ext h)
  rcases hq with rfl | rfl <;> rcases hr with rfl | rfl <;>
    intro h <;> have he := congrArg Fin.val h <;>
    simp [firstConnector, secondConnector] at he <;> omega

/-- Input contract for the final three-child rooted-minor assembly.

The bijection assigns each connector endpoint to one branch of exactly
one child. Exact intersections with the linkage are the properties
delivered by successive child rerouting. -/
structure ThreeChildFrame {V : Type*} (G : SimpleGraph V) (a c : ℕ) where
  root : Fin a → V
  root_injective : Function.Injective root
  childRoot : Fin 3 → Fin c → V
  childModel : ∀ k, RootedMinorModel
    (SimpleGraph.completeGraph (Fin c)) G (childRoot k)
  assignment : Fin (2 * a) ≃ Fin 3 × Fin c
  start : Fin (2 * a) → V
  linkage : IndexedLinkage G
    ⟨start, fun q => childRoot (assignment q).1 (assignment q).2⟩
  adjacent_first : ∀ j, G.Adj (root j) (start (firstConnector j))
  adjacent_second : ∀ j, G.Adj (root j) (start (secondConnector j))
  root_outside_linkage : ∀ j, root j ∉ linkage.vertices
  root_outside_child : ∀ j k, root j ∉ (childModel k).toMinorModel.vertices
  children_disjoint : Pairwise fun k l =>
    Disjoint (childModel k).toMinorModel.vertices
      (childModel l).toMinorModel.vertices
  exact_child_intersection : ∀ k,
    (childModel k).toMinorModel.vertices ∩ linkage.vertices =
      Set.range (childRoot k)
  different_children : ∀ j,
    (assignment (firstConnector j)).1 ≠
      (assignment (secondConnector j)).1

namespace ThreeChildFrame

variable {V : Type*} {G : SimpleGraph V} {a c : ℕ}
  (F : ThreeChildFrame G a c)

/-- The child containing a connector's far endpoint. -/
def child (q : Fin (2 * a)) : Fin 3 := (F.assignment q).1

/-- The branch number inside that child. -/
def slot (q : Fin (2 * a)) : Fin c := (F.assignment q).2

/-- The target vertex of a connector. -/
def target (q : Fin (2 * a)) : V := F.childRoot (F.child q) (F.slot q)

/-- The connector path together with its target branch. -/
def piece (q : Fin (2 * a)) : Set V :=
  pathVertexSet (F.linkage.path q) ∪
    (F.childModel (F.child q)).branch (F.slot q)

/-- The parent branch built from the two connectors and their child
branches. -/
def parentBranch (j : Fin a) : Set V :=
  insert (F.root j)
    (F.piece (firstConnector j) ∪ F.piece (secondConnector j))

private theorem target_mem_path (q : Fin (2 * a)) :
    F.target q ∈ pathVertexSet (F.linkage.path q) := by
  exact pathVertexSet.finish_mem _

private theorem target_mem_branch (q : Fin (2 * a)) :
    F.target q ∈ (F.childModel (F.child q)).branch (F.slot q) :=
  (F.childModel (F.child q)).root_mem (F.slot q)

/-- The path of connector q meets child k only at its own target, and
only when that target belongs to k. -/
theorem path_meets_child
    (q : Fin (2 * a)) (k : Fin 3) {x : V}
    (hxp : x ∈ pathVertexSet (F.linkage.path q))
    (hxm : x ∈ (F.childModel k).toMinorModel.vertices) :
    ∃ u : Fin c, x = F.childRoot k u ∧
      F.assignment q = (k, u) := by
  have hxL : x ∈ F.linkage.vertices :=
    F.linkage.path_subset_vertices q hxp
  have hxRange : x ∈ Set.range (F.childRoot k) := by
    rw [← F.exact_child_intersection k]
    exact ⟨hxm, hxL⟩
  obtain ⟨u, hxu⟩ := hxRange
  let q' : Fin (2 * a) := F.assignment.symm (k, u)
  have htarget : F.target q' = F.childRoot k u := by
    simp [target, child, slot, q']
  have hxp' : x ∈ pathVertexSet (F.linkage.path q') := by
    rw [← hxu, ← htarget]
    exact F.target_mem_path q'
  have hqq' : q = q' := by
    by_contra hne
    exact (Set.disjoint_left.mp (F.linkage.disjoint hne)) hxp hxp'
  refine ⟨u, hxu.symm, ?_⟩
  rw [hqq']
  exact F.assignment.apply_symm_apply (k, u)

/-- A connector path cannot use another connector's child branch. -/
theorem path_disjoint_other_branch
    {q r : Fin (2 * a)} (hqr : q ≠ r) :
    Disjoint (pathVertexSet (F.linkage.path q))
      ((F.childModel (F.child r)).branch (F.slot r)) := by
  apply Set.disjoint_left.mpr
  intro x hxp hxb
  have hxm : x ∈ (F.childModel (F.child r)).toMinorModel.vertices :=
    Set.mem_iUnion.mpr ⟨F.slot r, hxb⟩
  obtain ⟨u, hxu, hassign⟩ :=
    F.path_meets_child q (F.child r) hxp hxm
  have huBranch : x ∈ (F.childModel (F.child r)).branch u := by
    rw [hxu]
    exact (F.childModel (F.child r)).root_mem u
  have hur : u = F.slot r := by
    by_contra hne
    exact (Set.disjoint_left.mp
      ((F.childModel (F.child r)).disjoint hne)) huBranch hxb
  apply hqr
  apply F.assignment.injective
  simpa [child, slot, hur] using hassign


/-- Different connector indices select disjoint child branches. -/
theorem child_branches_disjoint
    {q r : Fin (2 * a)} (hqr : q ≠ r) :
    Disjoint ((F.childModel (F.child q)).branch (F.slot q))
      ((F.childModel (F.child r)).branch (F.slot r)) := by
  apply Set.disjoint_left.mpr
  intro x hxq hxr
  by_cases hchild : F.child q = F.child r
  · have hslot : F.slot q ≠ F.slot r := by
      intro hs
      apply hqr
      apply F.assignment.injective
      exact Prod.ext hchild hs
    rw [hchild] at hxq
    exact (Set.disjoint_left.mp
      ((F.childModel (F.child r)).disjoint hslot)) hxq hxr
  · have hxMq : x ∈ (F.childModel (F.child q)).toMinorModel.vertices :=
      Set.mem_iUnion.mpr ⟨F.slot q, hxq⟩
    have hxMr : x ∈ (F.childModel (F.child r)).toMinorModel.vertices :=
      Set.mem_iUnion.mpr ⟨F.slot r, hxr⟩
    exact (Set.disjoint_left.mp (F.children_disjoint hchild)) hxMq hxMr

/-- Distinct connector pieces are vertex-disjoint. -/
theorem piece_disjoint {q r : Fin (2 * a)} (hqr : q ≠ r) :
    Disjoint (F.piece q) (F.piece r) := by
  apply Set.disjoint_left.mpr
  intro x hxq hxr
  rcases hxq with hxPq | hxBq
  · rcases hxr with hxPr | hxBr
    · exact (Set.disjoint_left.mp (F.linkage.disjoint hqr)) hxPq hxPr
    · exact (Set.disjoint_left.mp (F.path_disjoint_other_branch hqr))
        hxPq hxBr
  · rcases hxr with hxPr | hxBr
    · exact (Set.disjoint_left.mp
        (F.path_disjoint_other_branch hqr.symm)) hxPr hxBq
    · exact (Set.disjoint_left.mp (F.child_branches_disjoint hqr))
        hxBq hxBr

/-- Each connector piece is connected through its common target. -/
theorem piece_connected (q : Fin (2 * a)) :
    (G.induce (F.piece q)).Connected := by
  have hP : (G.induce (pathVertexSet (F.linkage.path q))).Connected :=
    (F.linkage.path q :
      G.Walk (F.start q) (F.childRoot (F.assignment q).1 (F.assignment q).2)).connected_induce_support
  have hB : (G.induce
      ((F.childModel (F.child q)).branch (F.slot q))).Connected :=
    (F.childModel (F.child q)).connected (F.slot q)
  exact connected_induce_union_of_common hP hB
    (F.target_mem_path q) (F.target_mem_branch q)

/-- The original root joins a connector piece through its assigned
neighbor edge. -/
private theorem root_piece_connected (j : Fin a) (q : Fin (2 * a))
    (hadj : G.Adj (F.root j) (F.start q)) :
    (G.induce (insert (F.root j) (F.piece q))).Connected := by
  have hsing : (G.induce ({F.root j} : Set V)).Preconnected := by simp
  have hpiece : (G.induce (F.piece q)).Preconnected :=
    (F.piece_connected q).preconnected
  have hconn := G.connected_induce_union hsing hpiece
    (by simp : F.root j ∈ ({F.root j} : Set V))
    (Or.inl (pathVertexSet.start_mem (F.linkage.path q))) hadj
  simpa only [Set.singleton_union] using hconn

/-- Each assembled parent branch is connected. -/
theorem parentBranch_connected (j : Fin a) :
    (G.induce (F.parentBranch j)).Connected := by
  let q := firstConnector j
  let r := secondConnector j
  have hq : (G.induce (insert (F.root j) (F.piece q))).Connected :=
    F.root_piece_connected j q (F.adjacent_first j)
  have hr : (G.induce (insert (F.root j) (F.piece r))).Connected :=
    F.root_piece_connected j r (F.adjacent_second j)
  have hrootQ : F.root j ∈ insert (F.root j) (F.piece q) :=
    Set.mem_insert _ _
  have hrootR : F.root j ∈ insert (F.root j) (F.piece r) :=
    Set.mem_insert _ _
  have hunion := connected_induce_union_of_common hq hr hrootQ hrootR
  have hsets :
      insert (F.root j) (F.piece q) ∪
        insert (F.root j) (F.piece r) = F.parentBranch j := by
    ext x
    simp [parentBranch, q, r, or_assoc, or_left_comm, or_comm]
  rw [hsets] at hunion
  exact hunion

/-- Original parent roots lie outside every connector piece. -/
theorem root_not_mem_piece (j : Fin a) (q : Fin (2 * a)) :
    F.root j ∉ F.piece q := by
  rintro (hxP | hxB)
  · exact F.root_outside_linkage j
      (F.linkage.path_subset_vertices q hxP)
  · exact F.root_outside_child j (F.child q)
      (Set.mem_iUnion.mpr ⟨F.slot q, hxB⟩)

/-- The two pieces associated with different parent roots are
disjoint, regardless of which connector of each root is chosen. -/
private theorem parent_pieces_disjoint {j k : Fin a} (hjk : j ≠ k)
    {q r : Fin (2 * a)}
    (hq : q = firstConnector j ∨ q = secondConnector j)
    (hr : r = firstConnector k ∨ r = secondConnector k) :
    Disjoint (F.piece q) (F.piece r) :=
  F.piece_disjoint (connector_ne_of_parent_ne hjk hq hr)

/-- Branches assembled for different parent roots do not overlap. -/
theorem parentBranch_disjoint {j k : Fin a} (hjk : j ≠ k) :
    Disjoint (F.parentBranch j) (F.parentBranch k) := by
  apply Set.disjoint_left.mpr
  intro x hxj hxk
  have hxj' : x = F.root j ∨
      x ∈ F.piece (firstConnector j) ∨
      x ∈ F.piece (secondConnector j) := by
    simpa [parentBranch] using hxj
  have hxk' : x = F.root k ∨
      x ∈ F.piece (firstConnector k) ∨
      x ∈ F.piece (secondConnector k) := by
    simpa [parentBranch] using hxk
  rcases hxj' with hrootj | hfirstj | hsecondj
  · rcases hxk' with hrootk | hfirstk | hsecondk
    · exact hjk (F.root_injective (hrootj.symm.trans hrootk))
    · exact F.root_not_mem_piece j _ (hrootj ▸ hfirstk)
    · exact F.root_not_mem_piece j _ (hrootj ▸ hsecondk)
  · rcases hxk' with hrootk | hfirstk | hsecondk
    · exact F.root_not_mem_piece k _ (hrootk ▸ hfirstj)
    · exact (Set.disjoint_left.mp
        (F.parent_pieces_disjoint hjk (Or.inl rfl) (Or.inl rfl)))
        hfirstj hfirstk
    · exact (Set.disjoint_left.mp
        (F.parent_pieces_disjoint hjk (Or.inl rfl) (Or.inr rfl)))
        hfirstj hsecondk
  · rcases hxk' with hrootk | hfirstk | hsecondk
    · exact F.root_not_mem_piece k _ (hrootk ▸ hsecondj)
    · exact (Set.disjoint_left.mp
        (F.parent_pieces_disjoint hjk (Or.inr rfl) (Or.inl rfl)))
        hsecondj hfirstk
    · exact (Set.disjoint_left.mp
        (F.parent_pieces_disjoint hjk (Or.inr rfl) (Or.inr rfl)))
        hsecondj hsecondk

/-- The two child indices used by one parent branch. -/
def childPair (j : Fin a) : Finset (Fin 3) :=
  {F.child (firstConnector j), F.child (secondConnector j)}

private theorem childPair_card (j : Fin a) :
    2 ≤ (F.childPair j).card := by
  have hne : F.child (firstConnector j) ≠
      F.child (secondConnector j) := F.different_children j
  simp [childPair, hne]

/-- Any two parent branches use a common child. -/
theorem common_child (j k : Fin a) :
    ∃ q r : Fin (2 * a),
      (q = firstConnector j ∨ q = secondConnector j) ∧
      (r = firstConnector k ∨ r = secondConnector k) ∧
      F.child q = F.child r := by
  obtain ⟨h, hhj, hhk⟩ :=
    two_children_intersect (F.childPair j) (F.childPair k)
      (F.childPair_card j) (F.childPair_card k)
  have hj : h = F.child (firstConnector j) ∨
      h = F.child (secondConnector j) := by
    simpa [childPair] using hhj
  have hk : h = F.child (firstConnector k) ∨
      h = F.child (secondConnector k) := by
    simpa [childPair] using hhk
  rcases hj with hj | hj <;> rcases hk with hk | hk
  · exact ⟨firstConnector j, firstConnector k,
      Or.inl rfl, Or.inl rfl, hj.symm.trans hk⟩
  · exact ⟨firstConnector j, secondConnector k,
      Or.inl rfl, Or.inr rfl, hj.symm.trans hk⟩
  · exact ⟨secondConnector j, firstConnector k,
      Or.inr rfl, Or.inl rfl, hj.symm.trans hk⟩
  · exact ⟨secondConnector j, secondConnector k,
      Or.inr rfl, Or.inr rfl, hj.symm.trans hk⟩

private theorem selected_branch_subset_parent
    (j : Fin a) (q : Fin (2 * a))
    (hq : q = firstConnector j ∨ q = secondConnector j) :
    (F.childModel (F.child q)).branch (F.slot q) ⊆
      F.parentBranch j := by
  intro x hx
  have hxPiece : x ∈ F.piece q := Or.inr hx
  rcases hq with rfl | rfl
  · exact Set.mem_insert_of_mem _ (Or.inl hxPiece)
  · exact Set.mem_insert_of_mem _ (Or.inr hxPiece)

/-- A common child supplies an edge between every two distinct parent
branches. -/
theorem parentBranch_adjacent {j k : Fin a} (hjk : j ≠ k) :
    ∃ x ∈ F.parentBranch j, ∃ y ∈ F.parentBranch k,
      G.Adj x y := by
  obtain ⟨q, r, hq, hr, hchild⟩ := F.common_child j k
  have hqr : q ≠ r := connector_ne_of_parent_ne hjk hq hr
  have hslot : F.slot q ≠ F.slot r := by
    intro hs
    apply hqr
    apply F.assignment.injective
    exact Prod.ext hchild hs
  have hadj : (SimpleGraph.completeGraph (Fin c)).Adj
      (F.slot q) (F.slot r) := by
    simpa using hslot
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    (F.childModel (F.child q)).adjacent hadj
  have hy' : y ∈ (F.childModel (F.child r)).branch (F.slot r) := by
    rw [← hchild]
    exact hy
  exact ⟨x, F.selected_branch_subset_parent j q hq hx,
    y, F.selected_branch_subset_parent k r hr hy', hxy⟩

/-- The assembled branch family is a rooted clique minor. -/
def toRootedMinorModel :
    RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G F.root where
  branch := F.parentBranch
  connected := F.parentBranch_connected
  disjoint := by
    intro j k hjk
    exact F.parentBranch_disjoint hjk
  adjacent := by
    intro j k hjk
    exact F.parentBranch_adjacent (by simpa using hjk)
  root_mem := by
    intro j
    exact Set.mem_insert _ _
end ThreeChildFrame


/-- Rerouting through a disjoint new child preserves the exact
intersection of an earlier rooted model with the linkage. -/
theorem exact_model_intersection_preserved
    {V : Type*} {G : SimpleGraph V} {c j : ℕ}
    {P : IndexedPairs (Fin j) V} {root : Fin c → V}
    (M : RootedMinorModel (SimpleGraph.completeGraph (Fin c)) G root)
    (L L' : IndexedLinkage G P) (A B : Set V)
    (hM : M.toMinorModel.vertices ⊆ A)
    (hAB : Disjoint A B)
    (hOld : M.toMinorModel.vertices ∩ L.vertices = Set.range root)
    (hNew : L'.vertices ⊆ L.vertices ∪ B)
    (hterminal : Set.range root ⊆ P.allTerminals) :
    M.toMinorModel.vertices ∩ L'.vertices = Set.range root := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxM, hxL'⟩
    rcases hNew hxL' with hxL | hxB
    · rw [← hOld]
      exact ⟨hxM, hxL⟩
    · exact False.elim
        ((Set.disjoint_left.mp hAB) (hM hxM) hxB)
  · intro x hx
    obtain ⟨i, rfl⟩ := hx
    refine ⟨Set.mem_iUnion.mpr ⟨i, M.root_mem i⟩, ?_⟩
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp (hterminal ⟨i, rfl⟩)
    exact L'.path_subset_vertices q
      (L'.terminal_subset_path q hq)

/-- Successive rerouting through three disjoint woven children gives
three simultaneous rooted child models. Their exact intersections
with the final linkage are preserved. -/
theorem reroute_three_children
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {c b j : ℕ} (H : Fin 3 → Finset V)
    (hH : Pairwise fun k l : Fin 3 =>
      Disjoint (H k : Set V) (H l : Set V))
    (hW : ∀ k, Woven (G.induce (H k : Set V)) c b)
    (childRoot : Fin 3 → Fin c → V)
    (hroot : ∀ k, Function.Injective (childRoot k))
    (hrootH : ∀ k u, childRoot k u ∈ H k)
    {P : IndexedPairs (Fin j) V} (L : IndexedLinkage G P)
    (hj : j ≤ b)
    (hterminal : ∀ k, Set.range (childRoot k) ⊆ P.allTerminals) :
    ∃ (M : ∀ k : Fin 3,
        RootedMinorModel (SimpleGraph.completeGraph (Fin c)) G (childRoot k))
      (L' : IndexedLinkage G P),
      (∀ k, (M k).toMinorModel.vertices ⊆ (H k : Set V)) ∧
      (∀ k, (M k).toMinorModel.vertices ∩ L'.vertices =
        Set.range (childRoot k)) ∧
      L'.vertices ⊆ L.vertices ∪ ⋃ k, (H k : Set V) := by
  obtain ⟨M0, L1, hM0, hL1, hE0⟩ :=
    reroute_linkage_through_child_exact (H 0) (hW 0)
      (childRoot 0) (hroot 0) (hrootH 0) L hj (hterminal 0)
  obtain ⟨M1, L2, hM1, hL2, hE1⟩ :=
    reroute_linkage_through_child_exact (H 1) (hW 1)
      (childRoot 1) (hroot 1) (hrootH 1) L1 hj (hterminal 1)
  have hE0_2 : M0.toMinorModel.vertices ∩ L2.vertices =
      Set.range (childRoot 0) :=
    exact_model_intersection_preserved M0 L1 L2
      (H 0 : Set V) (H 1 : Set V) hM0
      (hH (by decide : (0 : Fin 3) ≠ 1))
      hE0 hL2 (hterminal 0)
  obtain ⟨M2, L3, hM2, hL3, hE2⟩ :=
    reroute_linkage_through_child_exact (H 2) (hW 2)
      (childRoot 2) (hroot 2) (hrootH 2) L2 hj (hterminal 2)
  have hE0_3 : M0.toMinorModel.vertices ∩ L3.vertices =
      Set.range (childRoot 0) :=
    exact_model_intersection_preserved M0 L2 L3
      (H 0 : Set V) (H 2 : Set V) hM0
      (hH (by decide : (0 : Fin 3) ≠ 2))
      hE0_2 hL3 (hterminal 0)
  have hE1_3 : M1.toMinorModel.vertices ∩ L3.vertices =
      Set.range (childRoot 1) :=
    exact_model_intersection_preserved M1 L2 L3
      (H 1 : Set V) (H 2 : Set V) hM1
      (hH (by decide : (1 : Fin 3) ≠ 2))
      hE1 hL3 (hterminal 1)
  let M : ∀ k : Fin 3,
      RootedMinorModel (SimpleGraph.completeGraph (Fin c)) G
        (childRoot k) :=
    Fin.cases M0 (Fin.cases M1 (Fin.cases M2 (fun i : Fin 0 => i.elim0)))
  refine ⟨M, L3, ?_, ?_, ?_⟩
  · intro k
    exact Fin.cases hM0 (Fin.cases hM1 (Fin.cases hM2 (fun i : Fin 0 => i.elim0))) k
  · intro k
    exact Fin.cases hE0_3 (Fin.cases hE1_3 (Fin.cases hE2 (fun i : Fin 0 => i.elim0))) k
  · intro x hx3
    rcases hL3 hx3 with hx2 | hxH2
    · rcases hL2 hx2 with hx1 | hxH1
      · rcases hL1 hx1 with hx0 | hxH0
        · exact Or.inl hx0
        · exact Or.inr (Set.mem_iUnion.mpr ⟨(0 : Fin 3), hxH0⟩)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨(1 : Fin 3), hxH1⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨(2 : Fin 3), hxH2⟩)


/-- Three pairwise disjoint woven children assemble into a rooted
clique model once two connector paths from each original root have
targets in different children. The assignment bijection enumerates all
child roots. -/
theorem rooted_minor_of_three_woven_children
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a c b : ℕ}
    (H : Fin 3 → Finset V)
    (hH : Pairwise fun k l : Fin 3 =>
      Disjoint (H k : Set V) (H l : Set V))
    (hW : ∀ k, Woven (G.induce (H k : Set V)) c b)
    (root : Fin a → V) (hroot : Function.Injective root)
    (childRoot : Fin 3 → Fin c → V)
    (hchildRoot : ∀ k, Function.Injective (childRoot k))
    (hchildRootH : ∀ k u, childRoot k u ∈ H k)
    (assignment : Fin (2 * a) ≃ Fin 3 × Fin c)
    (start : Fin (2 * a) → V)
    (L : IndexedLinkage G
      ⟨start, fun q =>
        childRoot (assignment q).1 (assignment q).2⟩)
    (hbudget : 2 * a ≤ b)
    (hrootOutsideL : ∀ i, root i ∉ L.vertices)
    (hrootOutsideH : ∀ i k, root i ∉ H k)
    (hfirst : ∀ i, G.Adj (root i) (start (firstConnector i)))
    (hsecond : ∀ i, G.Adj (root i) (start (secondConnector i)))
    (hdifferent : ∀ i,
      (assignment (firstConnector i)).1 ≠
        (assignment (secondConnector i)).1) :
    HasRootedCliqueMinor G root := by
  let P : IndexedPairs (Fin (2 * a)) V :=
    ⟨start, fun q => childRoot (assignment q).1 (assignment q).2⟩
  have hterm (k : Fin 3) : Set.range (childRoot k) ⊆ P.allTerminals := by
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    let q : Fin (2 * a) := assignment.symm (k, u)
    have hfinish : P.finish q = childRoot k u := by
      simp [P, q]
    exact Set.mem_iUnion.mpr ⟨q, Or.inr hfinish.symm⟩
  obtain ⟨M, L', hMsupport, hExact, hLsupport⟩ :=
    reroute_three_children H hH hW childRoot
      hchildRoot hchildRootH L hbudget hterm
  have hrootOutsideL' (i : Fin a) : root i ∉ L'.vertices := by
    intro hi
    rcases hLsupport hi with hiL | hiH
    · exact hrootOutsideL i hiL
    · obtain ⟨k, hik⟩ := Set.mem_iUnion.mp hiH
      exact hrootOutsideH i k hik
  have hrootOutsideM (i : Fin a) (k : Fin 3) :
      root i ∉ (M k).toMinorModel.vertices := by
    intro hi
    exact hrootOutsideH i k (hMsupport k hi)
  have hMdis : Pairwise fun k l : Fin 3 =>
      Disjoint (M k).toMinorModel.vertices
        (M l).toMinorModel.vertices := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro x hxk hxl
    exact (Set.disjoint_left.mp (hH hkl))
      (hMsupport k hxk) (hMsupport l hxl)
  let F : ThreeChildFrame G a c := {
    root := root
    root_injective := hroot
    childRoot := childRoot
    childModel := M
    assignment := assignment
    start := start
    linkage := L'
    adjacent_first := hfirst
    adjacent_second := hsecond
    root_outside_linkage := hrootOutsideL'
    root_outside_child := hrootOutsideM
    children_disjoint := hMdis
    exact_child_intersection := hExact
    different_children := hdifferent
  }
  exact ⟨F.toRootedMinorModel⟩
end Woven
end HadwigerLean
