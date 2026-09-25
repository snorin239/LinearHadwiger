import HadwigerLean.Graph.RootedDensity.HighConnectivity
import HadwigerLean.Graph.NeighborProxies
import Mathlib.Combinatorics.Hall.Basic

/-! Disjoint two-edge attachments for the low-connectivity branch of Appendix F. -/

namespace HadwigerLean.RootedDensity

universe u v

private def edgePath {V : Type v} {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) : G.Path a b :=
  ⟨SimpleGraph.Walk.cons hab SimpleGraph.Walk.nil, by
    simp [SimpleGraph.Walk.cons_isPath_iff, G.ne_of_adj hab]⟩

private theorem edgePath_vertices {V : Type v} {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) : pathVertexSet (edgePath hab) = {a, b} := by
  ext x
  simp [pathVertexSet, edgePath]

/-- Pairwise disjoint adjacent terminal pairs give an indexed one-edge linkage. -/
def edgeLinkage_of_disjointTerminals
    {I : Type u} {V : Type v} {G : SimpleGraph V}
    (P : IndexedPairs I V) (hdisj : P.DisjointTerminals)
    (hadj : ∀ i, G.Adj (P.start i) (P.finish i)) :
    IndexedLinkage G P where
  path := fun i => edgePath (hadj i)
  disjoint := by
    intro i j hij
    simpa only [edgePath_vertices, IndexedPairs.terminals] using hdisj hij

/-- Distinct one-edge root-to-proxy paths outside the model attach an
induced target minor, with each proxy adjacent to its assigned branch. -/
theorem rootedMinor_of_induced_minor_and_distinct_proxies
    {W : Type u} {V : Type v} {H : SimpleGraph W} {G : SimpleGraph V}
    (S : Set V) (M : MinorModel H (G.induce S))
    (r p : W → ↥(Sᶜ : Set V))
    (hr : Function.Injective r) (hp : Function.Injective p)
    (hrp : Disjoint (Set.range r) (Set.range p))
    (hrpEdge : ∀ i, G.Adj (r i : V) (p i : V))
    (hattach : ∀ i, ∃ x ∈ M.branch i, G.Adj (x : V) (p i : V)) :
    Nonempty (RootedMinorModel H G (fun i => (r i : V))) := by
  let P : IndexedPairs W ↥(Sᶜ : Set V) := ⟨r, p⟩
  have hterm : P.DisjointTerminals := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    change x = r i ∨ x = p i at hxi
    change x = r j ∨ x = p j at hxj
    rcases hxi with hxi | hxi <;> rcases hxj with hxj | hxj
    · exact hij (hr (hxi.symm.trans hxj))
    · exact (Set.disjoint_left.mp hrp) ⟨i, hxi.symm⟩ ⟨j, hxj.symm⟩
    · exact (Set.disjoint_left.mp hrp) ⟨j, hxj.symm⟩ ⟨i, hxi.symm⟩
    · exact hij (hp (hxi.symm.trans hxj))
  have hadj (i : W) : (G.induce Sᶜ).Adj (r i) (p i) := hrpEdge i
  let L := edgeLinkage_of_disjointTerminals P hterm hadj
  exact rootedMinor_of_induced_minor_and_complement_linkage S M P L
    (fun i => (r i : V)) (fun _ => rfl) hattach

/-- If every root/branch-representative pair has at least `h` available
common neighbors outside the target model and all prescribed roots, Hall's
theorem gives disjoint two-edge attachments for all target labels. -/
theorem rootedMinor_of_common_neighbor_candidates
    {W : Type u} {V : Type v} [Fintype W] [Fintype V] [DecidableEq V]
    (H : SimpleGraph W) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (M : MinorModel H (G.induce (S : Set V)))
    (root : W → V) (hroot : Function.Injective root)
    (hrootS : ∀ i, root i ∉ S)
    (hcand : ∀ i : W,
      Fintype.card W ≤
        ((G.neighborFinset (root i) ∩
          G.neighborFinset ((M.representative i : ↥(S : Set V)) : V)) \
          (S ∪ Finset.univ.image root)).card) :
    Nonempty (RootedMinorModel H G root) := by
  classical
  let h := Fintype.card W
  let e : W ≃ Fin h := Fintype.equivFin W
  let U : Finset V := S ∪ Finset.univ.image root
  let C : Fin h → Finset V := fun i =>
    (G.neighborFinset (root (e.symm i)) ∩
      G.neighborFinset ((M.representative (e.symm i) : ↥(S : Set V)) : V)) \ U
  have hC (i : Fin h) : h ≤ (C i).card := hcand (e.symm i)
  have hhall : ∀ T : Finset (Fin h), T.card ≤ (T.biUnion C).card := by
    intro T
    by_cases hT : T.Nonempty
    · obtain ⟨i, hi⟩ := hT
      calc
        T.card ≤ h := by simpa using Finset.card_le_univ T
        _ ≤ (C i).card := hC i
        _ ≤ (T.biUnion C).card :=
          Finset.card_le_card (by
            intro x hx
            exact Finset.mem_biUnion.mpr ⟨i, hi, hx⟩)
    · simp [Finset.not_nonempty_iff_eq_empty.mp hT]
  obtain ⟨q, hqinj, hqC⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective C).mp hhall
  have hqData (i : Fin h) :
      q i ∈ G.neighborFinset (root (e.symm i)) ∧
      q i ∈ G.neighborFinset ((M.representative (e.symm i) : ↥(S : Set V)) : V) ∧
      q i ∉ U := by
    have hi := Finset.mem_sdiff.mp (hqC i)
    exact ⟨(Finset.mem_inter.mp hi.1).1, (Finset.mem_inter.mp hi.1).2, hi.2⟩
  have hqS (i : Fin h) : q i ∉ S := by
    exact fun hi => (hqData i).2.2 (Finset.mem_union.mpr (Or.inl hi))
  let r : W → ↥((S : Set V)ᶜ) := fun i => ⟨root i, hrootS i⟩
  let p : W → ↥((S : Set V)ᶜ) := fun i => ⟨q (e i), hqS (e i)⟩
  have hr : Function.Injective r := by
    intro i j hij
    exact hroot (congrArg Subtype.val hij)
  have hp : Function.Injective p := by
    intro i j hij
    exact e.injective (hqinj (congrArg Subtype.val hij))
  have hrp : Disjoint (Set.range r) (Set.range p) := by
    apply Set.disjoint_left.mpr
    intro z hzR hzP
    obtain ⟨i, rfl⟩ := hzR
    obtain ⟨j, hj⟩ := hzP
    have hq : q (e j) = root i := congrArg Subtype.val hj
    exact (hqData (e j)).2.2 (Finset.mem_union.mpr
      (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hq.symm⟩)))
  have hrootEdge (i : W) : G.Adj (r i : V) (p i : V) := by
    exact (G.mem_neighborFinset _ _).mp (by simpa [r, p, e.symm_apply_apply] using
      (hqData (e i)).1)
  have hattach (i : W) : ∃ x ∈ M.branch i, G.Adj (x : V) (p i : V) := by
    refine ⟨M.representative i, M.representative_mem i, ?_⟩
    exact (G.mem_neighborFinset _ _).mp (by simpa [p, e.symm_apply_apply] using
      (hqData (e i)).2.1)
  exact rootedMinor_of_induced_minor_and_distinct_proxies
    (S : Set V) M r p hr hp hrp hrootEdge hattach


/-- A fixed induced target minor with many available common neighbors for
every root/branch vertex is universal at the prescribed root set. -/
theorem universalAt_of_minor_common_neighbor_candidates
    {W : Type u} {V : Type v} [Fintype W] [Fintype V] [DecidableEq V]
    (H : SimpleGraph W) (G : SimpleGraph V) [DecidableRel G.Adj]
    (X S : Finset V) (hXS : Disjoint X S)
    (M : MinorModel H (G.induce (S : Set V)))
    (hcand : ∀ x ∈ X, ∀ y ∈ S,
      Fintype.card W ≤
        ((G.neighborFinset x ∩ G.neighborFinset y) \ (S ∪ X)).card) :
    UniversalAt G H X := by
  classical
  intro Y root hroot hrange
  have hrootS (i : ↥(Y : Set W)) : root i ∉ S := by
    have hi : root i ∈ X := by
      have hset : root i ∈ (X : Set V) := by
        rw [← hrange]
        exact ⟨i, rfl⟩
      exact hset
    exact Finset.disjoint_left.mp hXS hi
  have hrootImage : Finset.univ.image root = X := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      have hi : root i ∈ (X : Set V) := by
        rw [← hrange]
        exact ⟨i, rfl⟩
      exact hi
    · intro hx
      have hset : x ∈ Set.range root := by
        rw [hrange]
        exact hx
      obtain ⟨i, rfl⟩ := hset
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hY : Fintype.card ↥(Y : Set W) ≤ Fintype.card W :=
    Fintype.card_subtype_le _
  have hC (i : ↥(Y : Set W)) :
      Fintype.card ↥(Y : Set W) ≤
        ((G.neighborFinset (root i) ∩
          G.neighborFinset
            (((minorModel_restrictTarget M (Y : Set W)).representative i :
              ↥(S : Set V)) : V)) \
          (S ∪ Finset.univ.image root)).card := by
    have hxi : root i ∈ X := by
      have hi : root i ∈ (X : Set V) := by
        rw [← hrange]
        exact ⟨i, rfl⟩
      exact hi
    have hyi : (((minorModel_restrictTarget M (Y : Set W)).representative i :
        ↥(S : Set V)) : V) ∈ S :=
      ((minorModel_restrictTarget M (Y : Set W)).representative i :
        ↥(S : Set V)).property
    rw [hrootImage]
    exact hY.trans (hcand (root i) hxi _ hyi)
  exact rootedMinor_of_common_neighbor_candidates
    (H.induce (Y : Set W)) G S (minorModel_restrictTarget M (Y : Set W))
    root hroot hrootS hC
end HadwigerLean.RootedDensity


