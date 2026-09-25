import HadwigerLean.Graph.RootedDensity.AttachLinked
import HadwigerLean.Graph.RootedDensity.Definitions
import HadwigerLean.Graph.NeighborProxies

/-! The high-connectivity branch of the Appendix F attachment argument. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- A minor in a reserved induced set can be attached to prescribed roots
outside that set if connectivity survives its deletion and every branch has
enough outside neighbors for distinct proxies. -/
theorem rootedMinor_of_induced_minor_high_connectivity
    {W : Type u} {V : Type v} [Fintype W] [Fintype V]
    [DecidableEq V] (H : SimpleGraph W) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (M : MinorModel H (G.induce (S : Set V)))
    (root : W → V) (hroot : Function.Injective root)
    (hrootS : ∀ i, root i ∉ S)
    (k : ℕ) (hconn : VertexConnected G k)
    (hk : S.card + 16 * Fintype.card W ≤ k)
    (hdegree : ∀ x ∈ S, S.card + 2 * Fintype.card W ≤ G.degree x) :
    Nonempty (RootedMinorModel H G root) := by
  classical
  let h := Fintype.card W
  let e : W ≃ Fin h := Fintype.equivFin W
  let U : Finset V := S ∪ Finset.univ.image root
  have hU : U.card ≤ S.card + h := by
    calc
      U.card ≤ S.card + (Finset.univ.image root).card := Finset.card_union_le _ _
      _ ≤ S.card + h := by
        exact Nat.add_le_add_left Finset.card_image_le _
  let rep (i : W) : ↥(M.branch i) := Classical.choice (M.connected i).nonempty
  let role : Fin h → V := fun i => (((rep (e.symm i) : ↥(S : Set V)) : V))
  have hrole (i : Fin h) : role i ∈ S := by
    exact (rep (e.symm i) : ↥(S : Set V)).property
  obtain ⟨q, hqinj, hqadj, hqU⟩ :=
    exists_distinct_neighbor_proxies_of_candidates G h (fun i => (role i : V)) U (by
      intro i
      have hd := hdegree (role i) (hrole i)
      have hcut := Finset.card_le_card_sdiff_add_card
        (s := G.neighborFinset (role i)) (t := U)
      have hd' : S.card + 2 * h ≤ (G.neighborFinset (role i)).card := by
        simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hd
      omega)
  have hqS (i : Fin h) : q i ∉ S := by
    exact fun hi => hqU i (Finset.mem_union.mpr (Or.inl hi))
  have hqroot (i j : Fin h) : q i ≠ root (e.symm j) := by
    intro heq
    apply hqU i
    apply Finset.mem_union.mpr
    right
    exact Finset.mem_image.mpr ⟨e.symm j, Finset.mem_univ _, heq.symm⟩
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
    exact hqroot (e j) (e i) (by simpa using hq)
  have hattach (i : W) : ∃ x ∈ M.branch i, G.Adj (x : V) (p i : V) := by
    let x : ↥(M.branch i) := rep i
    refine ⟨x, x.property, ?_⟩
    have h := hqadj (e i)
    change G.Adj (rep (e.symm (e i))) (q (e i)) at h
    rw [e.symm_apply_apply] at h
    exact h
  have hcomp : VertexConnected (G.induce (S : Set V)ᶜ) (16 * h) :=
    hconn.induce_compl S (16 * h) hk
  have hlinked : Linkedness.KLinked (G.induce (S : Set V)ᶜ) h :=
    Linkedness.kLinked_of_sixteen_mul_vertexConnected _ h hcomp
  exact rootedMinor_of_induced_minor_and_linked_complement
    (S : Set V) M r p hr hp hrp hattach hlinked


/-- Restrict the target labels of a minor model to an induced subgraph. -/
def minorModel_restrictTarget
    {W : Type u} {V : Type v} {H : SimpleGraph W} {G : SimpleGraph V}
    (M : MinorModel H G) (Y : Set W) : MinorModel (H.induce Y) G where
  branch := fun i => M.branch i
  connected := fun i => M.connected i
  disjoint := by
    intro i j hij
    apply M.disjoint
    exact fun heq => hij (Subtype.ext heq)
  adjacent := by
    intro i j hij
    exact M.adjacent hij

/-- One reserved minor supports every partial rooted target whose roots
avoid the reserve, provided connectivity and degree pay for its deletion. -/
theorem universalAt_of_induced_minor_high_connectivity
    {W : Type u} {V : Type v} [Fintype W] [Fintype V]
    [DecidableEq V] (H : SimpleGraph W) (G : SimpleGraph V) [DecidableRel G.Adj]
    (X S : Finset V) (hXS : Disjoint X S)
    (M : MinorModel H (G.induce (S : Set V)))
    (k : ℕ) (hconn : VertexConnected G k)
    (hk : S.card + 16 * Fintype.card W ≤ k)
    (hdegree : ∀ x ∈ S, S.card + 2 * Fintype.card W ≤ G.degree x) :
    UniversalAt G H X := by
  classical
  intro Y root hroot hrange
  have hrootS (i : ↥(Y : Set W)) : root i ∉ S := by
    have hmem : root i ∈ X := by
      have hi : root i ∈ (X : Set V) := by
        rw [← hrange]
        exact ⟨i, rfl⟩
      exact hi
    exact Finset.disjoint_left.mp hXS hmem
  have hY : Fintype.card ↥(Y : Set W) ≤ Fintype.card W := by
    exact Fintype.card_subtype_le _
  have hkY : S.card + 16 * Fintype.card ↥(Y : Set W) ≤ k := by omega
  have hdY : ∀ x ∈ S, S.card + 2 * Fintype.card ↥(Y : Set W) ≤ G.degree x := by
    intro x hx
    have hd := hdegree x hx
    omega
  exact rootedMinor_of_induced_minor_high_connectivity
    (H.induce (Y : Set W)) G S (minorModel_restrictTarget M (Y : Set W))
    root hroot hrootS k hconn hkY hdY
end HadwigerLean.RootedDensity











