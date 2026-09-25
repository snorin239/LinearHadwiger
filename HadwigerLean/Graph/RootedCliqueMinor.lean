import HadwigerLean.Graph.RootedMinor
import HadwigerLean.Graph.VertexConnectivity
import HadwigerLean.Graph.IndexedLinkage
import HadwigerLean.Graph.ConnectivityMenger
import Mathlib.Data.Fintype.EquivFin
import HadwigerLean.Graph.Contraction

/-!
# Rooted clique minors

The attached model is the output of the separator dichotomy in Appendix B:
its branches avoid all prescribed roots, and each branch has an edge to its
assigned root. Adding those roots yields a rooted clique minor.
-/

namespace HadwigerLean

universe v

/-- A clique model outside the roots, with a distinct root attached by an edge
to each branch. -/
structure RootAttachedCliqueModel {V : Type v} (G : SimpleGraph V)
    {r : ℕ} (root : Fin r → V) where
  branch : Fin r → Set V
  root_injective : Function.Injective root
  connected : ∀ i, (G.induce (branch i)).Connected
  disjoint : Pairwise fun i j => Disjoint (branch i) (branch j)
  avoids_roots : ∀ i j, root j ∉ branch i
  adjacent : ∀ {i j}, i ≠ j →
    ∃ x ∈ branch i, ∃ y ∈ branch j, G.Adj x y
  attached : ∀ i, ∃ x ∈ branch i, G.Adj (root i) x

namespace RootAttachedCliqueModel

variable {V : Type v} {G : SimpleGraph V} {r : ℕ}
  {root : Fin r → V}

/-- Add each assigned root to its attached branch. -/
def toRootedMinor (M : RootAttachedCliqueModel G root) :
    RootedMinorModel (SimpleGraph.completeGraph (Fin r)) G root where
  branch := fun i => insert (root i) (M.branch i)
  connected := by
    intro i
    obtain ⟨x, hx, hrx⟩ := M.attached i
    have hs : (G.induce ({root i} : Set V)).Preconnected := by simp
    have ht : (G.induce (M.branch i)).Preconnected := (M.connected i).preconnected
    have hc := G.connected_induce_union hs ht (by simp : root i ∈ ({root i} : Set V)) hx hrx
    simpa only [Set.singleton_union] using hc
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    rcases Set.mem_insert_iff.mp hxi with hxi | hxi
    · subst x
      rcases Set.mem_insert_iff.mp hxj with hxj | hxj
      · exact hij (M.root_injective hxj)
      · exact M.avoids_roots j i hxj
    · rcases Set.mem_insert_iff.mp hxj with hxj | hxj
      · subst x
        exact M.avoids_roots i j hxi
      · exact (Set.disjoint_left.mp (M.disjoint hij)) hxi hxj
  adjacent := by
    intro i j hij
    obtain ⟨x, hx, y, hy, hxy⟩ := M.adjacent hij
    exact ⟨x, Set.mem_insert_iff.mpr (Or.inr hx), y, Set.mem_insert_iff.mpr (Or.inr hy), hxy⟩
  root_mem := fun i => Set.mem_insert (root i) (M.branch i)

/-- An attached model certifies the desired rooted clique minor. -/
theorem hasRootedCliqueMinor (M : RootAttachedCliqueModel G root) :
    HasRootedCliqueMinor G root :=
  ⟨M.toRootedMinor⟩

end RootAttachedCliqueModel

end HadwigerLean

namespace HadwigerLean

universe v

/-- Add every missing edge within the prescribed set of roots. -/
def completeRoots {V : Type v} (G : SimpleGraph V) (R : Set V) :
    SimpleGraph V where
  Adj x y := G.Adj x y ∨ (x ∈ R ∧ y ∈ R ∧ x ≠ y)
  symm := by
    constructor
    intro x y h
    rcases h with h | ⟨hx, hy, hne⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hy, hx, hne.symm⟩
  loopless := by
    constructor
    intro x h
    rcases h with h | h
    · exact G.irrefl h
    · exact h.2.2 rfl

namespace completeRoots

variable {V : Type v} {G : SimpleGraph V} {R : Set V}

theorem supergraph : G ≤ completeRoots G R :=
  fun _ _ h => Or.inl h

theorem adj_of_roots {x y : V} (hx : x ∈ R) (hy : y ∈ R)
    (hne : x ≠ y) : (completeRoots G R).Adj x y :=
  Or.inr ⟨hx, hy, hne⟩

theorem adj_of_not_both_roots {x y : V}
    (h : (completeRoots G R).Adj x y)
    (hn : ¬(x ∈ R ∧ y ∈ R)) : G.Adj x y := by
  rcases h with h | h
  · exact h
  · exact (hn ⟨h.1, h.2.1⟩).elim

end completeRoots

/-- Completing edges inside R does not alter the induced graph on a set
which avoids R. -/
theorem completeRoots_induce_eq_of_disjoint (B : Set V) (hBR : Disjoint B R) :
    (completeRoots G R).induce B = G.induce B := by
  ext x y
  constructor
  · intro hxy
    change G.Adj x.1 y.1 ∨
      (x.1 ∈ R ∧ y.1 ∈ R ∧ x.1 ≠ y.1) at hxy
    rcases hxy with hxy | hxy
    · exact hxy
    · exact False.elim
        ((Set.disjoint_left.mp hBR) x.property hxy.1)
  · intro hxy
    exact Or.inl hxy

/-- A clique-model branch avoiding the roots is already connected by
original graph edges. -/
theorem cliqueModel_branch_connected_of_avoids_roots
    {V : Type v} {G : SimpleGraph V} {r : ℕ}
    {root : Fin r → V}
    (M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots G (Set.range root)))
    (i : Fin (2 * r))
    (havoid : Disjoint (M.branch i) (Set.range root)) :
    (G.induce (M.branch i)).Connected := by
  rw [← completeRoots_induce_eq_of_disjoint (G := G)
    (R := Set.range root) (M.branch i) havoid]
  exact M.connected i

/-- A model edge from a branch avoiding the roots is an actual edge of
G, since completed edges have both ends at roots. -/
theorem cliqueModel_adjacent_of_avoids_roots
    {V : Type v} {G : SimpleGraph V} {r : ℕ}
    {root : Fin r → V}
    (M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots G (Set.range root)))
    {i j : Fin (2 * r)} (hij : i ≠ j)
    (havoid : Disjoint (M.branch i) (Set.range root)) :
    ∃ x ∈ M.branch i, ∃ y ∈ M.branch j, G.Adj x y := by
  obtain ⟨x, hx, y, hy, hxy⟩ := M.adjacent hij
  refine ⟨x, hx, y, hy, ?_⟩
  apply completeRoots.adj_of_not_both_roots hxy
  intro hboth
  exact (Set.disjoint_left.mp havoid) hx hboth.1
/-- A non-singleton model branch with a vertex outside the roots has an
actual graph edge incident with that vertex. This is the edge contracted
in Appendix B's induction. -/
theorem cliqueModel_actual_edge_for_contraction
    {V : Type v} {G : SimpleGraph V} {r : ℕ}
    {root : Fin r → V}
    (M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots G (Set.range root)))
    (i : Fin (2 * r)) (u : V)
    (hu : u ∈ M.branch i) (huR : u ∉ Set.range root)
    (hother : ∃ v ∈ M.branch i, v ≠ u) :
    ∃ v ∈ M.branch i, G.Adj u v := by
  obtain ⟨v, hv, hne⟩ := hother
  let B := M.branch i
  haveI : Nontrivial B :=
    nontrivial_of_ne (⟨u, hu⟩ : B) (⟨v, hv⟩ : B)
      (by intro h; exact hne (congrArg Subtype.val h).symm)
  obtain ⟨w, huw⟩ := (M.connected i).preconnected.exists_adj_of_nontrivial
    (⟨u, hu⟩ : B)
  refine ⟨w.1, w.2, ?_⟩
  exact completeRoots.adj_of_not_both_roots huw (by
    intro h
    exact huR h.1)
/-- Among 2r disjoint clique-model branches, at least r avoid the r roots. -/
theorem exists_root_avoiding_branches
    {V : Type v} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r : ℕ}
    (root : Fin r → V)
    (M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots G (Set.range root))) :
    ∃ e : Fin r ↪ Fin (2 * r),
      ∀ i, Disjoint (M.branch (e i)) (Set.range root) := by
  classical
  let bad : Finset (Fin (2 * r)) :=
    Finset.univ.filter (fun i => ∃ j : Fin r, root j ∈ M.branch i)
  let good : Finset (Fin (2 * r)) :=
    Finset.univ.filter (fun i => ¬ ∃ j : Fin r, root j ∈ M.branch i)
  let f : bad → Fin r := fun i =>
    Classical.choose (Finset.mem_filter.mp i.2).2
  have hfmem : ∀ i : bad, root (f i) ∈ M.branch i.1 := fun i =>
    Classical.choose_spec (Finset.mem_filter.mp i.2).2
  have hfinj : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    exact (Set.disjoint_left.mp (M.disjoint hne))
      (hfmem i) (hij ▸ hfmem j)
  have hbad : bad.card ≤ r := by
    have h := Fintype.card_le_of_injective f hfinj
    simpa using h
  have hsplit : bad.card + good.card = 2 * r := by
    have h := (Finset.univ : Finset (Fin (2 * r))).card_filter_add_card_filter_not
      (fun i => ∃ j : Fin r, root j ∈ M.branch i)
    simpa [bad, good] using h
  have hgood : r ≤ good.card := by omega
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin r) (s := good) (by simpa using hgood)
  refine ⟨e, ?_⟩
  intro i
  have hi : e i ∈ good := he ⟨i, rfl⟩
  have hno : ¬ ∃ j : Fin r, root j ∈ M.branch (e i) :=
    (Finset.mem_filter.mp hi).2
  apply Set.disjoint_left.mpr
  intro x hx ⟨j, hj⟩
  subst x
  exact hno ⟨j, hx⟩
/-- A completed-root K_(2r) model contains an actual K_r model whose
branch sets all avoid the roots. -/
theorem exists_root_avoiding_clique_model
    {V : Type v} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r : ℕ}
    (root : Fin r → V)
    (M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots G (Set.range root))) :
    ∃ N : MinorModel (SimpleGraph.completeGraph (Fin r)) G,
      ∀ i, Disjoint (N.branch i) (Set.range root) := by
  obtain ⟨e, he⟩ := exists_root_avoiding_branches root M
  refine ⟨{
    branch := fun i => M.branch (e i)
    connected := fun i => cliqueModel_branch_connected_of_avoids_roots M (e i) (he i)
    disjoint := ?_
    adjacent := ?_
  }, he⟩
  · intro i j hij
    exact M.disjoint (e.injective.ne hij)
  · intro i j hij
    exact cliqueModel_adjacent_of_avoids_roots M (e.injective.ne hij) (he i)
/-- A separation of order below the number of distinct prescribed roots
cannot place all roots on one side and a vertex strictly on the other side
of an r-connected graph. -/
theorem no_small_root_separator {V : Type v} [Fintype V]
    {G : SimpleGraph V} {r : ℕ} (hconn : VertexConnected G r)
    (root : Fin r → V) (hroot : Function.Injective root)
    (S : VertexSeparation G)
    (hsmall : S.separatorFinset.card < r)
    (hleft : ∀ i, root i ∈ S.left) :
    ¬S.strictRight.Nonempty := by
  intro hright
  have hstrictLeft : S.strictLeft.Nonempty := by
    by_contra hnone
    have hsep : ∀ i, root i ∈ S.separatorFinset := by
      intro i
      apply (S.mem_separatorFinset (root i)).mpr
      refine ⟨hleft i, ?_⟩
      by_contra hnr
      exact hnone ⟨root i, hleft i, hnr⟩
    let f : Fin r → {x : V // x ∈ S.separatorFinset} :=
      fun i => ⟨root i, hsep i⟩
    have hf : Function.Injective f := by
      intro i j hij
      exact hroot (congrArg Subtype.val hij)
    have hcard := Fintype.card_le_of_injective f hf
    have hcard' : r ≤ S.separatorFinset.card := by simpa using hcard
    omega
  exact (S.not_two_strict_sides hconn hsmall) ⟨hstrictLeft, hright⟩

end HadwigerLean

namespace HadwigerLean

universe v

/-- The separator alternative in the rooted-clique-minor dichotomy. The
far-side branch refers to the original clique model in the graph with the
root set completed to a clique. -/
structure RootCliqueSeparatorOutcome {V : Type v} [Fintype V]
    (G : SimpleGraph V) {r : ℕ} (root : Fin r → V)
    (M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots G (Set.range root))) where
  sep : VertexSeparation G
  small : sep.separatorFinset.card < r
  roots_left : ∀ i, root i ∈ sep.left
  branch_right : ∃ i, M.branch i ⊆ sep.strictRight

/-- The separator alternative cannot occur in an r-connected graph. -/
theorem RootCliqueSeparatorOutcome.false_of_connected
    {V : Type v} [Fintype V] {G : SimpleGraph V} {r : ℕ}
    {root : Fin r → V} (hconn : VertexConnected G r)
    (hroot : Function.Injective root)
    {M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots G (Set.range root))}
    (O : RootCliqueSeparatorOutcome G root M) : False := by
  obtain ⟨i, hi⟩ := O.branch_right
  obtain ⟨x, hx⟩ := (M.connected i).nonempty
  exact (no_small_root_separator hconn root hroot O.sep
    O.small O.roots_left) ⟨x, hi hx⟩

/-- The separator dichotomy is the remaining substantive KR obligation:
an original clique model in the graph with completed roots either gives an
attached model or exhibits a smaller separator. -/
def RootCliqueSeparatorDichotomy {V : Type v} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ (root : Fin r → V), Function.Injective root →
    ∀ M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots G (Set.range root)),
      Nonempty (RootAttachedCliqueModel G root) ∨
        Nonempty (RootCliqueSeparatorOutcome G root M)

/-- Once the separator dichotomy is established, the connectivity hypothesis
eliminates its second alternative and yields the rooted clique minor. -/
theorem rootedCliqueMinor_of_dichotomy
    {V : Type v} [Fintype V] {G : SimpleGraph V} {r : ℕ}
    (hconn : VertexConnected G r) (hminor : HasCliqueMinor G (2 * r))
    (hD : RootCliqueSeparatorDichotomy G r)
    (root : Fin r → V) (hroot : Function.Injective root) :
    HasRootedCliqueMinor G root := by
  obtain ⟨M⟩ := hasCliqueMinor_mono
    (completeRoots.supergraph (G := G) (R := Set.range root)) hminor
  rcases hD root hroot M with hA | hO
  · obtain ⟨A⟩ := hA
    exact A.hasRootedCliqueMinor
  · obtain ⟨O⟩ := hO
    exact (O.false_of_connected hconn hroot).elim

end HadwigerLean

namespace HadwigerLean

universe v

/-- Disjoint root-to-clique paths themselves form the branch sets of a rooted
clique minor. The terminal clique may have additional unused vertices. -/
theorem rootedCliqueMinor_of_linkage_to_clique
    {V : Type v} {G : SimpleGraph V} {r : ℕ}
    {root : Fin r → V} {P : IndexedPairs (Fin r) V}
    (L : IndexedLinkage G P)
    (hstart : ∀ i, P.start i = root i)
    (hclique : ∀ {i j}, i ≠ j → G.Adj (P.finish i) (P.finish j)) :
    HasRootedCliqueMinor G root := by
  refine ⟨{
    branch := fun i => pathVertexSet (L.path i)
    connected := ?_
    disjoint := L.disjoint
    adjacent := ?_
    root_mem := ?_
  }⟩
  · intro i
    exact (L.path i : G.Walk (P.start i) (P.finish i)).connected_induce_support
  · intro i j hij
    exact ⟨P.finish i, pathVertexSet.finish_mem (L.path i),
      P.finish j, pathVertexSet.finish_mem (L.path j), hclique hij⟩
  · intro i
    exact (hstart i) ▸ pathVertexSet.start_mem (L.path i)


/-- In an r-connected graph, any actual clique of size at least r can be
linked to any prescribed r distinct roots, yielding a rooted clique minor. -/
theorem rootedCliqueMinor_of_connected_clique
    {V : Type v} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r : ℕ}
    (hconn : VertexConnected G r)
    (root : Fin r → V) (hroot : Function.Injective root)
    (Q : Finset V) (hQ : r ≤ Q.card)
    (hclique : ∀ ⦃u w : V⦄, u ∈ Q → w ∈ Q → u ≠ w → G.Adj u w) :
    HasRootedCliqueMinor G root := by
  classical
  let R : Finset V := Finset.univ.image root
  have hRcard : R.card = r := by
    simp [R, Finset.card_image_of_injective _ hroot]
  obtain ⟨P, L, hAB⟩ := hconn.exists_AB_linkage R Q
    (by omega) hQ
  have hstartInj : Function.Injective P.start := L.start_injective
  have hfinishInj : Function.Injective P.finish := L.finish_injective
  have hstartSubset : Finset.univ.image P.start ⊆ R := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hAB.1 i
  have hstartCard : (Finset.univ.image P.start).card = r := by
    simp [Finset.card_image_of_injective _ hstartInj]
  have hstartRange : Finset.univ.image P.start = R :=
    Finset.eq_of_subset_of_card_le hstartSubset (by omega)
  have hsurj : ∀ i : Fin r, ∃ j : Fin r, P.start j = root i := by
    intro i
    have hi : root i ∈ R := Finset.mem_image.mpr
      ⟨i, Finset.mem_univ _, rfl⟩
    rw [← hstartRange] at hi
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
    exact ⟨j, hj⟩
  let idx : Fin r → Fin r := fun i => Classical.choose (hsurj i)
  have hidx : ∀ i : Fin r, P.start (idx i) = root i := fun i =>
    Classical.choose_spec (hsurj i)
  have hidxInj : Function.Injective idx := by
    intro i j hij
    apply hroot
    calc
      root i = P.start (idx i) := (hidx i).symm
      _ = P.start (idx j) := by rw [hij]
      _ = root j := hidx j
  let emb : Fin r ↪ Fin r := ⟨idx, hidxInj⟩
  let P' := P.reindex emb
  let L' : IndexedLinkage G P' := L.reindex emb
  apply rootedCliqueMinor_of_linkage_to_clique L'
  · intro i
    exact hidx i
  · intro i j hij
    apply hclique
    · exact hAB.2 (emb i)
    · exact hAB.2 (emb j)
    · exact hfinishInj.ne (hidxInj.ne hij)
/-- Appendix B's final case: if every branch avoiding the roots is a
singleton, r-connectivity links the roots to an actual r-clique. -/
theorem rootedCliqueMinor_of_singleton_avoiding_branches
    {V : Type v} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r : ℕ}
    (hconn : VertexConnected G r)
    (root : Fin r → V) (hroot : Function.Injective root)
    (M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots G (Set.range root)))
    (hsingle : ∀ i : Fin (2 * r),
      Disjoint (M.branch i) (Set.range root) →
        ∃ x : V, M.branch i = {x}) :
    HasRootedCliqueMinor G root := by
  classical
  obtain ⟨e, he⟩ := exists_root_avoiding_branches root M
  let q : Fin r → V := fun i => M.representative (e i)
  have hqinj : Function.Injective q :=
    M.representative_injective.comp e.injective
  have hsingleton : ∀ i : Fin r, M.branch (e i) = {q i} := by
    intro i
    obtain ⟨x, hx⟩ := hsingle (e i) (he i)
    have hqx : q i = x := by
      have hmem := M.representative_mem (e i)
      simpa [q, hx] using hmem
    simpa [q, hqx] using hx
  let Q : Finset V := Finset.univ.image q
  have hQcard : Q.card = r := by
    simp [Q, Finset.card_image_of_injective _ hqinj]
  have hclique : ∀ ⦃u v : V⦄, u ∈ Q → v ∈ Q →
      u ≠ v → G.Adj u v := by
    intro u v hu hv huv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
    have hij : i ≠ j := by
      intro h
      exact huv (congrArg q h)
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      cliqueModel_adjacent_of_avoids_roots M (e.injective.ne hij) (he i)
    have hxi : x = q i := by simpa [hsingleton i] using hx
    have hyj : y = q j := by simpa [hsingleton j] using hy
    simpa [hxi, hyj] using hxy
  exact rootedCliqueMinor_of_connected_clique hconn root hroot Q
    (by omega) hclique

/-- If no model branch has an actual edge incident to a nonroot vertex,
then the root-free branches are singleton clique vertices and KR follows. -/
theorem rootedCliqueMinor_of_no_contractable_edge
    {V : Type v} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r : ℕ}
    (hconn : VertexConnected G r)
    (root : Fin r → V) (hroot : Function.Injective root)
    (M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots G (Set.range root)))
    (hnoedge : ∀ i : Fin (2 * r), ∀ u ∈ M.branch i,
      u ∉ Set.range root → ∀ v ∈ M.branch i, ¬G.Adj u v) :
    HasRootedCliqueMinor G root := by
  apply rootedCliqueMinor_of_singleton_avoiding_branches hconn root hroot M
  intro i havoid
  let u := M.representative i
  have hu : u ∈ M.branch i := M.representative_mem i
  have huR : u ∉ Set.range root := by
    intro h
    exact (Set.disjoint_left.mp havoid) hu h
  refine ⟨u, ?_⟩
  ext v
  constructor
  · intro hv
    by_contra hne
    obtain ⟨w, hw, huw⟩ := cliqueModel_actual_edge_for_contraction
      M i u hu huR ⟨v, hv, hne⟩
    exact hnoedge i u hu huR w hw huw
  · intro hv
    simpa using (hv : v = u) ▸ hu

/-- A map that sends each edge either to an edge or to a single vertex
preserves reachability. This permits branch-set contraction. -/
theorem reachable_of_adj_or_eq_map
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W)
    (hf : ∀ ⦃u v : V⦄, G.Adj u v → f u = f v ∨ H.Adj (f u) (f v))
    {u v : V} (hreach : G.Reachable u v) :
    H.Reachable (f u) (f v) := by
  obtain ⟨p⟩ := hreach
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj p ih =>
    rcases hf hadj with heq | hnew
    · simpa only [heq] using ih
    · exact hnew.reachable.trans ih

/-- A connected branch remains connected after a map that may collapse
edges but otherwise preserves them. -/
theorem connected_induce_image_of_adj_or_eq_map
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (B : Set V) (hB : (G.induce B).Connected)
    (f : V → W)
    (hmap : ∀ ⦃u v : V⦄, u ∈ B → v ∈ B → G.Adj u v →
      f u = f v ∨ H.Adj (f u) (f v)) :
    (H.induce (f '' B)).Connected := by
  let F : B → (f '' B) := fun u => ⟨f u.1, ⟨u.1, u.2, rfl⟩⟩
  have hF : ∀ ⦃u v : B⦄, (G.induce B).Adj u v →
      F u = F v ∨ (H.induce (f '' B)).Adj (F u) (F v) := by
    intro u v huv
    rcases hmap u.2 v.2 huv with heq | hadj
    · exact Or.inl (Subtype.ext heq)
    · exact Or.inr hadj
  haveI : Nonempty (f '' B) := by
    obtain ⟨u⟩ := hB.nonempty
    exact ⟨F u⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨u, hu, hux⟩ := x.2
  obtain ⟨v, hv, hvy⟩ := y.2
  have hr := reachable_of_adj_or_eq_map F hF
    (hB ⟨u, hu⟩ ⟨v, hv⟩)
  have hx : F ⟨u, hu⟩ = x := Subtype.ext hux
  have hy : F ⟨v, hv⟩ = y := Subtype.ext hvy
  simpa only [hx, hy] using hr

namespace ConnectedPartition

/-- The unique quotient block containing a vertex. -/
noncomputable def index {V I : Type*} {G : SimpleGraph V}
    (P : ConnectedPartition G I) (x : V) : I :=
  Classical.choose (P.cover x)

theorem index_mem {V I : Type*} {G : SimpleGraph V}
    (P : ConnectedPartition G I) (x : V) :
    x ∈ P.block (P.index x) := Classical.choose_spec (P.cover x)

/-- Quotienting either collapses an edge or maps it to an edge. -/
theorem index_adj_or_eq {V I : Type*} {G : SimpleGraph V}
    (P : ConnectedPartition G I) {x y : V} (hxy : G.Adj x y) :
    P.index x = P.index y ∨
      P.touchingQuotient.Adj (P.index x) (P.index y) := by
  by_cases heq : P.index x = P.index y
  · exact Or.inl heq
  · exact Or.inr ⟨heq, x, P.index_mem x, y, P.index_mem y, hxy⟩

end ConnectedPartition

namespace MinorModel

/-- Push a minor model through a connected partition when no partition
block meets two different branches. This is the contraction step used in
Appendix B. -/
noncomputable def pushThroughPartition
    {V I W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (P : ConnectedPartition G I) (M : MinorModel H G)
    (hcompatible : ∀ (i : I) ⦃w w' : W⦄ (x y : V),
      x ∈ P.block i → y ∈ P.block i →
      x ∈ M.branch w → y ∈ M.branch w' → w = w') :
    MinorModel H P.touchingQuotient where
  branch := fun w => P.index '' M.branch w
  connected := by
    intro w
    exact connected_induce_image_of_adj_or_eq_map
      (M.branch w) (M.connected w) P.index
      (by intro x y _ _ hxy; exact P.index_adj_or_eq hxy)
  disjoint := by
    intro w w' hww'
    apply Set.disjoint_left.mpr
    intro q hqw hqw'
    obtain ⟨x, hx, hqx⟩ := hqw
    obtain ⟨y, hy, hqy⟩ := hqw'
    have hxq : x ∈ P.block q := by simpa [← hqx] using P.index_mem x
    have hyq : y ∈ P.block q := by simpa [← hqy] using P.index_mem y
    exact hww' (hcompatible q x y hxq hyq hx hy)
  adjacent := by
    intro w w' hww'
    obtain ⟨x, hx, y, hy, hxy⟩ := M.adjacent hww'
    have hne : P.index x ≠ P.index y := by
      intro heq
      have hxybranch := hcompatible (P.index x) x y
        (P.index_mem x) (by simpa [← heq] using P.index_mem y) hx hy
      exact (H.ne_of_adj hww') hxybranch
    refine ⟨P.index x, ⟨x, hx, rfl⟩,
      P.index y, ⟨y, hy, rfl⟩, ?_⟩
    exact ⟨hne, x, P.index_mem x, y, P.index_mem y, hxy⟩

end MinorModel

namespace MinorModel

theorem eq_of_mem_same_branch
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (M : MinorModel H G) {w w' : W} {x : V}
    (hw : x ∈ M.branch w) (hw' : x ∈ M.branch w') : w = w' := by
  by_contra hne
  exact (Set.disjoint_left.mp (M.disjoint hne)) hw hw'

/-- Contracting an actual edge contained in one branch preserves any
minor model. -/
noncomputable def contractEdgeWithinBranch
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (M : MinorModel H G) {a b : V} (hab : G.Adj a b)
    (i₀ : W) (ha : a ∈ M.branch i₀) (hb : b ∈ M.branch i₀) :
    MinorModel H (edgeContraction G hab) := by
  let P := edgeContractionPartition G hab
  apply M.pushThroughPartition P
  intro q w w' x y hxq hyq hxw hyw
  cases q with
  | none =>
    have hx : x = a ∨ x = b := by
      simpa [P, edgeContractionPartition, edgeContractionBlock] using hxq
    have hy : y = a ∨ y = b := by
      simpa [P, edgeContractionPartition, edgeContractionBlock] using hyq
    have hxi₀ : x ∈ M.branch i₀ := by
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    have hyi₀ : y ∈ M.branch i₀ := by
      rcases hy with rfl | rfl
      · exact ha
      · exact hb
    exact (M.eq_of_mem_same_branch hxw hxi₀).trans
      (M.eq_of_mem_same_branch hyw hyi₀).symm
  | some z =>
    have hx : x = z.1 := by
      simpa [P, edgeContractionPartition, edgeContractionBlock] using hxq
    have hy : y = z.1 := by
      simpa [P, edgeContractionPartition, edgeContractionBlock] using hyq
    exact M.eq_of_mem_same_branch hxw (hx.trans hy.symm ▸ hyw)

end MinorModel

namespace ConnectedPartition

/-- Adding host edges preserves a connected partition. -/
def mono {V I : Type*} {G G' : SimpleGraph V}
    (P : ConnectedPartition G I) (h : G ≤ G') :
    ConnectedPartition G' I where
  block := P.block
  connected := fun i => (P.connected i).mono (by
    intro x y hxy
    exact h hxy)
  disjoint := P.disjoint
  cover := P.cover

/-- Completing edges inside R commutes with taking a touching quotient.
The quotient root set consists of blocks containing some original root. -/
theorem touchingQuotient_completeRoots
    {V I : Type*} {G : SimpleGraph V}
    (P : ConnectedPartition G I) (R : Set V) :
    (P.mono (completeRoots.supergraph (G := G) (R := R))).touchingQuotient =
      completeRoots P.touchingQuotient
        {i : I | ∃ x ∈ R, x ∈ P.block i} := by
  ext i j
  constructor
  · rintro ⟨hij, x, hx, y, hy, hxy⟩
    rcases hxy with hxy | ⟨hxR, hyR, _⟩
    · exact Or.inl ⟨hij, x, hx, y, hy, hxy⟩
    · exact Or.inr ⟨⟨x, hxR, hx⟩, ⟨y, hyR, hy⟩, hij⟩
  · rintro (hxy | ⟨hiR, hjR, hij⟩)
    · obtain ⟨hij, x, hx, y, hy, hxy⟩ := hxy
      exact ⟨hij, x, hx, y, hy, Or.inl hxy⟩
    · obtain ⟨x, hxR, hx⟩ := hiR
      obtain ⟨y, hyR, hy⟩ := hjR
      have hne : x ≠ y := by
        intro heq
        subst y
        exact (Set.disjoint_left.mp (P.disjoint hij)) hx hy
      exact ⟨hij, x, hx, y, hy, Or.inr ⟨hxR, hyR, hne⟩⟩

end ConnectedPartition

/-- The quotient vertices whose contraction blocks contain a prescribed
root. -/
def edgeContractionRootSet {V : Type*} {a b : V}
    (R : Set V) : Set (EdgeContractionVertex a b) :=
  {q | ∃ x ∈ R, x ∈ edgeContractionBlock (a := a) (b := b) q}

/-- Contracting an actual edge after completing R gives the same graph as
completing the quotient root blocks after contraction. -/
theorem edgeContraction_completeRoots
    {V : Type*} {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) (R : Set V) :
    edgeContraction (completeRoots G R) (completeRoots.supergraph hab) =
      completeRoots (edgeContraction G hab)
        (edgeContractionRootSet (a := a) (b := b) R) := by
  simpa only [edgeContraction, edgeContractionPartition,
    ConnectedPartition.mono, edgeContractionRootSet] using
      (edgeContractionPartition G hab).touchingQuotient_completeRoots R

namespace ConnectedPartition

/-- Membership in a block identifies the block index. -/
theorem index_eq_of_mem {V I : Type*} {G : SimpleGraph V}
    (P : ConnectedPartition G I) {x : V} {i : I}
    (hx : x ∈ P.block i) : P.index x = i := by
  by_contra hne
  exact (Set.disjoint_left.mp (P.disjoint hne)) (P.index_mem x) hx

end ConnectedPartition

/-- Map the prescribed roots to the blocks of an edge contraction. -/
noncomputable def edgeContractionRoot
    {V : Type*} {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) {r : ℕ} (root : Fin r → V) :
    Fin r → EdgeContractionVertex a b :=
  (edgeContractionPartition G hab).index ∘ root

theorem edgeContractionRootSet_eq_range
    {V : Type*} {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) {r : ℕ} (root : Fin r → V) :
    edgeContractionRootSet (a := a) (b := b) (Set.range root) =
      Set.range (edgeContractionRoot hab root) := by
  let P := edgeContractionPartition G hab
  ext q
  constructor
  · rintro ⟨x, ⟨i, rfl⟩, hx⟩
    exact ⟨i, P.index_eq_of_mem hx⟩
  · rintro ⟨i, rfl⟩
    exact ⟨root i, ⟨i, rfl⟩, P.index_mem (root i)⟩

/-- If one contracted endpoint is outside the root set, distinct roots
remain distinct after contraction. -/
theorem edgeContractionRoot_injective
    {V : Type*} {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) {r : ℕ} (root : Fin r → V)
    (hroot : Function.Injective root)
    (haR : a ∉ Set.range root) :
    Function.Injective (edgeContractionRoot hab root) := by
  let P := edgeContractionPartition G hab
  intro i j hij
  apply hroot
  change P.index (root i) = P.index (root j) at hij
  have hi : root i ∈ P.block (P.index (root i)) := P.index_mem (root i)
  have hj : root j ∈ P.block (P.index (root i)) := by
    rw [hij]
    exact P.index_mem (root j)
  cases hq : P.index (root i) with
  | none =>
    change root i ∈ edgeContractionBlock (a := a) (b := b)
      (P.index (root i)) at hi
    change root j ∈ edgeContractionBlock (a := a) (b := b)
      (P.index (root i)) at hj
    rw [hq] at hi hj
    simp only [edgeContractionBlock, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hi hj
    have hia : root i ≠ a := by
      intro h
      exact haR ⟨i, h⟩
    have hja : root j ≠ a := by
      intro h
      exact haR ⟨j, h⟩
    rcases hi with hi | hi
    · exact False.elim (hia hi)
    rcases hj with hj | hj
    · exact False.elim (hja hj)
    exact hi.trans hj.symm
  | some x =>
    change root i ∈ edgeContractionBlock (a := a) (b := b)
      (P.index (root i)) at hi
    change root j ∈ edgeContractionBlock (a := a) (b := b)
      (P.index (root i)) at hj
    rw [hq] at hi hj
    simp only [edgeContractionBlock, Set.mem_singleton_iff] at hi hj
    exact hi.trans hj.symm

/-- A K_(2r) model survives contraction of an actual edge within one
branch, with the contracted root set represented by the root-block map. -/
noncomputable def cliqueModel_contract_nonroot_edge
    {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (root : Fin r → V)
    (M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots G (Set.range root)))
    {a b : V} (hab : G.Adj a b)
    (i₀ : Fin (2 * r))
    (ha : a ∈ M.branch i₀) (hb : b ∈ M.branch i₀) :
    MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots (edgeContraction G hab)
        (Set.range (edgeContractionRoot hab root))) := by
  have habplus : (completeRoots G (Set.range root)).Adj a b :=
    completeRoots.supergraph hab
  let M' := M.contractEdgeWithinBranch habplus i₀ ha hb
  refine {
    branch := M'.branch
    connected := ?_
    disjoint := ?_
    adjacent := ?_
  }
  · intro j
    have h := M'.connected j
    simpa only [edgeContraction_completeRoots hab (Set.range root),
      edgeContractionRootSet_eq_range hab root] using h
  · exact M'.disjoint
  · intro j k hjk
    have h := M'.adjacent hjk
    simpa only [edgeContraction_completeRoots hab (Set.range root),
      edgeContractionRootSet_eq_range hab root] using h

/-- A rooted clique minor in a single-edge contraction lifts to the
original graph at the original prescribed roots. -/
theorem rootedCliqueMinor_of_edgeContraction
    {V : Type*} {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) {r : ℕ} (root : Fin r → V)
    (h : HasRootedCliqueMinor (edgeContraction G hab)
      (edgeContractionRoot hab root)) :
    HasRootedCliqueMinor G root := by
  obtain ⟨M⟩ := h
  let P := edgeContractionPartition G hab
  exact ⟨M.liftThroughPartition P root (fun i => P.index_mem (root i))⟩

/-- Menger links every prescribed root to a distinct vertex of any
r-element target set in an r-connected graph. -/
theorem exists_root_target_linkage
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r : ℕ}
    (hconn : VertexConnected G r)
    (root : Fin r → V) (hroot : Function.Injective root)
    (X : Finset V) (hX : X.card = r) :
    ∃ (P : IndexedPairs (Fin r) V) (L : IndexedLinkage G P),
      (∀ i, P.start i = root i) ∧
      (∀ i, P.finish i ∈ X) ∧
      (∀ x ∈ X, ∃ i, P.finish i = x) := by
  classical
  let R : Finset V := Finset.univ.image root
  have hRcard : R.card = r := by
    simp [R, Finset.card_image_of_injective _ hroot]
  obtain ⟨P, L, hAB⟩ := hconn.exists_AB_linkage R X
    (by omega) (by omega)
  have hstartInj := L.start_injective
  have hstartSubset : Finset.univ.image P.start ⊆ R := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hAB.1 i
  have hstartCard : (Finset.univ.image P.start).card = r := by
    simp [Finset.card_image_of_injective _ hstartInj]
  have hstartRange : Finset.univ.image P.start = R :=
    Finset.eq_of_subset_of_card_le hstartSubset (by omega)
  have hsurj : ∀ i : Fin r, ∃ j : Fin r, P.start j = root i := by
    intro i
    have hi : root i ∈ R := Finset.mem_image.mpr
      ⟨i, Finset.mem_univ _, rfl⟩
    rw [← hstartRange] at hi
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
    exact ⟨j, hj⟩
  let idx : Fin r → Fin r := fun i => Classical.choose (hsurj i)
  have hidx : ∀ i : Fin r, P.start (idx i) = root i := fun i =>
    Classical.choose_spec (hsurj i)
  have hidxInj : Function.Injective idx := by
    intro i j hij
    apply hroot
    calc
      root i = P.start (idx i) := (hidx i).symm
      _ = P.start (idx j) := by rw [hij]
      _ = root j := hidx j
  let e : Fin r ↪ Fin r := ⟨idx, hidxInj⟩
  let P' := P.reindex e
  let L' : IndexedLinkage G P' := L.reindex e
  have hfinishSubset : Finset.univ.image P'.finish ⊆ X := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hAB.2 (e i)
  have hfinishCard : (Finset.univ.image P'.finish).card = r := by
    simp [Finset.card_image_of_injective _ L'.finish_injective]
  have hfinishRange : Finset.univ.image P'.finish = X :=
    Finset.eq_of_subset_of_card_le hfinishSubset (by omega)
  refine ⟨P', L', hidx, (fun i => hAB.2 (e i)), ?_⟩
  intro x hx
  rw [← hfinishRange] at hx
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
  exact ⟨i, hi⟩

namespace IndexedLinkage

/-- When all vertices of X occur as distinct finishes, a disjoint path
can meet X only at its own finish. -/
theorem path_meets_finish_set_only_at_finish
    {ι V : Type*} {G : SimpleGraph V} {P : IndexedPairs ι V}
    (L : IndexedLinkage G P) (X : Set V)
    (hX : ∀ x ∈ X, ∃ j : ι, P.finish j = x)
    (i : ι) {x : V}
    (hx : x ∈ pathVertexSet (L.path i)) (hxX : x ∈ X) :
    x = P.finish i := by
  obtain ⟨j, hj⟩ := hX x hxX
  by_cases hij : i = j
  · subst j
    exact hj.symm
  · have hxj : x ∈ pathVertexSet (L.path j) := by
      simpa only [hj] using pathVertexSet.finish_mem (L.path j)
    exact False.elim ((Set.disjoint_left.mp (L.disjoint hij)) hx hxj)

/-- When all vertices of R occur as distinct starts, a disjoint path
can meet R only at its own start. -/
theorem path_meets_start_set_only_at_start
    {ι V : Type*} {G : SimpleGraph V} {P : IndexedPairs ι V}
    (L : IndexedLinkage G P) (R : Set V)
    (hR : ∀ x ∈ R, ∃ j : ι, P.start j = x)
    (i : ι) {x : V}
    (hx : x ∈ pathVertexSet (L.path i)) (hxR : x ∈ R) :
    x = P.start i := by
  obtain ⟨j, hj⟩ := hR x hxR
  by_cases hij : i = j
  · subst j
    exact hj.symm
  · have hxj : x ∈ pathVertexSet (L.path j) := by
      simpa only [hj] using pathVertexSet.start_mem (L.path j)
    exact False.elim ((Set.disjoint_left.mp (L.disjoint hij)) hx hxj)

end IndexedLinkage

namespace VertexSeparation

/-- A simple path starting on the left and meeting the separator only at
its finish stays on the left. -/
theorem path_support_subset_left_of_boundary_only_at_finish
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : VertexSeparation G)
    {u z : V} (p : G.Walk u z) (hp : p.IsPath)
    (hu : u ∈ S.left)
    (hboundary : ∀ x ∈ p.support, x ∈ S.separator → x = z) :
    ∀ x ∈ p.support, x ∈ S.left := by
  revert hp hu hboundary
  induction p with
  | nil =>
    intro hp hu hboundary
    intro x hx
    simp at hx
    subst x
    exact hu
  | @cons u v z huv p ih =>
    intro hp hu hboundary
    have hne : u ≠ z := by
      intro heq
      have hnil : (SimpleGraph.Walk.cons huv p).Nil :=
        (SimpleGraph.Walk.IsPath.nil_iff_eq hp).2 heq
      exact (by simpa using hnil)
    have huNotR : u ∉ S.right := by
      intro huR
      have hub : u ∈ S.separator := ⟨hu, huR⟩
      exact hne (hboundary u (by simp) hub)
    have hvL : v ∈ S.left := by
      by_contra hvL
      have hvR : v ∈ S.right := by
        have hcover : v ∈ S.left ∪ S.right := by rw [S.cover]; trivial
        rcases hcover with h | h
        · exact False.elim (hvL h)
        · exact h
      exact S.no_cross hu huNotR hvR hvL huv
    have hptail : p.IsPath := (SimpleGraph.Walk.cons_isPath_iff huv p).mp hp |>.1
    have hbTail : ∀ x ∈ p.support, x ∈ S.separator → x = z := by
      intro x hx hxB
      exact hboundary x (by simp [hx]) hxB
    have htail := ih hptail hvL hbTail
    intro x hx
    rcases (List.mem_cons.mp (by simpa using hx)) with hxu | hxp
    · exact hxu ▸ hu
    · exact htail x hxp

end VertexSeparation

namespace VertexSeparation

/-- An r-path linkage to every boundary vertex stays on the near side of
a separation when all of its starts lie there. -/
theorem linkage_to_boundary_stays_left
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : VertexSeparation G) {r : ℕ}
    (P : IndexedPairs (Fin r) V) (L : IndexedLinkage G P)
    (hstart : ∀ i, P.start i ∈ S.left)
    (hfinish : ∀ x ∈ S.separatorFinset,
      ∃ i : Fin r, P.finish i = x) :
    ∀ i, pathVertexSet (L.path i) ⊆ S.left := by
  intro i x hx
  have hboundary : ∀ y ∈ (L.path i : G.Walk (P.start i) (P.finish i)).support,
      y ∈ S.separator → y = P.finish i := by
    intro y hy hyS
    exact L.path_meets_finish_set_only_at_finish S.separator
      (by
        intro z hz
        exact hfinish z ((S.mem_separatorFinset z).mpr hz))
      i hy hyS
  exact S.path_support_subset_left_of_boundary_only_at_finish
    (L.path i : G.Walk (P.start i) (P.finish i))
    (L.path i).property (hstart i) hboundary x hx

end VertexSeparation
end HadwigerLean
