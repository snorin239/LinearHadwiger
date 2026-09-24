import HadwigerLean.Graph.Finite
import HadwigerLean.Graph.Minor
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Pair-indexed graph matchings

An orientation of the edges of a matching gives two injectively indexed
endpoints per pair.  This interface retains both endpoints when the pairs
are contracted and, unlike a quotient by components, does not forget
parallel matching edges.  The greedy weighted-matching construction and
independent transversal will be developed on top of it.
-/

namespace HadwigerLean

universe u v

/-- A matching of `G`, indexed and oriented by an arbitrary finite type. -/
structure IndexedMatching {V : Type u} (G : SimpleGraph V) (I : Type v) where
  endpoint : I → Bool → V
  injective : Function.Injective (fun p : I × Bool => endpoint p.1 p.2)
  adjacent : ∀ i, G.Adj (endpoint i false) (endpoint i true)

namespace IndexedMatching

variable {V : Type u} {I : Type v} {G : SimpleGraph V}

/-- The two endpoints of an indexed matching edge. -/
def branch (M : IndexedMatching G I) (i : I) : Set V :=
  {M.endpoint i false, M.endpoint i true}

@[simp] theorem mem_branch (M : IndexedMatching G I) (i : I) (x : V) :
    x ∈ M.branch i ↔ x = M.endpoint i false ∨ x = M.endpoint i true := by
  simp [branch]

/-- Every matching edge is a connected branch set. -/
theorem branch_connected (M : IndexedMatching G I) (i : I) :
    (G.induce (M.branch i)).Connected := by
  exact G.induce_pair_connected_of_adj (M.adjacent i)

/-- Distinct matching edges have disjoint vertex sets. -/
theorem branch_disjoint (M : IndexedMatching G I) :
    Pairwise fun i j => Disjoint (M.branch i) (M.branch j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases (M.mem_branch i x).mp hxi with hxi | hxi <;>
    rcases (M.mem_branch j x).mp hxj with hxj | hxj
  · have h : (i, false) = (j, false) := M.injective (hxi.symm.trans hxj)
    exact hij (congrArg Prod.fst h)
  · have h : (i, false) = (j, true) := M.injective (hxi.symm.trans hxj)
    exact Bool.false_ne_true (congrArg Prod.snd h)
  · have h : (i, true) = (j, false) := M.injective (hxi.symm.trans hxj)
    exact Bool.false_ne_true (congrArg Prod.snd h).symm
  · have h : (i, true) = (j, true) := M.injective (hxi.symm.trans hxj)
    exact hij (congrArg Prod.fst h)

/-- The simple quotient obtained by contracting all matching pairs. -/
def quotient (M : IndexedMatching G I) : SimpleGraph I where
  Adj i j := i ≠ j ∧ ∃ a b : Bool, G.Adj (M.endpoint i a) (M.endpoint j b)
  symm := ⟨by
    intro i j hij
    obtain ⟨hne, a, b, hab⟩ := hij
    exact ⟨hne.symm, b, a, hab.symm⟩⟩
  loopless := ⟨by
    intro i hii
    exact hii.1 rfl⟩

theorem quotient_adj_iff (M : IndexedMatching G I) (i j : I) :
    M.quotient.Adj i j ↔
      i ≠ j ∧ ∃ a b : Bool, G.Adj (M.endpoint i a) (M.endpoint j b) :=
  Iff.rfl

/-- Matching contraction is a graph minor, including when unmatched vertices are deleted. -/
def quotientMinorModel (M : IndexedMatching G I) : MinorModel M.quotient G where
  branch := M.branch
  connected := M.branch_connected
  disjoint := M.branch_disjoint
  adjacent := by
    intro i j hij
    obtain ⟨_, a, b, hab⟩ := (M.quotient_adj_iff i j).mp hij
    refine ⟨M.endpoint i a, ?_, M.endpoint j b, ?_, hab⟩
    · cases a <;> simp [branch]
    · cases b <;> simp [branch]

theorem quotient_isMinor (M : IndexedMatching G I) : IsMinor M.quotient G :=
  ⟨M.quotientMinorModel⟩

theorem quotient_cliqueMinorNumber_le [Fintype V] [Fintype I]
    (M : IndexedMatching G I) :
    cliqueMinorNumber M.quotient ≤ cliqueMinorNumber G :=
  cliqueMinorNumber_mono_minor M.quotient_isMinor

/-- The graph consisting exactly of the indexed matching edges. -/
def edgeGraph (M : IndexedMatching G I) : SimpleGraph V where
  Adj x y := ∃ i : I,
    (x = M.endpoint i false ∧ y = M.endpoint i true) ∨
    (x = M.endpoint i true ∧ y = M.endpoint i false)
  symm := ⟨by
    intro x y h
    obtain ⟨i, h⟩ := h
    refine ⟨i, ?_⟩
    rcases h with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩⟩
  loopless := ⟨by
    intro x h
    obtain ⟨i, h⟩ := h
    rcases h with h | h
    · exact (M.adjacent i).ne (h.1.symm.trans h.2)
    · exact (M.adjacent i).ne (h.2.symm.trans h.1)⟩

theorem edgeGraph_le (M : IndexedMatching G I) : M.edgeGraph ≤ G := by
  intro x y h
  obtain ⟨i, h⟩ := h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact M.adjacent i
  · exact (M.adjacent i).symm

theorem edgeGraph_adj_endpoints (M : IndexedMatching G I) (i : I) :
    M.edgeGraph.Adj (M.endpoint i false) (M.endpoint i true) :=
  ⟨i, Or.inl ⟨rfl, rfl⟩⟩

theorem edgeGraph_unique_of_left (M : IndexedMatching G I)
    (i : I) {v : V} (h : M.edgeGraph.Adj (M.endpoint i false) v) :
    v = M.endpoint i true := by
  obtain ⟨j, h⟩ := h
  rcases h with ⟨hleft, rfl⟩ | ⟨hright, rfl⟩
  · have hij : (i, false) = (j, false) := M.injective hleft
    exact (congrArg (fun p : I × Bool => M.endpoint p.1 true) hij).symm
  · have hij : (i, false) = (j, true) := M.injective hright
    exact (Bool.false_ne_true (congrArg Prod.snd hij)).elim

theorem edgeGraph_unique_of_right (M : IndexedMatching G I)
    (i : I) {v : V} (h : M.edgeGraph.Adj (M.endpoint i true) v) :
    v = M.endpoint i false := by
  obtain ⟨j, h⟩ := h
  rcases h with ⟨hleft, rfl⟩ | ⟨hright, rfl⟩
  · have hij : (i, true) = (j, false) := M.injective hleft
    exact (Bool.false_ne_true (congrArg Prod.snd hij).symm).elim
  · have hij : (i, true) = (j, true) := M.injective hright
    exact (congrArg (fun p : I × Bool => M.endpoint p.1 false) hij).symm
theorem edgeGraph_adj_unique (M : IndexedMatching G I)
    {x y z : V} (hxy : M.edgeGraph.Adj x y)
    (hxz : M.edgeGraph.Adj x z) : y = z := by
  obtain ⟨i, h⟩ := hxy
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (M.edgeGraph_unique_of_left i hxz).symm
  · exact (M.edgeGraph_unique_of_right i hxz).symm

theorem edgeGraph_degree_le_one [Fintype V] [DecidableEq V]
    (M : IndexedMatching G I) [DecidableRel M.edgeGraph.Adj] (x : V) :
    M.edgeGraph.degree x ≤ 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_le_one]
  intro y hy z hz
  exact M.edgeGraph_adj_unique (by simpa using hy) (by simpa using hz)
end IndexedMatching

/-- A finite forest with an edge has a leaf, even if it is disconnected. -/
theorem forest_exists_degree_one {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hforest : H.IsAcyclic)
    {u v : V} (huv : H.Adj u v) :
    ∃ x : V, H.degree x = 1 := by
  classical
  let C := H.connectedComponentMk u
  have hu : u ∈ C.supp := SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hv : v ∈ C.supp := C.mem_supp_of_adj_mem_supp hu huv
  let x₀ : C := ⟨u, hu⟩
  let y₀ : C := ⟨v, hv⟩
  haveI : Nontrivial C := ⟨x₀, y₀, by
    intro h
    exact huv.ne (congrArg Subtype.val h)⟩
  obtain ⟨x, hx⟩ :=
    (hforest.isTree_connectedComponent C).exists_vert_degree_one_of_nontrivial
  obtain ⟨y, hxy, huniq⟩ :=
    (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mp hx
  refine ⟨x.1, (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mpr ?_⟩
  refine ⟨y.1, (C.toSimpleGraph_adj x.property y.property).mp hxy, ?_⟩
  intro z hxz
  have hz : z ∈ C.supp := C.mem_supp_of_adj_mem_supp x.property hxz
  exact congrArg Subtype.val
    (huniq ⟨z, hz⟩ ((C.toSimpleGraph_adj x.property hz).mpr hxz))
/-- If matching edges stay outside cycles after replacing D by a spanning
forest, then a matching pair has a D-isolated endpoint. This is the peeling
step behind the independent transversal. -/
theorem exists_isolated_of_perfect_matching_forest
    {V : Type*} [Fintype V] [Nonempty V]
    (D P : SimpleGraph V)
    (hperfect : ∀ x : V, ∃ y : V, P.Adj x y)
    (hedgeDisjoint : ∀ x y, D.Adj x y → ¬ P.Adj x y)
    (hacyclic : ∀ F : SimpleGraph V, F ≤ D → F.IsAcyclic →
      (F ⊔ P).IsAcyclic) :
    ∃ x : V, D.IsIsolated x := by
  classical
  obtain ⟨F, hFD, hFforest, hreach⟩ := D.exists_isAcyclic_reachable_eq_le
  let x₀ : V := Classical.choice inferInstance
  obtain ⟨y₀, hPxy⟩ := hperfect x₀
  have hHP : (F ⊔ P).Adj x₀ y₀ := Or.inr hPxy
  obtain ⟨x, hx⟩ :=
    forest_exists_degree_one (F ⊔ P) (hacyclic F hFD hFforest) hHP
  obtain ⟨y, hPxy⟩ := hperfect x
  obtain ⟨z, hHz, huniq⟩ :=
    (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mp hx
  have hyz : y = z := huniq y (Or.inr hPxy)
  have hFisolated : F.IsIsolated x := by
    intro t hFxt
    have htz : t = z := huniq t (Or.inl hFxt)
    have hty : t = y := htz.trans hyz.symm
    have hPxt : P.Adj x t := by simpa [hty] using hPxy
    exact hedgeDisjoint x t (hFD hFxt) hPxt
  refine ⟨x, ?_⟩
  intro t hDxt
  have hFreach : F.Reachable x t := by
    rw [hreach]
    exact hDxt.reachable
  obtain ⟨p⟩ := hFreach
  cases p with
  | nil => exact hDxt.ne rfl
  | cons h _ => exact hFisolated _ h
/-- No cycle of D+P uses an edge of P. Cycles entirely in D are permitted. -/
def NoMatchingEdgeCycle {V : Type*} (D P : SimpleGraph V) : Prop :=
  ∀ (u : V) (c : (D ⊔ P).Walk u u), c.IsCycle →
    ∀ e ∈ c.edges, e ∉ P.edgeSet

/-- The paper's cycle condition makes a spanning forest of D together with
the matching edges acyclic. -/
theorem forest_union_acyclic_of_no_matching_cycle
    {V : Type*} (D P : SimpleGraph V)
    (hcycles : NoMatchingEdgeCycle D P)
    (F : SimpleGraph V) (hFD : F ≤ D) (hFforest : F.IsAcyclic) :
    (F ⊔ P).IsAcyclic := by
  intro u c hc
  have hle : F ⊔ P ≤ D ⊔ P := sup_le_sup hFD le_rfl
  have hno := hcycles u (c.mapLe hle) (hc.mapLe hle)
  have hFedges : ∀ e, e ∈ c.edges → e ∈ F.edgeSet := by
    intro e he
    have hmem : e ∈ (F ⊔ P).edgeSet := c.edges_subset_edgeSet he
    rw [SimpleGraph.edgeSet_sup] at hmem
    rcases hmem with heF | heP
    · exact heF
    · have hnot : e ∉ P.edgeSet :=
        hno e (by simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using he)
      exact (hnot heP).elim
  exact hFforest (c.transfer F hFedges) (hc.transfer hFedges)

/-- A perfect matching whose edges are all absent from cycles of D+P has a
pair with a D-isolated endpoint. -/
theorem exists_isolated_of_no_matching_cycle
    {V : Type*} [Fintype V] [Nonempty V]
    (D P : SimpleGraph V)
    (hperfect : ∀ x : V, ∃ y : V, P.Adj x y)
    (hedgeDisjoint : ∀ x y, D.Adj x y → ¬ P.Adj x y)
    (hcycles : NoMatchingEdgeCycle D P) :
    ∃ x : V, D.IsIsolated x :=
  exists_isolated_of_perfect_matching_forest D P hperfect hedgeDisjoint
    (forest_union_acyclic_of_no_matching_cycle D P hcycles)
/-- Keep only edges with both endpoints in a specified finite set, while
retaining the original vertex type. -/
def spanningInduce {V : Type*} (G : SimpleGraph V) (s : Finset V) : SimpleGraph V where
  Adj x y := x ∈ s ∧ y ∈ s ∧ G.Adj x y
  symm := ⟨by
    intro x y h
    exact ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨by
    intro x h
    exact G.loopless.irrefl x h.2.2⟩

@[simp] theorem spanningInduce_adj_iff {V : Type*} (G : SimpleGraph V)
    (s : Finset V) (x y : V) :
    (spanningInduce G s).Adj x y ↔ x ∈ s ∧ y ∈ s ∧ G.Adj x y :=
  Iff.rfl

theorem spanningInduce_le {V : Type*} (G : SimpleGraph V) (s : Finset V) :
    spanningInduce G s ≤ G := by
  intro x y h
  exact h.2.2

/-- The no-matching-cycle condition is inherited by spanning subgraphs. -/
theorem NoMatchingEdgeCycle.mono
    {V : Type*} {D P D' P' : SimpleGraph V}
    (h : NoMatchingEdgeCycle D P) (hD : D' ≤ D) (hP : P' ≤ P) :
    NoMatchingEdgeCycle D' P' := by
  intro u c hc e he
  have hle : D' ⊔ P' ≤ D ⊔ P := sup_le_sup hD hP
  have hnot := h u (c.mapLe hle) (hc.mapLe hle) e
    (by simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using he)
  intro heP'
  exact hnot (SimpleGraph.edgeSet_mono hP heP')
/-- Peeling with the graph vertex type fixed. All edges are supported on s,
and vertices of s are paired by P. -/
theorem exists_isolated_on_support
    {V : Type*} [Fintype V] (D P : SimpleGraph V) (s : Finset V)
    (hs : s.Nonempty)
    (hDsupport : ∀ x y, D.Adj x y → x ∈ s)
    (hPsupport : ∀ x y, P.Adj x y → x ∈ s)
    (hperfect : ∀ x ∈ s, ∃ y, P.Adj x y)
    (hedgeDisjoint : ∀ x y, D.Adj x y → ¬ P.Adj x y)
    (hcycles : NoMatchingEdgeCycle D P) :
    ∃ x ∈ s, D.IsIsolated x := by
  classical
  obtain ⟨F, hFD, hFforest, hreach⟩ := D.exists_isAcyclic_reachable_eq_le
  obtain ⟨x₀, hx₀⟩ := hs
  obtain ⟨y₀, hPxy⟩ := hperfect x₀ hx₀
  have hHP : (F ⊔ P).Adj x₀ y₀ := Or.inr hPxy
  obtain ⟨x, hx⟩ := forest_exists_degree_one (F ⊔ P)
    (forest_union_acyclic_of_no_matching_cycle D P hcycles F hFD hFforest) hHP
  obtain ⟨z, hHz, huniqH⟩ :=
    (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mp hx
  have hxs : x ∈ s := by
    rcases hHz with hF | hP
    · exact hDsupport x z (hFD hF)
    · exact hPsupport x z hP
  obtain ⟨y, hPxy⟩ := hperfect x hxs
  have hyz : y = z := huniqH y (Or.inr hPxy)
  have hFisolated : F.IsIsolated x := by
    intro t hFxt
    have htz : t = z := huniqH t (Or.inl hFxt)
    have hty : t = y := htz.trans hyz.symm
    have hPxt : P.Adj x t := by simpa [hty] using hPxy
    exact hedgeDisjoint x t (hFD hFxt) hPxt
  refine ⟨x, hxs, ?_⟩
  intro t hDxt
  have hFreach : F.Reachable x t := by
    rw [hreach]
    exact hDxt.reachable
  obtain ⟨p⟩ := hFreach
  cases p with
  | nil => exact hDxt.ne rfl
  | cons h _ => exact hFisolated _ h
/-- Deleting both ends of one perfect-matching pair preserves any union of
matching pairs. -/
theorem perfect_matching_closed_sdiff_pair
    {V : Type*} [DecidableEq V] (P : SimpleGraph V)
    (hperfect : ∀ a : V, ∃! b : V, P.Adj a b)
    {s : Finset V}
    (hclosed : ∀ a ∈ s, ∀ b, P.Adj a b → b ∈ s)
    {x y : V} (hxy : P.Adj x y) :
    ∀ a ∈ s \ {x, y}, ∀ b, P.Adj a b → b ∈ s \ {x, y} := by
  intro a ha b hab
  have has : a ∈ s := (Finset.mem_sdiff.mp ha).1
  have hax : a ≠ x := by
    intro h
    subst a
    exact (Finset.mem_sdiff.mp ha).2 (by simp)
  have hay : a ≠ y := by
    intro h
    subst a
    exact (Finset.mem_sdiff.mp ha).2 (by simp)
  have hbs : b ∈ s := hclosed a has b hab
  have hbx : b ≠ x := by
    intro h
    subst b
    obtain ⟨_, _, huniq⟩ := hperfect x
    have hya : a = y := by
      have hxy' : P.Adj x y := hxy
      exact (huniq a hab.symm).trans (huniq y hxy').symm
    exact hay hya
  have hby : b ≠ y := by
    intro h
    subst b
    obtain ⟨_, _, huniq⟩ := hperfect y
    have hxa : a = x := (huniq a hab.symm).trans (huniq x hxy.symm).symm
    exact hax hxa
  exact Finset.mem_sdiff.mpr ⟨hbs, by simp [hbx, hby]⟩
/-- Independent transversal of a perfect matching under the paper's
no-matching-edge-cycle condition. The auxiliary set may be any union of
matching pairs, which gives the induction invariant. -/
theorem independent_transversal_on
    {V : Type*} [Fintype V] [DecidableEq V]
    (D P : SimpleGraph V)
    (hperfect : ∀ a : V, ∃! b : V, P.Adj a b)
    (hedgeDisjoint : ∀ a b, D.Adj a b → ¬ P.Adj a b)
    (hcycles : NoMatchingEdgeCycle D P)
    (s : Finset V)
    (hclosed : ∀ a ∈ s, ∀ b, P.Adj a b → b ∈ s) :
    ∃ T : Finset V, T ⊆ s ∧ D.IsIndepSet (T : Set V) ∧
      ∀ a b, P.Adj a b → a ∈ s → (a ∈ T ↔ b ∉ T) := by
  classical
  have aux : ∀ t : Finset V,
      (∀ a ∈ t, ∀ b, P.Adj a b → b ∈ t) →
      ∃ T : Finset V, T ⊆ t ∧ D.IsIndepSet (T : Set V) ∧
        ∀ a b, P.Adj a b → a ∈ t → (a ∈ T ↔ b ∉ T) := by
    intro t
    refine Finset.strongInductionOn t ?_
    intro t ih htclosed
    by_cases ht : t.Nonempty
    · let Dt := spanningInduce D t
      let Pt := spanningInduce P t
      have hDt : Dt ≤ D := spanningInduce_le D t
      have hPt : Pt ≤ P := spanningInduce_le P t
      have hcycles_t : NoMatchingEdgeCycle Dt Pt :=
        hcycles.mono hDt hPt
      have hperfect_t : ∀ a ∈ t, ∃ b, Pt.Adj a b := by
        intro a ha
        obtain ⟨b, hab, _⟩ := hperfect a
        exact ⟨b, ⟨ha, htclosed a ha b hab, hab⟩⟩
      have hdisj_t : ∀ a b, Dt.Adj a b → ¬ Pt.Adj a b := by
        intro a b hab hp
        exact hedgeDisjoint a b hab.2.2 hp.2.2
      obtain ⟨x, hxt, hxisol⟩ :=
        exists_isolated_on_support Dt Pt t ht
          (fun a b hab => hab.1)
          (fun a b hab => hab.1)
          hperfect_t hdisj_t hcycles_t
      obtain ⟨y, hxy, huniqx⟩ := hperfect x
      have hyt : y ∈ t := htclosed x hxt y hxy
      let t' : Finset V := t \ {x, y}
      have hpairsub : ({x, y} : Finset V) ⊆ t := by
        intro z hz
        rcases Finset.mem_insert.mp hz with hzx | hzy
        · exact hzx ▸ hxt
        · simpa [Finset.mem_singleton.mp hzy] using hyt
      have hpairne : ({x, y} : Finset V).Nonempty := by simp
      have ht'lt : t' ⊂ t := Finset.sdiff_ssubset hpairsub hpairne
      have ht'closed : ∀ a ∈ t', ∀ b, P.Adj a b → b ∈ t' :=
        perfect_matching_closed_sdiff_pair P hperfect htclosed hxy
      obtain ⟨T, hTsub, hTindep, hTcross⟩ := ih t' ht'lt ht'closed
      have hxnotT : x ∉ T := by
        intro hxT
        have hx' := hTsub hxT
        simp [t'] at hx'
      have hynotT : y ∉ T := by
        intro hyT
        have hy' := hTsub hyT
        simp [t'] at hy'
      have hTsubset : insert x T ⊆ t := by
        intro a ha
        rcases Finset.mem_insert.mp ha with hax | haT
        · simpa [hax] using hxt
        · exact (Finset.mem_sdiff.mp (hTsub haT)).1
      have hTindep' : D.IsIndepSet ((insert x T : Finset V) : Set V) := by
        intro a ha b hb hne hab
        change a ∈ insert x T at ha
        change b ∈ insert x T at hb
        rcases Finset.mem_insert.mp ha with hax | haT
        · subst a
          rcases Finset.mem_insert.mp hb with hbx | hbT
          · exact hne hbx.symm
          · have hbt : b ∈ t := (Finset.mem_sdiff.mp (hTsub hbT)).1
            exact hxisol b (show Dt.Adj x b from ⟨hxt, hbt, hab⟩)
        · rcases Finset.mem_insert.mp hb with hbx | hbT
          · subst b
            have hat : a ∈ t := (Finset.mem_sdiff.mp (hTsub haT)).1
            exact hxisol a (show Dt.Adj x a from ⟨hxt, hat, hab.symm⟩)
          · exact hTindep haT hbT hne hab
      refine ⟨insert x T, hTsubset, hTindep', ?_⟩
      intro a b hab hat
      by_cases hax : a = x
      · subst a
        have hby : b = y := huniqx b hab
        subst b
        simp [Finset.mem_insert, hxy.ne.symm, hynotT]
      · by_cases hay : a = y
        · subst a
          obtain ⟨q, hyq, huniqy⟩ := hperfect y
          have hbx : b = x := (huniqy b hab).trans (huniqy x hxy.symm).symm
          subst b
          simp [Finset.mem_insert, hxy.ne.symm, hynotT]
        · have hat' : a ∈ t' := by
            simp [t', hat, hax, hay]
          have hbt' : b ∈ t' := ht'closed a hat' b hab
          have hbx : b ≠ x := by
            intro h
            subst b
            have hb' := hbt'
            simp [t'] at hb'
          simpa [Finset.mem_insert, hax, hbx] using hTcross a b hab hat'
    · have he : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
      subst t
      refine ⟨∅, by simp, ?_, ?_⟩
      · intro a ha
        simp at ha
      · intro a b hab ha
        simp at ha
  exact aux s hclosed
/-- Independent transversal of every pair of a perfect matching, in the
precise form of Lemma "Independent transversal" in the paper. -/
theorem independent_transversal
    {V : Type*} [Fintype V] [DecidableEq V]
    (D P : SimpleGraph V)
    (hperfect : ∀ a : V, ∃! b : V, P.Adj a b)
    (hedgeDisjoint : ∀ a b, D.Adj a b → ¬ P.Adj a b)
    (hcycles : NoMatchingEdgeCycle D P) :
    ∃ T : Finset V, D.IsIndepSet (T : Set V) ∧
      ∀ a b, P.Adj a b → (a ∈ T ↔ b ∉ T) := by
  obtain ⟨T, _, hTindep, hTcross⟩ :=
    independent_transversal_on D P hperfect hedgeDisjoint hcycles
      (Finset.univ : Finset V) (by simp)
  exact ⟨T, hTindep, fun a b hab => hTcross a b hab (Finset.mem_univ a)⟩
/-- Extended distance excludes all short walks, including across disconnected
components, where ordinary natural-valued distance would be zero. -/
theorem length_gt_of_edist_gt
    {V : Type*} (J : SimpleGraph V) {u v : V} {r : ℕ}
    (h : (r : ℕ∞) < J.edist u v) (p : J.Walk u v) :
    r < p.length := by
  exact_mod_cast h.trans_le p.edist_le

theorem not_adj_of_edist_gt_one
    {V : Type*} (J : SimpleGraph V) {u v : V}
    (h : (1 : ℕ∞) < J.edist u v) :
    ¬ J.Adj u v := by
  intro hadj
  exact (not_lt_of_ge (SimpleGraph.edist_le hadj.toWalk)) h
/-- A simple cycle uses no more vertices than the ambient finite graph. -/
theorem cycle_length_le_card
    {V : Type*} [Fintype V] {J : SimpleGraph V}
    {u : V} {c : J.Walk u u} (hc : c.IsCycle) :
    c.length ≤ Fintype.card V := by
  have h := hc.support_nodup.length_le_card
  simpa [List.length_tail, c.length_support] using h

/-- A global exclusion of cycles through a matching edge up to the graph
order implies the unrestricted cycle condition. -/
theorem no_matching_edge_cycle_of_short_excluded
    {V : Type*} [Fintype V] (D P : SimpleGraph V) (r : ℕ)
    (hcard : Fintype.card V ≤ r)
    (hshort : ∀ (u : V) (c : (D ⊔ P).Walk u u),
      c.IsCycle → c.length ≤ r →
        ∀ e ∈ c.edges, e ∉ P.edgeSet) :
    NoMatchingEdgeCycle D P := by
  intro u c hc
  exact hshort u c hc ((cycle_length_le_card hc).trans hcard)
/-- Endpoints of walks of exactly n steps from u. This counts walks through
vertices already visited, which is convenient for upper bounds. -/
def walkReach {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (u : V) : ℕ → Finset V
  | 0 => {u}
  | n + 1 => (J.neighborFinset u).biUnion fun v => walkReach J v n

theorem mem_walkReach_of_walk
    {V : Type*} [Fintype V] [DecidableEq V]
    {J : SimpleGraph V} [DecidableRel J.Adj]
    {u v : V} (p : J.Walk u v) :
    v ∈ walkReach J u p.length := by
  induction p with
  | nil => simp [walkReach]
  | @cons u w v huw p ih =>
    simp only [SimpleGraph.Walk.length_cons, walkReach, Finset.mem_biUnion]
    exact ⟨w, by simpa using huw, ih⟩

theorem card_walkReach_le_pow
    {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (k : ℕ)
    (hdegree : ∀ u, J.degree u ≤ k) :
    ∀ n u, (walkReach J u n).card ≤ k ^ n := by
  intro n
  induction n with
  | zero =>
    intro u
    simp [walkReach]
  | succ n ih =>
    intro u
    calc
      (walkReach J u (n + 1)).card =
          ((J.neighborFinset u).biUnion fun v => walkReach J v n).card := rfl
      _ ≤ ∑ v ∈ J.neighborFinset u, (walkReach J v n).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ v ∈ J.neighborFinset u, k ^ n := by
        apply Finset.sum_le_sum
        intro v _
        exact ih v
      _ = J.degree u * k ^ n := by simp [SimpleGraph.card_neighborFinset_eq_degree]
      _ ≤ k * k ^ n := Nat.mul_le_mul_right _ (hdegree u)
      _ = k ^ (n + 1) := by simp [pow_succ, Nat.mul_comm]

/-- Endpoints of walks of at most r steps from u. -/
def walkBall {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (u : V) (r : ℕ) : Finset V :=
  (Finset.range (r + 1)).biUnion fun n => walkReach J u n

theorem card_walkBall_le_sum_pow
    {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (k r : ℕ)
    (hdegree : ∀ u, J.degree u ≤ k) (u : V) :
    (walkBall J u r).card ≤ ∑ n ∈ Finset.range (r + 1), k ^ n := by
  calc
    (walkBall J u r).card ≤
        ∑ n ∈ Finset.range (r + 1), (walkReach J u n).card := by
          exact Finset.card_biUnion_le
    _ ≤ ∑ n ∈ Finset.range (r + 1), k ^ n := by
          apply Finset.sum_le_sum
          intro n _
          exact card_walkReach_le_pow J k hdegree n u

theorem mem_walkBall_of_edist_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj]
    {u v : V} {r : ℕ} (h : J.edist u v ≤ (r : ℕ∞)) :
    v ∈ walkBall J u r := by
  have hfinite : J.edist u v ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by simp) h
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hfinite
  have hlen : p.length ≤ r := by
    exact_mod_cast hp.symm ▸ h
  exact Finset.mem_biUnion.mpr
    ⟨p.length, Finset.mem_range.mpr (Nat.lt_succ_of_le hlen),
      mem_walkReach_of_walk p⟩

theorem card_edist_ball_le_sum_pow
    {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (k r : ℕ)
    (hdegree : ∀ u, J.degree u ≤ k) (u : V) :
    (Finset.univ.filter fun v => J.edist u v ≤ (r : ℕ∞)).card ≤
      ∑ n ∈ Finset.range (r + 1), k ^ n := by
  calc
    (Finset.univ.filter fun v => J.edist u v ≤ (r : ℕ∞)).card ≤
        (walkBall J u r).card := by
          apply Finset.card_le_card
          intro v hv
          exact mem_walkBall_of_edist_le J (Finset.mem_filter.mp hv).2
    _ ≤ ∑ n ∈ Finset.range (r + 1), k ^ n :=
      card_walkBall_le_sum_pow J k r hdegree u

/-- Degrees are subadditive under the union of two spanning graphs. -/
theorem degree_sup_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (D P : SimpleGraph V) [DecidableRel D.Adj] [DecidableRel P.Adj]
    [DecidableRel (D ⊔ P).Adj] (x : V) :
    (D ⊔ P).degree x ≤ D.degree x + P.degree x := by
  have hsubset :
      (D ⊔ P).neighborFinset x ⊆ D.neighborFinset x ∪ P.neighborFinset x := by
    intro y hy
    have hadj : D.Adj x y ∨ P.Adj x y :=
      (SimpleGraph.sup_adj D P x y).mp
        (((D ⊔ P).mem_neighborFinset x y).mp hy)
    rcases hadj with h | h
    · exact Finset.mem_union_left _ ((D.mem_neighborFinset x y).mpr h)
    · exact Finset.mem_union_right _ ((P.mem_neighborFinset x y).mpr h)
  calc
    (D ⊔ P).degree x = ((D ⊔ P).neighborFinset x).card := rfl
    _ ≤ (D.neighborFinset x ∪ P.neighborFinset x).card :=
      Finset.card_le_card hsubset
    _ ≤ (D.neighborFinset x).card + (P.neighborFinset x).card :=
      Finset.card_union_le _ _
    _ = D.degree x + P.degree x := rfl

theorem IndexedMatching.degree_sup_edgeGraph_le
    {V : Type*} {I : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (M : IndexedMatching G I)
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableRel M.edgeGraph.Adj]
    [DecidableRel (D ⊔ M.edgeGraph).Adj]
    (d : ℕ) (hdegree : ∀ x, D.degree x ≤ d) :
    ∀ x, (D ⊔ M.edgeGraph).degree x ≤ d + 1 := by
  intro x
  exact (degree_sup_le D M.edgeGraph x).trans
    (Nat.add_le_add (hdegree x) (M.edgeGraph_degree_le_one x))

/-- Neighbors in a finite vertex set that occur later in an injective order. -/
def laterNeighbors {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (time : V → ℕ) (x : V) : Finset V :=
  s.filter fun y => G.Adj x y ∧ time x < time y

/-- An ordered set with at most B later neighbors per vertex has an
independent subset of at least a 1/(B+1) fraction of its vertices. -/
theorem exists_large_independent_of_later_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (time : V → ℕ) (htime : Function.Injective time)
    (B : ℕ)
    (hlater : ∀ x ∈ s, (laterNeighbors G s time x).card ≤ B) :
    ∃ T : Finset V, T ⊆ s ∧ G.IsIndepSet (T : Set V) ∧
      s.card ≤ (B + 1) * T.card := by
  classical
  have aux : ∀ t : Finset V, t ⊆ s →
      ∃ T : Finset V, T ⊆ t ∧ G.IsIndepSet (T : Set V) ∧
        t.card ≤ (B + 1) * T.card := by
    intro t
    refine Finset.strongInductionOn t ?_
    intro t ih hts
    by_cases ht : t.Nonempty
    · obtain ⟨x, hxt, hmin⟩ := Finset.exists_min_image t time ht
      let N : Finset V := (t.erase x).filter (G.Adj x)
      let R : Finset V := (t.erase x).filter (fun y => ¬ G.Adj x y)
      have hRsub : R ⊆ t := by
        intro y hy
        exact (Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).2
      have hRstrict : R ⊂ t := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hRsub, ?_⟩
        intro h
        have hxR : x ∈ R := h ▸ hxt
        exact (Finset.mem_erase.mp (Finset.mem_filter.mp hxR).1).1 rfl
      obtain ⟨U, hUsub, hUind, hUcard⟩ := ih R hRstrict (hRsub.trans hts)
      have hNle : N.card ≤ B := by
        calc
          N.card ≤ (laterNeighbors G s time x).card := by
            apply Finset.card_le_card
            intro y hy
            have hyt : y ∈ t :=
              (Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).2
            have hyne : y ≠ x :=
              (Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).1
            have hlt : time x < time y := by
              apply lt_of_le_of_ne (hmin y hyt)
              intro heq
              exact hyne (htime heq).symm
            exact Finset.mem_filter.mpr
              ⟨hts hyt, (Finset.mem_filter.mp hy).2, hlt⟩
          _ ≤ B := hlater x (hts hxt)
      have hcardParts : N.card + R.card = (t.erase x).card := by
        exact Finset.card_filter_add_card_filter_not (s := t.erase x) (G.Adj x)
      have hcardErase : (t.erase x).card + 1 = t.card := by
        simpa using Finset.card_erase_add_one hxt
      have hxnotU : x ∉ U := by
        intro hxU
        have hxR := hUsub hxU
        exact (Finset.mem_erase.mp (Finset.mem_filter.mp hxR).1).1 rfl
      have hTsub : insert x U ⊆ t := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hyU
        · exact hxt
        · exact hRsub (hUsub hyU)
      have hTind : G.IsIndepSet ((insert x U : Finset V) : Set V) := by
        intro a ha b hb hne hab
        change a ∈ insert x U at ha
        change b ∈ insert x U at hb
        rcases Finset.mem_insert.mp ha with rfl | haU
        · rcases Finset.mem_insert.mp hb with rfl | hbU
          · exact hne rfl
          · exact (Finset.mem_filter.mp (hUsub hbU)).2 hab
        · rcases Finset.mem_insert.mp hb with rfl | hbU
          · exact (Finset.mem_filter.mp (hUsub haU)).2 hab.symm
          · exact hUind haU hbU hne hab
      refine ⟨insert x U, hTsub, hTind, ?_⟩
      rw [Finset.card_insert_of_notMem hxnotU, Nat.mul_add, mul_one]
      omega
    · have he : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
      subst t
      exact ⟨∅, by simp, by simp, by simp⟩
  exact aux s (Finset.Subset.refl s)

/-- Independence number converts the ordered-neighborhood certificate to
the numerical bound used for unmatched vertices and threshold crossings. -/
theorem card_le_independence_mul_succ_of_later_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (time : V → ℕ) (htime : Function.Injective time)
    (B m : ℕ) (halpha : independenceNumber G ≤ m)
    (hlater : ∀ x ∈ s, (laterNeighbors G s time x).card ≤ B) :
    s.card ≤ m * (B + 1) := by
  obtain ⟨T, _, hTind, hcard⟩ :=
    exists_large_independent_of_later_neighbors G s time htime B hlater
  have hTcard : T.card ≤ m :=
    (stable_card_le_independenceNumber G hTind).trans halpha
  calc
    s.card ≤ (B + 1) * T.card := hcard
    _ ≤ (B + 1) * m := Nat.mul_le_mul_left _ hTcard
    _ = m * (B + 1) := Nat.mul_comm _ _

/-- Final-graph distance certificates bound a time-ordered exceptional set.
A greedy construction will supply the distance premise for unmatched vertices
and, threshold by threshold, for the high ends of crossing matching edges. -/
theorem card_le_of_later_adj_edist_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G J : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel J.Adj]
    (s : Finset V) (time : V → ℕ) (htime : Function.Injective time)
    (k r m : ℕ) (halpha : independenceNumber G ≤ m)
    (hdegree : ∀ x, J.degree x ≤ k)
    (hclose : ∀ x ∈ s, ∀ y ∈ s,
      time x < time y → G.Adj x y → J.edist x y ≤ (r : ℕ∞)) :
    s.card ≤ m * ((∑ n ∈ Finset.range (r + 1), k ^ n) + 1) := by
  let B := ∑ n ∈ Finset.range (r + 1), k ^ n
  apply card_le_independence_mul_succ_of_later_neighbors G s time htime B m halpha
  intro x hx
  calc
    (laterNeighbors G s time x).card ≤
        (Finset.univ.filter fun y => J.edist x y ≤ (r : ℕ∞)).card := by
      apply Finset.card_le_card
      intro y hy
      obtain ⟨hyS, hadj, hlt⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hclose x hx y hyS hlt hadj⟩
    _ ≤ B := card_edist_ball_le_sum_pow J k r hdegree x

/-- The high-weight endpoint of each matching edge crossing a threshold. -/
noncomputable def crossingHigh
    {V I : Type*} [Fintype I] [DecidableEq V]
    {G : SimpleGraph V} (M : IndexedMatching G I)
    (w : V → ℝ) (a : ℝ) : Finset V := by
  classical
  exact ((Finset.univ : Finset I).filter
    fun i => w (M.endpoint i true) ≤ a ∧ a < w (M.endpoint i false)).image
      (fun i => M.endpoint i false)

theorem mem_crossingHigh
    {V I : Type*} [Fintype I] [DecidableEq V]
    {G : SimpleGraph V} (M : IndexedMatching G I)
    (w : V → ℝ) (a : ℝ) (x : V) :
    x ∈ crossingHigh M w a ↔
      ∃ i : I, w (M.endpoint i true) ≤ a ∧
        a < w (M.endpoint i false) ∧ x = M.endpoint i false := by
  classical
  simp [crossingHigh, and_assoc, eq_comm]

theorem IndexedMatching.endpoint_left_injective
    {V I : Type*} {G : SimpleGraph V}
    (M : IndexedMatching G I) :
    Function.Injective (fun i => M.endpoint i false) := by
  intro i j h
  exact congrArg Prod.fst (M.injective (show
    (fun p : I × Bool => M.endpoint p.1 p.2) (i, false) =
      (fun p : I × Bool => M.endpoint p.1 p.2) (j, false) from h))

theorem crossingHigh_card_eq
    {V I : Type*} [Fintype I] [DecidableEq V]
    {G : SimpleGraph V} (M : IndexedMatching G I)
    (w : V → ℝ) (a : ℝ) :
    (crossingHigh M w a).card =
      ((Finset.univ : Finset I).filter
        fun i => w (M.endpoint i true) ≤ a ∧ a < w (M.endpoint i false)).card := by
  classical
  exact Finset.card_image_of_injective _ M.endpoint_left_injective

/-- Every threshold crossing set has the paper's cardinal bound once later
adjacent high endpoints are certified to lie in the final radius-r ball. -/
theorem crossingHigh_card_le
    {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (M : IndexedMatching G I) (time : V → ℕ)
    (htime : Function.Injective time) (w : V → ℝ)
    (d r m : ℕ) (halpha : independenceNumber G ≤ m)
    (hdegree : ∀ x, D.degree x ≤ d)
    (hclose : ∀ a : ℝ, ∀ i j : I,
      w (M.endpoint i true) ≤ a → a < w (M.endpoint i false) →
      w (M.endpoint j true) ≤ a → a < w (M.endpoint j false) →
      time (M.endpoint i false) < time (M.endpoint j false) →
      G.Adj (M.endpoint i false) (M.endpoint j false) →
      (D ⊔ M.edgeGraph).edist (M.endpoint i false) (M.endpoint j false) ≤
        (r : ℕ∞))
    (a : ℝ) :
    (crossingHigh M w a).card ≤
      m * ((∑ n ∈ Finset.range (r + 1), (d + 1) ^ n) + 1) := by
  classical
  apply card_le_of_later_adj_edist_le G (D ⊔ M.edgeGraph)
    (crossingHigh M w a) time htime (d + 1) r m halpha
    (M.degree_sup_edgeGraph_le D d hdegree)
  intro x hx y hy hlt hadj
  obtain ⟨i, hilow, hihigh, rfl⟩ := (mem_crossingHigh M w a x).mp hx
  obtain ⟨j, hjlow, hjhigh, rfl⟩ := (mem_crossingHigh M w a y).mp hy
  exact hclose a i j hilow hihigh hjlow hjhigh hlt hadj

/-- Finite layer cake: if at most C intervals cover each threshold in
[0,1], their total length is at most C. -/
theorem sum_interval_lengths_le_of_overlap
    {I : Type*} [Fintype I]
    (lo hi : I → ℝ) (C : ℕ)
    (hlo : ∀ i, 0 ≤ lo i) (hhi : ∀ i, hi i ≤ 1)
    (hlohi : ∀ i, lo i ≤ hi i)
    (hcap : ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      ((Finset.univ : Finset I).filter fun i => lo i ≤ a ∧ a < hi i).card ≤ C) :
    (∑ i : I, (hi i - lo i)) ≤ (C : ℝ) := by
  classical
  let f : I → ℝ → ℝ := fun i a =>
    (Set.Ico (lo i) (hi i)).indicator (fun _ => 1) a
  have hint (i : I) : MeasureTheory.Integrable (f i) MeasureTheory.volume := by
    dsimp [f]
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Ico]
    exact MeasureTheory.integrableOn_const (by simp [Real.volume_Ico]) (by simp)
  have hright : MeasureTheory.Integrable
      ((Set.Icc (0 : ℝ) 1).indicator (fun _ => (C : ℝ)))
      MeasureTheory.volume := by
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Icc]
    exact MeasureTheory.integrableOn_const (by simp [Real.volume_Icc]) (by simp)
  have hpoint (a : ℝ) :
      (∑ i : I, f i a) ≤
        (Set.Icc (0 : ℝ) 1).indicator (fun _ => (C : ℝ)) a := by
    by_cases ha : a ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem ha]
      have hs :
          (∑ i : I, f i a) =
            (((Finset.univ : Finset I).filter
              fun i => lo i ≤ a ∧ a < hi i).card : ℝ) := by
        simp [f, Set.indicator]
      rw [hs]
      exact_mod_cast hcap a ha.1 ha.2
    · rw [Set.indicator_of_notMem ha]
      have hnone (i : I) : a ∉ Set.Ico (lo i) (hi i) := by
        intro h
        exact ha ⟨(hlo i).trans h.1, (le_of_lt h.2).trans (hhi i)⟩
      simp [f, Set.indicator_of_notMem, hnone]
  calc
    (∑ i : I, (hi i - lo i)) =
        ∑ i : I, ∫ a : ℝ, f i a := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [f]
      rw [MeasureTheory.integral_indicator measurableSet_Ico]
      simp [hlohi i]
    _ = ∫ a : ℝ, ∑ i : I, f i a := by
      exact (MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hint i)).symm
    _ ≤ ∫ a : ℝ,
        (Set.Icc (0 : ℝ) 1).indicator (fun _ => (C : ℝ)) a := by
      exact MeasureTheory.integral_mono
        (MeasureTheory.integrable_finsetSum _ (fun i _ => hint i)) hright hpoint
    _ = C := by
      rw [MeasureTheory.integral_indicator measurableSet_Icc]
      simp

/-- The layer-cake weight-loss estimate for a pair-indexed matching, supplied
with a uniform bound on threshold crossing edges. -/
theorem IndexedMatching.weight_loss_le_of_crossing_bound
    {V I : Type*} [Fintype I] [DecidableEq V]
    {G : SimpleGraph V} (M : IndexedMatching G I)
    (w : V → ℝ) (C : ℕ)
    (hweight : ∀ v, 0 ≤ w v ∧ w v ≤ 1)
    (horder : ∀ i, w (M.endpoint i true) ≤ w (M.endpoint i false))
    (hcross : ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      (crossingHigh M w a).card ≤ C) :
    (∑ i : I, |w (M.endpoint i false) - w (M.endpoint i true)|) ≤
      (C : ℝ) := by
  classical
  have hraw := sum_interval_lengths_le_of_overlap
    (fun i => w (M.endpoint i true))
    (fun i => w (M.endpoint i false)) C
    (fun i => (hweight _).1) (fun i => (hweight _).2) horder
    (by
      intro a h0 h1
      rw [← crossingHigh_card_eq M w a]
      exact hcross a h0 h1)
  simpa only [abs_of_nonneg, sub_nonneg.mpr, horder] using hraw

/-- The bounded weight-loss conclusion from final-graph neighborhood
certificates for all threshold crossing sets. -/
theorem IndexedMatching.weight_loss_le_of_later_crossings_close
    {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (M : IndexedMatching G I) (time : V → ℕ)
    (htime : Function.Injective time) (w : V → ℝ)
    (d r m : ℕ) (halpha : independenceNumber G ≤ m)
    (hdegree : ∀ x, D.degree x ≤ d)
    (hweight : ∀ v, 0 ≤ w v ∧ w v ≤ 1)
    (horder : ∀ i, w (M.endpoint i true) ≤ w (M.endpoint i false))
    (hclose : ∀ a : ℝ, ∀ i j : I,
      w (M.endpoint i true) ≤ a → a < w (M.endpoint i false) →
      w (M.endpoint j true) ≤ a → a < w (M.endpoint j false) →
      time (M.endpoint i false) < time (M.endpoint j false) →
      G.Adj (M.endpoint i false) (M.endpoint j false) →
      (D ⊔ M.edgeGraph).edist (M.endpoint i false) (M.endpoint j false) ≤
        (r : ℕ∞)) :
    (∑ i : I, |w (M.endpoint i false) - w (M.endpoint i true)|) ≤
      ((m * ((∑ n ∈ Finset.range (r + 1), (d + 1) ^ n) + 1) : ℕ) : ℝ) := by
  classical
  apply M.weight_loss_le_of_crossing_bound w _
    hweight horder
  intro a _ _
  exact crossingHigh_card_le G D M time htime w d r m
    halpha hdegree hclose a

/-- Deleting a matching pair preserves a set closed under matching partners;
global perfection is unnecessary. -/
theorem matching_closed_sdiff_pair
    {V : Type*} [DecidableEq V] (P : SimpleGraph V)
    (hunique : ∀ a b c, P.Adj a b → P.Adj a c → b = c)
    {s : Finset V}
    (hclosed : ∀ a ∈ s, ∀ b, P.Adj a b → b ∈ s)
    {x y : V} (hxy : P.Adj x y) :
    ∀ a ∈ s \ {x, y}, ∀ b, P.Adj a b → b ∈ s \ {x, y} := by
  intro a ha b hab
  have has : a ∈ s := (Finset.mem_sdiff.mp ha).1
  have hax : a ≠ x := by
    intro h
    subst a
    exact (Finset.mem_sdiff.mp ha).2 (by simp)
  have hay : a ≠ y := by
    intro h
    subst a
    exact (Finset.mem_sdiff.mp ha).2 (by simp)
  have hbs : b ∈ s := hclosed a has b hab
  have hbx : b ≠ x := by
    intro h
    subst b
    exact hay ((hunique x y a hxy hab.symm).symm)
  have hby : b ≠ y := by
    intro h
    subst b
    exact hax ((hunique y x a hxy.symm hab.symm).symm)
  exact Finset.mem_sdiff.mpr ⟨hbs, by simp [hbx, hby]⟩

/-- Independent transversal on a matching-closed subset, assuming matching
perfection only on that subset. This is suited to partial matchings. -/
theorem independent_transversal_on_partial
    {V : Type*} [Fintype V] [DecidableEq V]
    (D P : SimpleGraph V)
    (hunique : ∀ a b c, P.Adj a b → P.Adj a c → b = c)
    (hedgeDisjoint : ∀ a b, D.Adj a b → ¬ P.Adj a b)
    (hcycles : NoMatchingEdgeCycle D P)
    (s : Finset V)
    (hperfect : ∀ a ∈ s, ∃ b, P.Adj a b)
    (hclosed : ∀ a ∈ s, ∀ b, P.Adj a b → b ∈ s) :
    ∃ T : Finset V, T ⊆ s ∧ D.IsIndepSet (T : Set V) ∧
      ∀ a b, P.Adj a b → a ∈ s → (a ∈ T ↔ b ∉ T) := by
  classical
  have aux : ∀ t : Finset V, t ⊆ s →
      (∀ a ∈ t, ∀ b, P.Adj a b → b ∈ t) →
      ∃ T : Finset V, T ⊆ t ∧ D.IsIndepSet (T : Set V) ∧
        ∀ a b, P.Adj a b → a ∈ t → (a ∈ T ↔ b ∉ T) := by
    intro t
    refine Finset.strongInductionOn t ?_
    intro t ih hts htclosed
    by_cases ht : t.Nonempty
    · let Dt := spanningInduce D t
      let Pt := spanningInduce P t
      have hDt : Dt ≤ D := spanningInduce_le D t
      have hPt : Pt ≤ P := spanningInduce_le P t
      have hcycles_t : NoMatchingEdgeCycle Dt Pt := hcycles.mono hDt hPt
      have hperfect_t : ∀ a ∈ t, ∃ b, Pt.Adj a b := by
        intro a ha
        obtain ⟨b, hab⟩ := hperfect a (hts ha)
        exact ⟨b, ⟨ha, htclosed a ha b hab, hab⟩⟩
      have hdisj_t : ∀ a b, Dt.Adj a b → ¬ Pt.Adj a b := by
        intro a b hab hp
        exact hedgeDisjoint a b hab.2.2 hp.2.2
      obtain ⟨x, hxt, hxisol⟩ :=
        exists_isolated_on_support Dt Pt t ht
          (fun a b hab => hab.1)
          (fun a b hab => hab.1)
          hperfect_t hdisj_t hcycles_t
      obtain ⟨y, hxy⟩ := hperfect x (hts hxt)
      have hyt : y ∈ t := htclosed x hxt y hxy
      let t' : Finset V := t \ {x, y}
      have hpairsub : ({x, y} : Finset V) ⊆ t := by
        intro z hz
        rcases Finset.mem_insert.mp hz with hzx | hzy
        · exact hzx ▸ hxt
        · simpa [Finset.mem_singleton.mp hzy] using hyt
      have hpairne : ({x, y} : Finset V).Nonempty := by simp
      have ht'lt : t' ⊂ t := Finset.sdiff_ssubset hpairsub hpairne
      have ht'closed : ∀ a ∈ t', ∀ b, P.Adj a b → b ∈ t' :=
        matching_closed_sdiff_pair P hunique htclosed hxy
      obtain ⟨T, hTsub, hTindep, hTcross⟩ :=
        ih t' ht'lt (Finset.sdiff_subset.trans hts) ht'closed
      have hxnotT : x ∉ T := by
        intro hxT
        have hx' := hTsub hxT
        simp [t'] at hx'
      have hynotT : y ∉ T := by
        intro hyT
        have hy' := hTsub hyT
        simp [t'] at hy'
      have hTsubset : insert x T ⊆ t := by
        intro a ha
        rcases Finset.mem_insert.mp ha with hax | haT
        · simpa [hax] using hxt
        · exact (Finset.mem_sdiff.mp (hTsub haT)).1
      have hTindep' : D.IsIndepSet ((insert x T : Finset V) : Set V) := by
        intro a ha b hb hne hab
        change a ∈ insert x T at ha
        change b ∈ insert x T at hb
        rcases Finset.mem_insert.mp ha with hax | haT
        · subst a
          rcases Finset.mem_insert.mp hb with hbx | hbT
          · exact hne hbx.symm
          · have hbt : b ∈ t := (Finset.mem_sdiff.mp (hTsub hbT)).1
            exact hxisol b (show Dt.Adj x b from ⟨hxt, hbt, hab⟩)
        · rcases Finset.mem_insert.mp hb with hbx | hbT
          · subst b
            have hat : a ∈ t := (Finset.mem_sdiff.mp (hTsub haT)).1
            exact hxisol a (show Dt.Adj x a from ⟨hxt, hat, hab.symm⟩)
          · exact hTindep haT hbT hne hab
      refine ⟨insert x T, hTsubset, hTindep', ?_⟩
      intro a b hab hat
      by_cases hax : a = x
      · subst a
        have hby : b = y := hunique x b y hab hxy
        subst b
        simp [Finset.mem_insert, hxy.ne.symm, hynotT]
      · by_cases hay : a = y
        · subst a
          have hbx : b = x := hunique y b x hab hxy.symm
          subst b
          simp [Finset.mem_insert, hxy.ne.symm, hynotT]
        · have hat' : a ∈ t' := by
            simp [t', hat, hax, hay]
          have hbt' : b ∈ t' := ht'closed a hat' b hab
          have hbx : b ≠ x := by
            intro h
            subst b
            have hb' := hbt'
            simp [t'] at hb'
          simpa [Finset.mem_insert, hax, hbx] using hTcross a b hab hat'
    · have he : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
      subst t
      refine ⟨∅, by simp, ?_, ?_⟩
      · intro a ha
        simp at ha
      · intro a b hab ha
        simp at ha
  exact aux s (Finset.Subset.refl s) hclosed

/-- Vertices of a selected family of matching pairs. -/
noncomputable def IndexedMatching.pairVertices
    {V I : Type*} [DecidableEq V]
    {G : SimpleGraph V} (M : IndexedMatching G I)
    (S : Finset I) : Finset V := by
  classical
  exact S.biUnion fun i => {M.endpoint i false, M.endpoint i true}

theorem IndexedMatching.mem_pairVertices
    {V I : Type*} [DecidableEq V]
    {G : SimpleGraph V} (M : IndexedMatching G I)
    (S : Finset I) (x : V) :
    x ∈ M.pairVertices S ↔
      ∃ i ∈ S, x = M.endpoint i false ∨ x = M.endpoint i true := by
  classical
  simp [IndexedMatching.pairVertices, Finset.mem_biUnion]

theorem IndexedMatching.pairVertices_perfect
    {V I : Type*} [DecidableEq V]
    {G : SimpleGraph V} (M : IndexedMatching G I)
    (S : Finset I) :
    ∀ x ∈ M.pairVertices S, ∃ y, M.edgeGraph.Adj x y := by
  intro x hx
  obtain ⟨i, _, hleft | hright⟩ := (M.mem_pairVertices S x).mp hx
  · subst x
    exact ⟨M.endpoint i true, M.edgeGraph_adj_endpoints i⟩
  · subst x
    exact ⟨M.endpoint i false, (M.edgeGraph_adj_endpoints i).symm⟩

theorem IndexedMatching.pairVertices_closed
    {V I : Type*} [DecidableEq V]
    {G : SimpleGraph V} (M : IndexedMatching G I)
    (S : Finset I) :
    ∀ x ∈ M.pairVertices S, ∀ y,
      M.edgeGraph.Adj x y → y ∈ M.pairVertices S := by
  intro x hx y hxy
  obtain ⟨i, hi, hleft | hright⟩ := (M.mem_pairVertices S x).mp hx
  · subst x
    exact (M.mem_pairVertices S y).mpr
      ⟨i, hi, Or.inr (M.edgeGraph_unique_of_left i hxy)⟩
  · subst x
    exact (M.mem_pairVertices S y).mpr
      ⟨i, hi, Or.inl (M.edgeGraph_unique_of_right i hxy)⟩

/-- The partial-matching transversal lemma specialized to a family of
indexed matching edges. -/
theorem IndexedMatching.independent_transversal_pairs
    {V I : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (M : IndexedMatching G I)
    (D : SimpleGraph V)
    (hedgeDisjoint : ∀ a b, D.Adj a b → ¬ M.edgeGraph.Adj a b)
    (hcycles : NoMatchingEdgeCycle D M.edgeGraph)
    (S : Finset I) :
    ∃ T : Finset V, T ⊆ M.pairVertices S ∧
      D.IsIndepSet (T : Set V) ∧
      ∀ i ∈ S,
        (M.endpoint i false ∈ T ↔ M.endpoint i true ∉ T) := by
  obtain ⟨T, hTsub, hTind, hTcross⟩ :=
    independent_transversal_on_partial D M.edgeGraph
      (fun _ _ _ hab hac => M.edgeGraph_adj_unique hab hac)
      hedgeDisjoint hcycles (M.pairVertices S)
      (M.pairVertices_perfect S) (M.pairVertices_closed S)
  refine ⟨T, hTsub, hTind, ?_⟩
  intro i hi
  apply hTcross _ _ (M.edgeGraph_adj_endpoints i)
  exact (M.mem_pairVertices S _).mpr ⟨i, hi, Or.inl rfl⟩

/-- Adding graph edges can only decrease extended distance. -/
theorem edist_antitone
    {V : Type*} {J K : SimpleGraph V}
    (hJK : J ≤ K) (x y : V) :
    K.edist x y ≤ J.edist x y := by
  by_cases htop : J.edist x y = ⊤
  · simp [htop]
  · obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top htop
    let q : K.Walk x y := p.map (SimpleGraph.Hom.ofLE hJK)
    calc
      K.edist x y ≤ (q.length : ℕ∞) := q.edist_le
      _ = (p.length : ℕ∞) := by exact_mod_cast p.length_map (SimpleGraph.Hom.ofLE hJK)
      _ = J.edist x y := hp

/-- A cycle in a graph whose edges stay inside s uses at most s.card
vertices. The graph may retain additional isolated ambient vertices. -/
theorem cycle_length_le_edge_support
    {V : Type*} [DecidableEq V]
    (J : SimpleGraph V) (s : Finset V)
    (hedge : ∀ a b, J.Adj a b → a ∈ s ∧ b ∈ s)
    {u : V} {c : J.Walk u u} (hc : c.IsCycle) :
    c.length ≤ s.card := by
  have hsubset : c.support.tail.toFinset ⊆ s := by
    intro v hv
    have hvsupport : v ∈ c.support := List.mem_of_mem_tail (List.mem_toFinset.mp hv)
    obtain ⟨e, he, hve⟩ :=
      (c.mem_support_iff_exists_mem_edges_of_not_nil hc.not_nil).mp hvsupport
    obtain ⟨⟨a, b⟩, rfl⟩ := Sym2.mk_surjective e
    have hab : J.Adj a b := c.edges_subset_edgeSet he
    rcases Sym2.mem_iff.mp hve with h | h
    · simpa [h] using (hedge a b hab).1
    · simpa [h] using (hedge a b hab).2
  have hcard := Finset.card_le_card hsubset
  rw [List.toFinset_card_of_nodup hc.support_nodup] at hcard
  simpa [List.length_tail, c.length_support] using hcard

/-- Excluding matching-edge cycles up to the support size gives the unrestricted
cycle condition after restricting both graphs to that support. -/
theorem no_matching_edge_cycle_spanningInduce_of_short
    {V : Type*} [DecidableEq V]
    (D P : SimpleGraph V) (s : Finset V) (L : ℕ)
    (hcard : s.card ≤ L)
    (hshort : ∀ (u : V) (c : (D ⊔ P).Walk u u),
      c.IsCycle → c.length ≤ L →
        ∀ e ∈ c.edges, e ∉ P.edgeSet) :
    NoMatchingEdgeCycle (spanningInduce D s) (spanningInduce P s) := by
  intro u c hc e he
  have hedge :
      ∀ a b, (spanningInduce D s ⊔ spanningInduce P s).Adj a b →
        a ∈ s ∧ b ∈ s := by
    intro a b hab
    rcases (SimpleGraph.sup_adj _ _ a b).mp hab with hD | hP
    · exact ⟨hD.1, hD.2.1⟩
    · exact ⟨hP.1, hP.2.1⟩
  have hlen : c.length ≤ L :=
    (cycle_length_le_edge_support _ s hedge hc).trans hcard
  have hle : spanningInduce D s ⊔ spanningInduce P s ≤ D ⊔ P :=
    sup_le_sup (spanningInduce_le D s) (spanningInduce_le P s)
  have hlen' : (c.mapLe hle).length ≤ L := by
    change (c.map (SimpleGraph.Hom.ofLE hle)).length ≤ L
    rw [c.length_map (SimpleGraph.Hom.ofLE hle)]
    exact hlen
  have hnot := hshort u (c.mapLe hle) (hc.mapLe hle) hlen' e
    (by simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using he)
  intro heP
  exact hnot (SimpleGraph.edgeSet_mono (spanningInduce_le P s) heP)

theorem IndexedMatching.pairVertices_card_le_two_mul
    {V I : Type*} [DecidableEq V]
    {G : SimpleGraph V} (M : IndexedMatching G I)
    (S : Finset I) :
    (M.pairVertices S).card ≤ 2 * S.card := by
  classical
  calc
    (M.pairVertices S).card =
        (S.biUnion fun i => ({M.endpoint i false, M.endpoint i true} : Finset V)).card := rfl
    _ ≤ ∑ i ∈ S, ({M.endpoint i false, M.endpoint i true} : Finset V).card :=
      Finset.card_biUnion_le
    _ = ∑ i ∈ S, 2 := by
      apply Finset.sum_congr rfl
      intro i _
      have hne : M.endpoint i false ≠ M.endpoint i true := (M.adjacent i).ne
      simp [hne]
    _ = 2 * S.card := by simp [Nat.mul_comm]

/-- The paper's bounded-cycle condition suffices for a selected family of
matching pairs whenever their support has at most L vertices. -/
theorem IndexedMatching.independent_transversal_pairs_of_short
    {V I : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (M : IndexedMatching G I)
    (D : SimpleGraph V)
    (hedgeDisjoint : ∀ a b, D.Adj a b → ¬ M.edgeGraph.Adj a b)
    (S : Finset I) (L : ℕ)
    (hcard : (M.pairVertices S).card ≤ L)
    (hshort : ∀ (u : V) (c : (D ⊔ M.edgeGraph).Walk u u),
      c.IsCycle → c.length ≤ L →
        ∀ e ∈ c.edges, e ∉ M.edgeGraph.edgeSet) :
    ∃ T : Finset V, T ⊆ M.pairVertices S ∧
      D.IsIndepSet (T : Set V) ∧
      ∀ i ∈ S,
        (M.endpoint i false ∈ T ↔ M.endpoint i true ∉ T) := by
  let s := M.pairVertices S
  let Dt := spanningInduce D s
  let Pt := spanningInduce M.edgeGraph s
  have hcycles : NoMatchingEdgeCycle Dt Pt :=
    no_matching_edge_cycle_spanningInduce_of_short
      D M.edgeGraph s L hcard hshort
  have hunique : ∀ a b c, Pt.Adj a b → Pt.Adj a c → b = c := by
    intro a b c hab hac
    exact M.edgeGraph_adj_unique hab.2.2 hac.2.2
  have hdisj : ∀ a b, Dt.Adj a b → ¬ Pt.Adj a b := by
    intro a b hab hp
    exact hedgeDisjoint a b hab.2.2 hp.2.2
  have hperfect : ∀ a ∈ s, ∃ b, Pt.Adj a b := by
    intro a ha
    obtain ⟨b, hab⟩ := M.pairVertices_perfect S a ha
    exact ⟨b, ⟨ha, M.pairVertices_closed S a ha b hab, hab⟩⟩
  have hclosed : ∀ a ∈ s, ∀ b, Pt.Adj a b → b ∈ s := by
    intro a ha b hab
    exact hab.2.1
  obtain ⟨T, hTsub, hTind, hTcross⟩ :=
    independent_transversal_on_partial Dt Pt hunique hdisj
      hcycles s hperfect hclosed
  have hTindD : D.IsIndepSet (T : Set V) := by
    intro a ha b hb hne hab
    exact hTind ha hb hne ⟨hTsub ha, hTsub hb, hab⟩
  refine ⟨T, hTsub, hTindD, ?_⟩
  intro i hi
  have hleft : M.endpoint i false ∈ s :=
    (M.mem_pairVertices S _).mpr ⟨i, hi, Or.inl rfl⟩
  have hright : M.endpoint i true ∈ s :=
    (M.mem_pairVertices S _).mpr ⟨i, hi, Or.inr rfl⟩
  exact hTcross _ _
    ⟨hleft, hright, M.edgeGraph_adj_endpoints i⟩ hleft

/-- A precise local certificate for the two bounds in the greedy matching
lemma. The before graph is the full-vertex graph used when each selected
vertex was processed; the final matching graph contains every before graph.
The two local premises state the unmatched ineligibility rule and the
maximum-weight eligible-partner rule. -/
theorem matching_bounds_of_greedy_trace
    {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (M : IndexedMatching G I) (X : Finset V)
    (time : V → ℕ) (htime : Function.Injective time)
    (before : V → SimpleGraph V)
    (hbefore : ∀ x, before x ≤ D ⊔ M.edgeGraph)
    (d r m : ℕ) (halpha : independenceNumber G ≤ m)
    (hdegree : ∀ x, D.degree x ≤ d)
    (w : V → ℝ) (hweight : ∀ v, 0 ≤ w v ∧ w v ≤ 1)
    (horder : ∀ i, w (M.endpoint i true) ≤ w (M.endpoint i false))
    (hunmatchedIneligible : ∀ x ∈ X, ∀ y ∈ X,
      time x < time y → G.Adj x y →
      (before x).edist x y ≤ (r : ℕ∞))
    (hpartnerMaximal : ∀ i j : I,
      w (M.endpoint i true) < w (M.endpoint i false) →
      time (M.endpoint i false) < time (M.endpoint j false) →
      w (M.endpoint i true) < w (M.endpoint j false) →
      G.Adj (M.endpoint i false) (M.endpoint j false) →
      (before (M.endpoint i false)).edist
        (M.endpoint i false) (M.endpoint j false) ≤ (r : ℕ∞)) :
    X.card ≤
        m * ((∑ n ∈ Finset.range (r + 1), (d + 1) ^ n) + 1) ∧
      (∑ i : I,
        |w (M.endpoint i false) - w (M.endpoint i true)|) ≤
        ((m * ((∑ n ∈ Finset.range (r + 1), (d + 1) ^ n) + 1) : ℕ) : ℝ) := by
  classical
  have hdegreeFinal : ∀ x, (D ⊔ M.edgeGraph).degree x ≤ d + 1 :=
    M.degree_sup_edgeGraph_le D d hdegree
  have hXclose : ∀ x ∈ X, ∀ y ∈ X,
      time x < time y → G.Adj x y →
      (D ⊔ M.edgeGraph).edist x y ≤ (r : ℕ∞) := by
    intro x hx y hy hlt hadj
    exact (edist_antitone (hbefore x) x y).trans
      (hunmatchedIneligible x hx y hy hlt hadj)
  have hMclose : ∀ a : ℝ, ∀ i j : I,
      w (M.endpoint i true) ≤ a → a < w (M.endpoint i false) →
      w (M.endpoint j true) ≤ a → a < w (M.endpoint j false) →
      time (M.endpoint i false) < time (M.endpoint j false) →
      G.Adj (M.endpoint i false) (M.endpoint j false) →
      (D ⊔ M.edgeGraph).edist (M.endpoint i false) (M.endpoint j false) ≤
        (r : ℕ∞) := by
    intro a i j hilow hihigh _ hjhigh hlt hadj
    exact (edist_antitone (hbefore (M.endpoint i false))
      (M.endpoint i false) (M.endpoint j false)).trans
        (hpartnerMaximal i j (lt_of_le_of_lt hilow hihigh)
          hlt (lt_of_le_of_lt hilow hjhigh) hadj)
  constructor
  · exact card_le_of_later_adj_edist_le G (D ⊔ M.edgeGraph)
      X time htime (d + 1) r m halpha hdegreeFinal hXclose
  · exact M.weight_loss_le_of_later_crossings_close
      G D time htime w d r m halpha hdegree
      hweight horder hMclose

/-- Eligible partners for one greedy step, measured in the current full
vertex graph D + P. -/
noncomputable def eligiblePartners
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D P : SimpleGraph V) (R : Finset V) (r : ℕ) (v : V) :
    Finset V := by
  classical
  exact (R.erase v).filter fun u =>
    G.Adj v u ∧ (r : ℕ∞) < (D ⊔ P).edist v u

theorem mem_eligiblePartners
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D P : SimpleGraph V) (R : Finset V) (r : ℕ) (v u : V) :
    u ∈ eligiblePartners G D P R r v ↔
      u ∈ R ∧ u ≠ v ∧ G.Adj v u ∧
        (r : ℕ∞) < (D ⊔ P).edist v u := by
  classical
  simp [eligiblePartners, and_assoc, and_left_comm, and_comm]

/-- The finite choice made at a single greedy step: a maximum-weight
unprocessed vertex, followed by a maximum-weight eligible partner if any. -/
structure GreedyChoice
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D P : SimpleGraph V) (R : Finset V)
    (w : V → ℝ) (r : ℕ) where
  selected : V
  selected_mem : selected ∈ R
  selected_max : ∀ x ∈ R, w x ≤ w selected
  partner : Option V
  partner_optimal : match partner with
    | none => eligiblePartners G D P R r selected = ∅
    | some u => u ∈ eligiblePartners G D P R r selected ∧
        ∀ x ∈ eligiblePartners G D P R r selected, w x ≤ w u

theorem exists_greedyChoice
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D P : SimpleGraph V) (R : Finset V) (hR : R.Nonempty)
    (w : V → ℝ) (r : ℕ) :
    Nonempty (GreedyChoice G D P R w r) := by
  classical
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image R w hR
  let E := eligiblePartners G D P R r v
  by_cases hE : E.Nonempty
  · obtain ⟨u, hu, humax⟩ := Finset.exists_max_image E w hE
    exact ⟨⟨v, hv, hmax, some u, by
      dsimp only
      exact ⟨hu, humax⟩⟩⟩
  · have hEempty : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    exact ⟨⟨v, hv, hmax, none, by
      dsimp only
      exact hEempty⟩⟩

theorem GreedyChoice.partner_mem_unprocessed
    {V : Type*} [Fintype V] [DecidableEq V]
    {G D P : SimpleGraph V} {R : Finset V}
    {w : V → ℝ} {r : ℕ}
    (c : GreedyChoice G D P R w r) {u : V}
    (hpartner : c.partner = some u) :
    u ∈ R ∧ u ≠ c.selected ∧ G.Adj c.selected u ∧
      (r : ℕ∞) < (D ⊔ P).edist c.selected u := by
  have h := c.partner_optimal
  rw [hpartner] at h
  exact (mem_eligiblePartners G D P R r c.selected u).mp h.1

theorem GreedyChoice.selected_weight_ge_partner
    {V : Type*} [Fintype V] [DecidableEq V]
    {G D P : SimpleGraph V} {R : Finset V}
    {w : V → ℝ} {r : ℕ}
    (c : GreedyChoice G D P R w r) {u : V}
    (hpartner : c.partner = some u) :
    w u ≤ w c.selected :=
  c.selected_max u (c.partner_mem_unprocessed hpartner).1

/-- If no partner is chosen, every remaining G-neighbor lies in the
current radius-r ball. -/
theorem GreedyChoice.unmatched_neighbor_close
    {V : Type*} [Fintype V] [DecidableEq V]
    {G D P : SimpleGraph V} {R : Finset V}
    {w : V → ℝ} {r : ℕ}
    (c : GreedyChoice G D P R w r)
    (hpartner : c.partner = none)
    {y : V} (hyR : y ∈ R) (hadj : G.Adj c.selected y) :
    (D ⊔ P).edist c.selected y ≤ (r : ℕ∞) := by
  have hnone := c.partner_optimal
  rw [hpartner] at hnone
  apply le_of_not_gt
  intro hfar
  have hyeligible : y ∈ eligiblePartners G D P R r c.selected :=
    (mem_eligiblePartners G D P R r c.selected y).mpr
      ⟨hyR, hadj.ne.symm, hadj, hfar⟩
  rw [hnone] at hyeligible
  simp at hyeligible

/-- A later unprocessed neighbor heavier than the chosen partner must have
been ineligible at this step. -/
theorem GreedyChoice.heavier_neighbor_close
    {V : Type*} [Fintype V] [DecidableEq V]
    {G D P : SimpleGraph V} {R : Finset V}
    {w : V → ℝ} {r : ℕ}
    (c : GreedyChoice G D P R w r)
    {u : V} (hpartner : c.partner = some u)
    {y : V} (hyR : y ∈ R) (hadj : G.Adj c.selected y)
    (hweight : w u < w y) :
    (D ⊔ P).edist c.selected y ≤ (r : ℕ∞) := by
  have hopt := c.partner_optimal
  rw [hpartner] at hopt
  apply le_of_not_gt
  intro hfar
  have hyeligible : y ∈ eligiblePartners G D P R r c.selected :=
    (mem_eligiblePartners G D P R r c.selected y).mpr
      ⟨hyR, hadj.ne.symm, hadj, hfar⟩
  exact (not_lt_of_ge (hopt.2 y hyeligible)) hweight

/-- A graph with one edge, or no edge if the endpoints coincide. -/
def singletonEdgeGraph {V : Type*} (u v : V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {s(u, v)}

/-- The finite state of a greedy matching run. The history records the
selected vertex, optional partner, and the matching graph before that step. -/
structure WeightedGreedyState (V : Type*) where
  unprocessed : Finset V
  matching : SimpleGraph V
  unmatched : Finset V
  history : List (V × Option V × SimpleGraph V)

/-- Execute one certified maximum-weight choice. -/
def weightedGreedyAdvanceWithChoice
    {V : Type*} [Fintype V] [DecidableEq V]
    {G D : SimpleGraph V} {w : V → ℝ} {r : ℕ}
    (st : WeightedGreedyState V)
    (c : GreedyChoice G D st.matching st.unprocessed w r) :
    WeightedGreedyState V :=
  match c.partner with
  | none =>
      { unprocessed := st.unprocessed.erase c.selected
        matching := st.matching
        unmatched := insert c.selected st.unmatched
        history := st.history ++ [(c.selected, none, st.matching)] }
  | some u =>
      { unprocessed := (st.unprocessed.erase c.selected).erase u
        matching := st.matching ⊔ singletonEdgeGraph c.selected u
        unmatched := st.unmatched
        history := st.history ++ [(c.selected, some u, st.matching)] }

theorem weightedGreedyAdvanceWithChoice_card_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G D : SimpleGraph V} {w : V → ℝ} {r : ℕ}
    (st : WeightedGreedyState V)
    (c : GreedyChoice G D st.matching st.unprocessed w r) :
    (weightedGreedyAdvanceWithChoice st c).unprocessed.card <
      st.unprocessed.card := by
  cases h : c.partner with
  | none =>
      simpa [weightedGreedyAdvanceWithChoice, h] using
        (Finset.card_erase_lt_of_mem c.selected_mem)
  | some u =>
      have hfirst : (st.unprocessed.erase c.selected).card <
          st.unprocessed.card :=
        Finset.card_erase_lt_of_mem c.selected_mem
      have hsecond : ((st.unprocessed.erase c.selected).erase u).card ≤
          (st.unprocessed.erase c.selected).card :=
        Finset.card_erase_le
      simpa [weightedGreedyAdvanceWithChoice, h] using hsecond.trans_lt hfirst

/-- Choose and execute one step whenever unprocessed vertices remain. -/
noncomputable def weightedGreedyAdvance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ)
    (st : WeightedGreedyState V) (hR : st.unprocessed.Nonempty) :
    WeightedGreedyState V :=
  weightedGreedyAdvanceWithChoice st
    (Classical.choice
      (exists_greedyChoice G D st.matching st.unprocessed hR w r))

theorem weightedGreedyAdvance_card_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ)
    (st : WeightedGreedyState V) (hR : st.unprocessed.Nonempty) :
    (weightedGreedyAdvance G D w r st hR).unprocessed.card <
      st.unprocessed.card :=
  weightedGreedyAdvanceWithChoice_card_lt st _

/-- Iterate the greedy step with a finite fuel bound. -/
noncomputable def weightedGreedyRun
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ) :
    ℕ → WeightedGreedyState V → WeightedGreedyState V
  | 0, st => st
  | n + 1, st =>
      if hR : st.unprocessed.Nonempty then
        weightedGreedyRun G D w r n (weightedGreedyAdvance G D w r st hR)
      else st

theorem weightedGreedyRun_unprocessed_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ)
    (n : ℕ) (st : WeightedGreedyState V)
    (hcard : st.unprocessed.card ≤ n) :
    (weightedGreedyRun G D w r n st).unprocessed = ∅ := by
  induction n generalizing st with
  | zero =>
      have hzero : st.unprocessed = ∅ := by
        apply Finset.card_eq_zero.mp
        omega
      simp [weightedGreedyRun, hzero]
  | succ n ih =>
      by_cases hR : st.unprocessed.Nonempty
      · have hstep :=
          weightedGreedyAdvance_card_lt G D w r st hR
        have hcard' :
            (weightedGreedyAdvance G D w r st hR).unprocessed.card ≤ n := by
          omega
        simpa [weightedGreedyRun, hR] using
          ih (weightedGreedyAdvance G D w r st hR) hcard'
      · have hzero : st.unprocessed = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hR
        simp [weightedGreedyRun, hzero]

/-- Start with all vertices unprocessed and no matching edge. -/
def weightedGreedyInitial {V : Type*} [Fintype V] : WeightedGreedyState V where
  unprocessed := Finset.univ
  matching := ⊥
  unmatched := ∅
  history := []

/-- A complete finite run of the greedy procedure. -/
noncomputable def weightedGreedyFullRun
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ) :
    WeightedGreedyState V :=
  weightedGreedyRun G D w r (Fintype.card V) weightedGreedyInitial

theorem weightedGreedyFullRun_unprocessed_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ) :
    (weightedGreedyFullRun G D w r).unprocessed = ∅ := by
  apply weightedGreedyRun_unprocessed_empty
  simp [weightedGreedyInitial]

theorem singletonEdgeGraph_adj_iff
    {V : Type*} (u v a b : V) :
    (singletonEdgeGraph u v).Adj a b ↔
      ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) ∧ a ≠ b := by
  simp [singletonEdgeGraph, SimpleGraph.fromEdgeSet_adj,
    Prod.mk.injEq]

theorem singletonEdgeGraph_le_of_adj
    {V : Type*} (G : SimpleGraph V) {u v : V}
    (huv : G.Adj u v) :
    singletonEdgeGraph u v ≤ G := by
  intro a b hab
  obtain ⟨h, _⟩ := (singletonEdgeGraph_adj_iff u v a b).mp hab
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact huv
  · exact huv.symm

theorem weightedGreedyAdvanceWithChoice_matching_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G D : SimpleGraph V} {w : V → ℝ} {r : ℕ}
    (st : WeightedGreedyState V)
    (c : GreedyChoice G D st.matching st.unprocessed w r)
    (hP : st.matching ≤ G) :
    (weightedGreedyAdvanceWithChoice st c).matching ≤ G := by
  cases h : c.partner with
  | none =>
      simpa [weightedGreedyAdvanceWithChoice, h] using hP
  | some u =>
      have hadj : G.Adj c.selected u :=
        (c.partner_mem_unprocessed h).2.2.1
      simpa [weightedGreedyAdvanceWithChoice, h] using
        (sup_le hP (singletonEdgeGraph_le_of_adj G hadj))

theorem weightedGreedyAdvance_matching_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ)
    (st : WeightedGreedyState V) (hR : st.unprocessed.Nonempty)
    (hP : st.matching ≤ G) :
    (weightedGreedyAdvance G D w r st hR).matching ≤ G :=
  weightedGreedyAdvanceWithChoice_matching_le st _ hP

theorem weightedGreedyRun_matching_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r n : ℕ)
    (st : WeightedGreedyState V)
    (hP : st.matching ≤ G) :
    (weightedGreedyRun G D w r n st).matching ≤ G := by
  induction n generalizing st with
  | zero => exact hP
  | succ n ih =>
      by_cases hR : st.unprocessed.Nonempty
      · simpa [weightedGreedyRun, hR] using
          ih (weightedGreedyAdvance G D w r st hR)
            (weightedGreedyAdvance_matching_le G D w r st hR hP)
      · simpa [weightedGreedyRun, hR] using hP

theorem weightedGreedyFullRun_matching_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ) :
    (weightedGreedyFullRun G D w r).matching ≤ G := by
  apply weightedGreedyRun_matching_le
  simp [weightedGreedyInitial]

/-- The graph made from one proper pair has at most one neighbor per vertex. -/
theorem singletonEdgeGraph_adj_unique
    {V : Type*} {u v x y z : V} (huv : u ≠ v)
    (hxy : (singletonEdgeGraph u v).Adj x y)
    (hxz : (singletonEdgeGraph u v).Adj x z) :
    y = z := by
  obtain ⟨hxy, _⟩ := (singletonEdgeGraph_adj_iff u v x y).mp hxy
  obtain ⟨hxz, _⟩ := (singletonEdgeGraph_adj_iff u v x z).mp hxz
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases hxz with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · rfl
  · exact (huv h).elim
  · exact (huv h.symm).elim
  · rfl

/-- State invariant: unprocessed vertices have no matching edge yet, and
the current matching graph has degree at most one. -/
def WeightedGreedyState.IsMatchingState
    {V : Type*} (st : WeightedGreedyState V) : Prop :=
  (∀ x ∈ st.unprocessed, ∀ y, ¬st.matching.Adj x y) ∧
    ∀ x y z, st.matching.Adj x y → st.matching.Adj x z → y = z

theorem weightedGreedyInitial_isMatchingState
    {V : Type*} [Fintype V] :
    (weightedGreedyInitial (V := V)).IsMatchingState := by
  constructor
  · intro x hx y h
    exact h
  · intro x y z h
    exact False.elim h

theorem weightedGreedyAdvanceWithChoice_isMatchingState
    {V : Type*} [Fintype V] [DecidableEq V]
    {G D : SimpleGraph V} {w : V → ℝ} {r : ℕ}
    (st : WeightedGreedyState V)
    (c : GreedyChoice G D st.matching st.unprocessed w r)
    (hstate : st.IsMatchingState) :
    (weightedGreedyAdvanceWithChoice st c).IsMatchingState := by
  rcases hstate with ⟨hisolated, hunique⟩
  cases h : c.partner with
  | none =>
      simp only [WeightedGreedyState.IsMatchingState, weightedGreedyAdvanceWithChoice, h]
      constructor
      · intro x hx y
        exact hisolated x (Finset.mem_of_mem_erase hx) y
      · exact hunique
  | some u =>
      have huR : u ∈ st.unprocessed := (c.partner_mem_unprocessed h).1
      have hne : c.selected ≠ u := (c.partner_mem_unprocessed h).2.1.symm
      have hvIsolated := hisolated c.selected c.selected_mem
      have huIsolated := hisolated u huR
      simp only [WeightedGreedyState.IsMatchingState, weightedGreedyAdvanceWithChoice, h]
      constructor
      · intro x hx y hxy
        have hxR : x ∈ st.unprocessed :=
          Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
        have hxneU : x ≠ u := (Finset.mem_erase.mp hx).1
        have hxneV : x ≠ c.selected :=
          (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
        rcases (SimpleGraph.sup_adj _ _ x y).mp hxy with hP | hE
        · exact hisolated x hxR y hP
        · obtain ⟨hE, _⟩ :=
            (singletonEdgeGraph_adj_iff c.selected u x y).mp hE
          rcases hE with ⟨rfl, _⟩ | ⟨rfl, _⟩
          · exact hxneV rfl
          · exact hxneU rfl
      · intro x y z hxy hxz
        rcases (SimpleGraph.sup_adj _ _ x y).mp hxy with hPxy | hExy
        · rcases (SimpleGraph.sup_adj _ _ x z).mp hxz with hPxz | hExz
          · exact hunique x y z hPxy hPxz
          · obtain ⟨hE, _⟩ :=
              (singletonEdgeGraph_adj_iff c.selected u x z).mp hExz
            rcases hE with ⟨rfl, _⟩ | ⟨rfl, _⟩
            · exact False.elim (hvIsolated y hPxy)
            · exact False.elim (huIsolated y hPxy)
        · rcases (SimpleGraph.sup_adj _ _ x z).mp hxz with hPxz | hExz
          · obtain ⟨hE, _⟩ :=
              (singletonEdgeGraph_adj_iff c.selected u x y).mp hExy
            rcases hE with ⟨rfl, _⟩ | ⟨rfl, _⟩
            · exact False.elim (hvIsolated z hPxz)
            · exact False.elim (huIsolated z hPxz)
          · exact singletonEdgeGraph_adj_unique hne hExy hExz
theorem weightedGreedyAdvance_isMatchingState
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ)
    (st : WeightedGreedyState V) (hR : st.unprocessed.Nonempty)
    (hstate : st.IsMatchingState) :
    (weightedGreedyAdvance G D w r st hR).IsMatchingState :=
  weightedGreedyAdvanceWithChoice_isMatchingState st _ hstate

theorem weightedGreedyRun_isMatchingState
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r n : ℕ)
    (st : WeightedGreedyState V)
    (hstate : st.IsMatchingState) :
    (weightedGreedyRun G D w r n st).IsMatchingState := by
  induction n generalizing st with
  | zero => exact hstate
  | succ n ih =>
      by_cases hR : st.unprocessed.Nonempty
      · simpa [weightedGreedyRun, hR] using
          ih (weightedGreedyAdvance G D w r st hR)
            (weightedGreedyAdvance_isMatchingState G D w r st hR hstate)
      · simpa [weightedGreedyRun, hR] using hstate

theorem weightedGreedyFullRun_isMatchingState
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ) :
    (weightedGreedyFullRun G D w r).IsMatchingState :=
  weightedGreedyRun_isMatchingState G D w r (Fintype.card V)
    weightedGreedyInitial weightedGreedyInitial_isMatchingState
/-- Orient an edge by its canonical `Sym2` representative. -/
noncomputable def matchingEdgeEndpoint {V : Type*} {P : SimpleGraph V}
    (e : P.edgeSet) (b : Bool) : V :=
  if b then e.val.out.2 else e.val.out.1

theorem matchingEdgeEndpoint_adj
    {V : Type*} (P : SimpleGraph V) (e : P.edgeSet) :
    P.Adj (matchingEdgeEndpoint e false) (matchingEdgeEndpoint e true) := by
  change P.Adj e.val.out.1 e.val.out.2
  apply (P.mem_edgeSet).mp
  simpa only [Sym2.mk, e.val.out_eq] using e.property

theorem matchingEdgeEndpoint_pair
    {V : Type*} {P : SimpleGraph V}
    (e : P.edgeSet) (b : Bool) :
    e.val = s(matchingEdgeEndpoint e b, matchingEdgeEndpoint e (!b)) := by
  cases b with
  | false => exact e.val.out_eq.symm
  | true => exact e.val.out_eq.symm.trans Sym2.eq_swap

/-- A graph with at most one neighbor at each vertex canonically yields an
indexed matching, with its edge set as index type. -/
noncomputable def indexedMatchingOfUnique
    {V : Type*} (G P : SimpleGraph V) (hPG : P ≤ G)
    (hunique : ∀ x y z, P.Adj x y → P.Adj x z → y = z) :
    IndexedMatching G P.edgeSet where
  endpoint := matchingEdgeEndpoint
  adjacent e := hPG (matchingEdgeEndpoint_adj P e)
  injective := by
    rintro ⟨e, b⟩ ⟨f, c⟩ h
    have he := matchingEdgeEndpoint_adj P e
    have hf := matchingEdgeEndpoint_adj P f
    have heb : P.Adj (matchingEdgeEndpoint e b)
        (matchingEdgeEndpoint e (!b)) := by
      cases b <;> first | exact he | exact he.symm
    have hfc : P.Adj (matchingEdgeEndpoint f c)
        (matchingEdgeEndpoint f (!c)) := by
      cases c <;> first | exact hf | exact hf.symm
    change matchingEdgeEndpoint e b = matchingEdgeEndpoint f c at h
    have hother : matchingEdgeEndpoint e (!b) =
        matchingEdgeEndpoint f (!c) := by
      rw [h] at heb
      exact hunique _ _ _ heb hfc
    have hef : e = f := by
      apply Subtype.ext
      calc
        e.val = s(matchingEdgeEndpoint e b, matchingEdgeEndpoint e (!b)) :=
          matchingEdgeEndpoint_pair e b
        _ = s(matchingEdgeEndpoint f c, matchingEdgeEndpoint f (!c)) :=
          congrArg₂ (fun x y => s(x, y)) h hother
        _ = f.val := (matchingEdgeEndpoint_pair f c).symm
    subst f
    have hbc : b = c := by
      cases b <;> cases c <;> simp_all [matchingEdgeEndpoint]
    exact Prod.ext rfl hbc
theorem indexedMatchingOfUnique_edgeGraph_eq
    {V : Type*} (G P : SimpleGraph V) (hPG : P ≤ G)
    (hunique : ∀ x y z, P.Adj x y → P.Adj x z → y = z) :
    (indexedMatchingOfUnique G P hPG hunique).edgeGraph = P := by
  ext x y
  constructor
  · rintro ⟨e, hxy | hxy⟩
    · rcases hxy with ⟨rfl, rfl⟩
      exact matchingEdgeEndpoint_adj P e
    · rcases hxy with ⟨rfl, rfl⟩
      exact (matchingEdgeEndpoint_adj P e).symm
  · intro hxy
    let e : P.edgeSet := ⟨s(x, y), P.mem_edgeSet.mpr hxy⟩
    have heq : s(e.val.out.1, e.val.out.2) = s(x, y) := by
      exact e.val.out_eq
    rcases Sym2.eq_iff.mp heq with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact ⟨e, Or.inl ⟨hx.symm, hy.symm⟩⟩
    · exact ⟨e, Or.inr ⟨hy.symm, hx.symm⟩⟩

/-- The complete greedy run determines a genuine indexed matching of G. -/
noncomputable def weightedGreedyFullMatching
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ) :
    IndexedMatching G (weightedGreedyFullRun G D w r).matching.edgeSet :=
  indexedMatchingOfUnique G (weightedGreedyFullRun G D w r).matching
    (weightedGreedyFullRun_matching_le G D w r)
    (weightedGreedyFullRun_isMatchingState G D w r).2

theorem weightedGreedyFullMatching_edgeGraph_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ) :
    (weightedGreedyFullMatching G D w r).edgeGraph =
      (weightedGreedyFullRun G D w r).matching :=
  indexedMatchingOfUnique_edgeGraph_eq G _
    (weightedGreedyFullRun_matching_le G D w r)
    (weightedGreedyFullRun_isMatchingState G D w r).2
/-- A chosen eligible edge cannot already belong to D when r ≥ 1. -/
theorem GreedyChoice.partner_not_D_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    {G D P : SimpleGraph V} {R : Finset V}
    {w : V → ℝ} {r : ℕ}
    (c : GreedyChoice G D P R w r) (hr : 1 ≤ r)
    {u : V} (hpartner : c.partner = some u) :
    ¬D.Adj c.selected u := by
  intro hadj
  have hfar := (c.partner_mem_unprocessed hpartner).2.2.2
  have hdist : (D ⊔ P).edist c.selected u = 1 :=
    SimpleGraph.edist_eq_one_iff_adj.mpr (Or.inl hadj)
  have hlt : (r : ℕ∞) < 1 := by simpa [hdist] using hfar
  have hr' : (1 : ℕ∞) ≤ (r : ℕ∞) := by exact_mod_cast hr
  exact (not_lt_of_ge hr') hlt

theorem weightedGreedyAdvanceWithChoice_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    {G D : SimpleGraph V} {w : V → ℝ} {r : ℕ}
    (st : WeightedGreedyState V)
    (c : GreedyChoice G D st.matching st.unprocessed w r)
    (hr : 1 ≤ r)
    (hdisj : ∀ x y, D.Adj x y → ¬ st.matching.Adj x y) :
    ∀ x y, D.Adj x y →
      ¬(weightedGreedyAdvanceWithChoice st c).matching.Adj x y := by
  cases h : c.partner with
  | none =>
      simpa [weightedGreedyAdvanceWithChoice, h] using hdisj
  | some u =>
      intro x y hD hP
      have hnew : ¬D.Adj c.selected u := c.partner_not_D_adj hr h
      have hnew' : ¬D.Adj u c.selected := by
        intro hD'
        exact hnew hD'.symm
      simp only [weightedGreedyAdvanceWithChoice, h] at hP
      rcases (SimpleGraph.sup_adj _ _ x y).mp hP with hOld | hEdge
      · exact hdisj x y hD hOld
      · obtain ⟨hxy, _⟩ :=
          (singletonEdgeGraph_adj_iff c.selected u x y).mp hEdge
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hnew hD
        · exact hnew' hD

theorem weightedGreedyRun_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r n : ℕ)
    (hr : 1 ≤ r) (st : WeightedGreedyState V)
    (hdisj : ∀ x y, D.Adj x y → ¬ st.matching.Adj x y) :
    ∀ x y, D.Adj x y →
      ¬(weightedGreedyRun G D w r n st).matching.Adj x y := by
  induction n generalizing st with
  | zero => exact hdisj
  | succ n ih =>
      by_cases hR : st.unprocessed.Nonempty
      · simpa [weightedGreedyRun, hR] using
          ih (weightedGreedyAdvance G D w r st hR)
            (weightedGreedyAdvanceWithChoice_disjoint st _ hr hdisj)
      · simpa [weightedGreedyRun, hR] using hdisj

theorem weightedGreedyFullMatching_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ)
    (hr : 1 ≤ r) :
    ∀ x y, D.Adj x y →
      ¬(weightedGreedyFullMatching G D w r).edgeGraph.Adj x y := by
  rw [weightedGreedyFullMatching_edgeGraph_eq]
  exact weightedGreedyRun_disjoint G D w r (Fintype.card V) hr
    weightedGreedyInitial (by simp [weightedGreedyInitial])
/-- Every vertex is still available, was set aside, or has a matching edge;
set-aside vertices remain isolated from the matching. -/
def WeightedGreedyState.IsCoverageState
    {V : Type*} (st : WeightedGreedyState V) : Prop :=
  (∀ x, x ∈ st.unprocessed ∨ x ∈ st.unmatched ∨
      ∃ y, st.matching.Adj x y) ∧
  (∀ x ∈ st.unmatched, ∀ y, ¬st.matching.Adj x y) ∧
  Disjoint st.unprocessed st.unmatched

theorem weightedGreedyInitial_isCoverageState
    {V : Type*} [Fintype V] :
    (weightedGreedyInitial (V := V)).IsCoverageState := by
  classical
  constructor
  · intro x
    exact Or.inl (Finset.mem_univ x)
  constructor
  · intro x hx
    simp [weightedGreedyInitial] at hx
  · simp [weightedGreedyInitial]

theorem weightedGreedyAdvanceWithChoice_isCoverageState
    {V : Type*} [Fintype V] [DecidableEq V]
    {G D : SimpleGraph V} {w : V → ℝ} {r : ℕ}
    (st : WeightedGreedyState V)
    (c : GreedyChoice G D st.matching st.unprocessed w r)
    (hmatch : st.IsMatchingState)
    (hcover : st.IsCoverageState) :
    (weightedGreedyAdvanceWithChoice st c).IsCoverageState := by
  rcases hmatch with ⟨hisolated, _⟩
  rcases hcover with ⟨hcover, hunmatched, hdisj⟩
  cases h : c.partner with
  | none =>
      simp only [WeightedGreedyState.IsCoverageState,
        weightedGreedyAdvanceWithChoice, h]
      constructor
      · intro x
        rcases hcover x with hxR | hxX | ⟨y, hxy⟩
        · by_cases hxv : x = c.selected
          · subst x
            exact Or.inr (Or.inl (Finset.mem_insert_self _ _))
          · exact Or.inl (Finset.mem_erase.mpr ⟨hxv, hxR⟩)
        · exact Or.inr (Or.inl (Finset.mem_insert_of_mem hxX))
        · exact Or.inr (Or.inr ⟨y, hxy⟩)
      constructor
      · intro x hx y
        rcases Finset.mem_insert.mp hx with rfl | hxX
        · exact hisolated c.selected c.selected_mem y
        · exact hunmatched x hxX y
      · apply Finset.disjoint_left.mpr
        intro x hxR hxX
        rcases Finset.mem_insert.mp hxX with rfl | hxX
        · exact (Finset.mem_erase.mp hxR).1 rfl
        · exact Finset.disjoint_left.mp hdisj
            (Finset.mem_of_mem_erase hxR) hxX
  | some u =>
      have huR : u ∈ st.unprocessed := (c.partner_mem_unprocessed h).1
      have hne : c.selected ≠ u := (c.partner_mem_unprocessed h).2.1.symm
      have hEdge : (singletonEdgeGraph c.selected u).Adj c.selected u :=
        (singletonEdgeGraph_adj_iff c.selected u c.selected u).mpr
          ⟨Or.inl ⟨rfl, rfl⟩, hne⟩
      have hvNotX : c.selected ∉ st.unmatched := by
        intro hx
        exact Finset.disjoint_left.mp hdisj c.selected_mem hx
      have huNotX : u ∉ st.unmatched := by
        intro hx
        exact Finset.disjoint_left.mp hdisj huR hx
      simp only [WeightedGreedyState.IsCoverageState,
        weightedGreedyAdvanceWithChoice, h]
      constructor
      · intro x
        rcases hcover x with hxR | hxX | ⟨y, hxy⟩
        · by_cases hxv : x = c.selected
          · subst x
            exact Or.inr (Or.inr ⟨u, Or.inr hEdge⟩)
          · by_cases hxu : x = u
            · subst x
              exact Or.inr (Or.inr ⟨c.selected, Or.inr hEdge.symm⟩)
            · exact Or.inl (Finset.mem_erase.mpr
                ⟨hxu, Finset.mem_erase.mpr ⟨hxv, hxR⟩⟩)
        · exact Or.inr (Or.inl hxX)
        · exact Or.inr (Or.inr ⟨y, Or.inl hxy⟩)
      constructor
      · intro x hxX y hxy
        rcases (SimpleGraph.sup_adj _ _ x y).mp hxy with hOld | hNew
        · exact hunmatched x hxX y hOld
        · obtain ⟨hxy, _⟩ :=
            (singletonEdgeGraph_adj_iff c.selected u x y).mp hNew
          rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩
          · exact hvNotX hxX
          · exact huNotX hxX
      · apply Finset.disjoint_left.mpr
        intro x hxR hxX
        exact Finset.disjoint_left.mp hdisj
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hxR)) hxX
theorem weightedGreedyRun_isCoverageState
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r n : ℕ)
    (st : WeightedGreedyState V)
    (hmatch : st.IsMatchingState)
    (hcover : st.IsCoverageState) :
    (weightedGreedyRun G D w r n st).IsCoverageState := by
  induction n generalizing st with
  | zero => exact hcover
  | succ n ih =>
      by_cases hR : st.unprocessed.Nonempty
      · simpa [weightedGreedyRun, hR] using
          ih (weightedGreedyAdvance G D w r st hR)
            (weightedGreedyAdvance_isMatchingState G D w r st hR hmatch)
            (weightedGreedyAdvanceWithChoice_isCoverageState st _ hmatch hcover)
      · simpa [weightedGreedyRun, hR] using hcover

theorem weightedGreedyFullRun_isCoverageState
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ) :
    (weightedGreedyFullRun G D w r).IsCoverageState :=
  weightedGreedyRun_isCoverageState G D w r (Fintype.card V)
    weightedGreedyInitial weightedGreedyInitial_isMatchingState
    weightedGreedyInitial_isCoverageState

theorem weightedGreedyFullRun_mem_unmatched_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ) (x : V) :
    x ∈ (weightedGreedyFullRun G D w r).unmatched ↔
      ¬∃ y, (weightedGreedyFullRun G D w r).matching.Adj x y := by
  have hcover := weightedGreedyFullRun_isCoverageState G D w r
  constructor
  · intro hx ⟨y, hxy⟩
    exact hcover.2.1 x hx y hxy
  · intro hnone
    rcases hcover.1 x with hxR | hxX | ⟨y, hxy⟩
    · rw [weightedGreedyFullRun_unprocessed_empty] at hxR
      simp at hxR
    · exact hxX
    · exact (hnone ⟨y, hxy⟩).elim
/-- Reverse any chosen pair orientations without changing the indexed edges. -/
def IndexedMatching.flipBy
    {V I : Type*} {G : SimpleGraph V}
    (M : IndexedMatching G I) (flip : I → Bool) : IndexedMatching G I where
  endpoint i b := M.endpoint i (if flip i then !b else b)
  adjacent i := by
    by_cases hf : flip i
    · simpa [hf] using (M.adjacent i).symm
    · simpa [hf] using M.adjacent i
  injective := by
    rintro ⟨i, b⟩ ⟨j, c⟩ h
    have hp : (i, if flip i then !b else b) =
        (j, if flip j then !c else c) := M.injective h
    have hij : i = j := congrArg Prod.fst hp
    subst j
    have hbc : (if flip i then !b else b) =
        (if flip i then !c else c) := congrArg Prod.snd hp
    have hbc' : b = c := by
      by_cases hf : flip i <;> simp [hf] at hbc ⊢
      · cases b <;> cases c <;> simp_all
      · exact hbc
    exact Prod.ext rfl hbc'

theorem IndexedMatching.flipBy_edgeGraph_eq
    {V I : Type*} {G : SimpleGraph V}
    (M : IndexedMatching G I) (flip : I → Bool) :
    (M.flipBy flip).edgeGraph = M.edgeGraph := by
  ext x y
  have hor (i : I) :
      ((x = (M.flipBy flip).endpoint i false ∧
          y = (M.flipBy flip).endpoint i true) ∨
        (x = (M.flipBy flip).endpoint i true ∧
          y = (M.flipBy flip).endpoint i false)) ↔
      ((x = M.endpoint i false ∧ y = M.endpoint i true) ∨
        (x = M.endpoint i true ∧ y = M.endpoint i false)) := by
    by_cases hf : flip i
    · simp [IndexedMatching.flipBy, hf, or_comm]
    · simp [IndexedMatching.flipBy, hf]
  constructor
  · rintro ⟨i, hxy⟩
    exact ⟨i, (hor i).mp hxy⟩
  · rintro ⟨i, hxy⟩
    exact ⟨i, (hor i).mpr hxy⟩
/-- Orient each pair with the heavier endpoint first. -/
noncomputable def IndexedMatching.orientByWeight
    {V I : Type*} {G : SimpleGraph V}
    (M : IndexedMatching G I) (w : V → ℝ) : IndexedMatching G I :=
  M.flipBy fun i => decide (w (M.endpoint i false) < w (M.endpoint i true))

theorem IndexedMatching.orientByWeight_order
    {V I : Type*} {G : SimpleGraph V}
    (M : IndexedMatching G I) (w : V → ℝ) (i : I) :
    w ((M.orientByWeight w).endpoint i true) ≤
      w ((M.orientByWeight w).endpoint i false) := by
  by_cases h : w (M.endpoint i false) < w (M.endpoint i true)
  · simpa [IndexedMatching.orientByWeight, IndexedMatching.flipBy, h] using
      (le_of_lt h)
  · simpa [IndexedMatching.orientByWeight, IndexedMatching.flipBy, h] using
      (le_of_not_gt h)

theorem IndexedMatching.orientByWeight_edgeGraph_eq
    {V I : Type*} {G : SimpleGraph V}
    (M : IndexedMatching G I) (w : V → ℝ) :
    (M.orientByWeight w).edgeGraph = M.edgeGraph :=
  M.flipBy_edgeGraph_eq _
/-- The greedy matching with every pair oriented by decreasing weight. -/
noncomputable def weightedGreedyFullMatchingSorted
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ) :
    IndexedMatching G (weightedGreedyFullRun G D w r).matching.edgeSet :=
  (weightedGreedyFullMatching G D w r).orientByWeight w

theorem weightedGreedyFullMatchingSorted_order
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ)
    (i : (weightedGreedyFullRun G D w r).matching.edgeSet) :
    w ((weightedGreedyFullMatchingSorted G D w r).endpoint i true) ≤
      w ((weightedGreedyFullMatchingSorted G D w r).endpoint i false) :=
  (weightedGreedyFullMatching G D w r).orientByWeight_order w i

theorem weightedGreedyFullMatchingSorted_edgeGraph_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ) :
    (weightedGreedyFullMatchingSorted G D w r).edgeGraph =
      (weightedGreedyFullRun G D w r).matching := by
  rw [weightedGreedyFullMatchingSorted,
    IndexedMatching.orientByWeight_edgeGraph_eq,
    weightedGreedyFullMatching_edgeGraph_eq]
/-- Vertices in the order they leave the unprocessed set. Each pair is
listed with its selected endpoint first. -/
def WeightedGreedyState.processedVertices
    {V : Type*} (st : WeightedGreedyState V) : List V :=
  st.history.flatMap fun h => h.1 :: h.2.1.toList

/-- At every stage, the processed history and unprocessed finset partition
the ambient vertex type. -/
def WeightedGreedyState.IsProcessPartition
    {V : Type*} (st : WeightedGreedyState V) : Prop :=
  ∀ x, x ∈ st.unprocessed ↔ x ∉ st.processedVertices

theorem weightedGreedyInitial_isProcessPartition
    {V : Type*} [Fintype V] :
    (weightedGreedyInitial (V := V)).IsProcessPartition := by
  intro x
  simp [
    WeightedGreedyState.processedVertices, weightedGreedyInitial]

theorem weightedGreedyAdvanceWithChoice_isProcessPartition
    {V : Type*} [Fintype V] [DecidableEq V]
    {G D : SimpleGraph V} {w : V → ℝ} {r : ℕ}
    (st : WeightedGreedyState V)
    (c : GreedyChoice G D st.matching st.unprocessed w r)
    (hpartition : st.IsProcessPartition) :
    (weightedGreedyAdvanceWithChoice st c).IsProcessPartition := by
  intro x
  cases h : c.partner with
  | none =>
      have hproc : (weightedGreedyAdvanceWithChoice st c).processedVertices =
          st.processedVertices ++ [c.selected] := by
        simp [WeightedGreedyState.processedVertices,
          weightedGreedyAdvanceWithChoice, h]
      rw [hproc]
      simp only [weightedGreedyAdvanceWithChoice, h, Finset.mem_erase,
        List.mem_append, List.mem_singleton, not_or, hpartition x]
      tauto
  | some u =>
      have hproc : (weightedGreedyAdvanceWithChoice st c).processedVertices =
          st.processedVertices ++ [c.selected, u] := by
        simp [WeightedGreedyState.processedVertices,
          weightedGreedyAdvanceWithChoice, h]
      rw [hproc]
      simp only [weightedGreedyAdvanceWithChoice, h, Finset.mem_erase,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        not_or, hpartition x]
      tauto
theorem weightedGreedyRun_isProcessPartition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r n : ℕ)
    (st : WeightedGreedyState V)
    (hpartition : st.IsProcessPartition) :
    (weightedGreedyRun G D w r n st).IsProcessPartition := by
  induction n generalizing st with
  | zero => exact hpartition
  | succ n ih =>
      by_cases hR : st.unprocessed.Nonempty
      · simpa [weightedGreedyRun, hR] using
          ih (weightedGreedyAdvance G D w r st hR)
            (weightedGreedyAdvanceWithChoice_isProcessPartition st _ hpartition)
      · simpa [weightedGreedyRun, hR] using hpartition

theorem weightedGreedyFullRun_isProcessPartition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ) :
    (weightedGreedyFullRun G D w r).IsProcessPartition :=
  weightedGreedyRun_isProcessPartition G D w r (Fintype.card V)
    weightedGreedyInitial weightedGreedyInitial_isProcessPartition

theorem weightedGreedyFullRun_mem_processedVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ) (x : V) :
    x ∈ (weightedGreedyFullRun G D w r).processedVertices := by
  have hpart := weightedGreedyFullRun_isProcessPartition G D w r x
  rw [weightedGreedyFullRun_unprocessed_empty] at hpart
  simpa using hpart.mpr

/-- A globally injective processing time, including vertices consumed as
partners, from their positions in the completed history. -/
noncomputable def weightedGreedyFullRun_time
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ) (x : V) : ℕ :=
  (weightedGreedyFullRun G D w r).processedVertices.idxOf x

theorem weightedGreedyFullRun_time_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ) :
    Function.Injective (weightedGreedyFullRun_time G D w r) := by
  intro x y h
  exact (List.idxOf_inj
    (weightedGreedyFullRun_mem_processedVertices G D w r x)).mp h
theorem weightedGreedyAdvanceWithChoice_processed_prefix
    {V : Type*} [Fintype V] [DecidableEq V]
    {G D : SimpleGraph V} {w : V → ℝ} {r : ℕ}
    (st : WeightedGreedyState V)
    (c : GreedyChoice G D st.matching st.unprocessed w r) :
    st.processedVertices <+:
      (weightedGreedyAdvanceWithChoice st c).processedVertices := by
  cases h : c.partner with
  | none =>
      have hproc : (weightedGreedyAdvanceWithChoice st c).processedVertices =
          st.processedVertices ++ [c.selected] := by
        simp [WeightedGreedyState.processedVertices,
          weightedGreedyAdvanceWithChoice, h]
      rw [hproc]
      exact List.prefix_append _ _
  | some u =>
      have hproc : (weightedGreedyAdvanceWithChoice st c).processedVertices =
          st.processedVertices ++ [c.selected, u] := by
        simp [WeightedGreedyState.processedVertices,
          weightedGreedyAdvanceWithChoice, h]
      rw [hproc]
      exact List.prefix_append _ _

theorem weightedGreedyRun_processed_prefix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r n : ℕ)
    (st : WeightedGreedyState V) :
    st.processedVertices <+:
      (weightedGreedyRun G D w r n st).processedVertices := by
  induction n generalizing st with
  | zero => exact List.prefix_refl _
  | succ n ih =>
      by_cases hR : st.unprocessed.Nonempty
      · have hstep : st.processedVertices <+:
          (weightedGreedyAdvance G D w r st hR).processedVertices :=
          weightedGreedyAdvanceWithChoice_processed_prefix st _
        simpa [weightedGreedyRun, hR] using
          hstep.trans (ih (weightedGreedyAdvance G D w r st hR))
      · simp [weightedGreedyRun, hR]
/-- In any later extension of a greedy history, the chosen vertex precedes
every vertex still unprocessed after its step. -/
theorem weightedGreedyAdvanceWithChoice_selected_time_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G D : SimpleGraph V} {w : V → ℝ} {r : ℕ}
    (st : WeightedGreedyState V)
    (c : GreedyChoice G D st.matching st.unprocessed w r)
    (hpartition : st.IsProcessPartition)
    (final : WeightedGreedyState V)
    (hprefix : (weightedGreedyAdvanceWithChoice st c).processedVertices <+:
      final.processedVertices)
    (y : V) (hyR : y ∈ (weightedGreedyAdvanceWithChoice st c).unprocessed) :
    final.processedVertices.idxOf c.selected <
      final.processedVertices.idxOf y := by
  let next := weightedGreedyAdvanceWithChoice st c
  have hpartNext : next.IsProcessPartition :=
    weightedGreedyAdvanceWithChoice_isProcessPartition st c hpartition
  have hyNot : y ∉ next.processedVertices := (hpartNext y).mp hyR
  have hvMem : c.selected ∈ next.processedVertices := by
    cases h : c.partner with
    | none =>
        simp [next, WeightedGreedyState.processedVertices,
          weightedGreedyAdvanceWithChoice, h]
    | some u =>
        simp [next, WeightedGreedyState.processedVertices,
          weightedGreedyAdvanceWithChoice, h]
  have hvlt : final.processedVertices.idxOf c.selected <
      next.processedVertices.length := by
    rw [← hprefix.idxOf_eq_of_mem hvMem]
    exact List.idxOf_lt_length_of_mem hvMem
  have hyge : next.processedVertices.length ≤
      final.processedVertices.idxOf y := by
    by_contra hnot
    have hlt : final.processedVertices.idxOf y < next.processedVertices.length := by
      omega
    exact hyNot ((hprefix.mem_iff_idxOf_lt_length y).mpr hlt)
  exact hvlt.trans_le hyge
/-- Matching edges are only added during a greedy step. -/
theorem weightedGreedyAdvanceWithChoice_matching_mono
    {V : Type*} [Fintype V] [DecidableEq V]
    {G D : SimpleGraph V} {w : V → ℝ} {r : ℕ}
    (st : WeightedGreedyState V)
    (c : GreedyChoice G D st.matching st.unprocessed w r) :
    st.matching ≤ (weightedGreedyAdvanceWithChoice st c).matching := by
  cases h : c.partner with
  | none => simp [weightedGreedyAdvanceWithChoice, h]
  | some u =>
      simp [weightedGreedyAdvanceWithChoice, h]

theorem weightedGreedyRun_matching_mono
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r n : ℕ)
    (st : WeightedGreedyState V) :
    st.matching ≤ (weightedGreedyRun G D w r n st).matching := by
  induction n generalizing st with
  | zero => exact le_rfl
  | succ n ih =>
      by_cases hR : st.unprocessed.Nonempty
      · have hstep : st.matching ≤
          (weightedGreedyAdvance G D w r st hR).matching :=
          weightedGreedyAdvanceWithChoice_matching_mono st _
        simpa [weightedGreedyRun, hR] using
          hstep.trans (ih (weightedGreedyAdvance G D w r st hR))
      · simp [weightedGreedyRun, hR]

/-- A vertex occurring after the chosen vertex in a final extension was
still unprocessed when that choice was made. -/
theorem GreedyChoice.later_unprocessed_of_prefix
    {V : Type*} [Fintype V] [DecidableEq V]
    {G D : SimpleGraph V} {w : V → ℝ} {r : ℕ}
    {st : WeightedGreedyState V}
    (c : GreedyChoice G D st.matching st.unprocessed w r)
    (hpartition : st.IsProcessPartition)
    (final : WeightedGreedyState V)
    (hprefix : st.processedVertices <+: final.processedVertices)
    (y : V)
    (hlt : final.processedVertices.idxOf c.selected <
      final.processedVertices.idxOf y) :
    y ∈ st.unprocessed := by
  have hvNot : c.selected ∉ st.processedVertices :=
    (hpartition c.selected).mp c.selected_mem
  by_contra hyR
  have hyMem : y ∈ st.processedVertices := by
    by_contra hyNot
    exact hyR ((hpartition y).mpr hyNot)
  have hylt : final.processedVertices.idxOf y <
      st.processedVertices.length :=
    (hprefix.mem_iff_idxOf_lt_length y).mp hyMem
  have hvge : st.processedVertices.length ≤
      final.processedVertices.idxOf c.selected := by
    by_contra hnot
    have hvlt : final.processedVertices.idxOf c.selected <
        st.processedVertices.length := by omega
    exact hvNot ((hprefix.mem_iff_idxOf_lt_length c.selected).mpr hvlt)
  omega
/-- The local ineligibility rule remains valid as a distance bound in any
later matching graph. -/
theorem GreedyChoice.unmatched_neighbor_close_final
    {V : Type*} [Fintype V] [DecidableEq V]
    {G D : SimpleGraph V} {w : V → ℝ} {r : ℕ}
    {st : WeightedGreedyState V}
    (c : GreedyChoice G D st.matching st.unprocessed w r)
    (hpartner : c.partner = none)
    (hpartition : st.IsProcessPartition)
    (final : WeightedGreedyState V)
    (hprefix : st.processedVertices <+: final.processedVertices)
    (hgraph : st.matching ≤ final.matching)
    {y : V}
    (hlt : final.processedVertices.idxOf c.selected <
      final.processedVertices.idxOf y)
    (hadj : G.Adj c.selected y) :
    (D ⊔ final.matching).edist c.selected y ≤ (r : ℕ∞) := by
  have hyR := c.later_unprocessed_of_prefix hpartition final hprefix y hlt
  exact (edist_antitone (sup_le_sup le_rfl hgraph) c.selected y).trans
    (c.unmatched_neighbor_close hpartner hyR hadj)

/-- The maximum-weight partner rule also persists in every later matching
graph. -/
theorem GreedyChoice.heavier_neighbor_close_final
    {V : Type*} [Fintype V] [DecidableEq V]
    {G D : SimpleGraph V} {w : V → ℝ} {r : ℕ}
    {st : WeightedGreedyState V}
    (c : GreedyChoice G D st.matching st.unprocessed w r)
    {u : V} (hpartner : c.partner = some u)
    (hpartition : st.IsProcessPartition)
    (final : WeightedGreedyState V)
    (hprefix : st.processedVertices <+: final.processedVertices)
    (hgraph : st.matching ≤ final.matching)
    {y : V}
    (hlt : final.processedVertices.idxOf c.selected <
      final.processedVertices.idxOf y)
    (hadj : G.Adj c.selected y)
    (hweight : w u < w y) :
    (D ⊔ final.matching).edist c.selected y ≤ (r : ℕ∞) := by
  have hyR := c.later_unprocessed_of_prefix hpartition final hprefix y hlt
  exact (edist_antitone (sup_le_sup le_rfl hgraph) c.selected y).trans
    (c.heavier_neighbor_close hpartner hyR hadj hweight)
/-- Every newly set-aside vertex satisfies the unmatched-neighbor distance
rule in any final extension of the run. -/
theorem weightedGreedyRun_unmatched_close_final
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r n : ℕ)
    (st final : WeightedGreedyState V)
    (hpartition : st.IsProcessPartition)
    (hprefix : (weightedGreedyRun G D w r n st).processedVertices <+:
      final.processedVertices)
    (hgraph : (weightedGreedyRun G D w r n st).matching ≤ final.matching)
    {x : V}
    (hx : x ∈ (weightedGreedyRun G D w r n st).unmatched)
    (hxnew : x ∉ st.unmatched)
    {y : V}
    (hlt : final.processedVertices.idxOf x < final.processedVertices.idxOf y)
    (hadj : G.Adj x y) :
    (D ⊔ final.matching).edist x y ≤ (r : ℕ∞) := by
  induction n generalizing st with
  | zero =>
      exact (hxnew hx).elim
  | succ n ih =>
      by_cases hR : st.unprocessed.Nonempty
      · let c : GreedyChoice G D st.matching st.unprocessed w r :=
          Classical.choice
            (exists_greedyChoice G D st.matching st.unprocessed hR w r)
        let next := weightedGreedyAdvanceWithChoice st c
        have hrun : weightedGreedyRun G D w r (n + 1) st =
            weightedGreedyRun G D w r n next := by
          simp [weightedGreedyRun, hR, next, weightedGreedyAdvance, c]
        rw [hrun] at hx hprefix hgraph
        have hpartNext : next.IsProcessPartition :=
          weightedGreedyAdvanceWithChoice_isProcessPartition st c hpartition
        cases hp : c.partner with
        | none =>
            by_cases hxx : x = c.selected
            · subst x
              have hprefixSt : st.processedVertices <+: final.processedVertices :=
                (weightedGreedyAdvanceWithChoice_processed_prefix st c).trans
                  ((weightedGreedyRun_processed_prefix G D w r n next).trans hprefix)
              have hgraphSt : st.matching ≤ final.matching :=
                (weightedGreedyAdvanceWithChoice_matching_mono st c).trans
                  ((weightedGreedyRun_matching_mono G D w r n next).trans hgraph)
              exact c.unmatched_neighbor_close_final hp hpartition final
                hprefixSt hgraphSt hlt hadj
            · have hxnewNext : x ∉ next.unmatched := by
                simpa [next, weightedGreedyAdvanceWithChoice, hp, hxx] using hxnew
              exact ih next hpartNext hprefix hgraph hx hxnewNext
        | some u =>
            have hxnewNext : x ∉ next.unmatched := by
              simpa [next, weightedGreedyAdvanceWithChoice, hp] using hxnew
            exact ih next hpartNext hprefix hgraph hx hxnewNext
      · have hrun : weightedGreedyRun G D w r (n + 1) st = st := by
          simp [weightedGreedyRun, hR]
        rw [hrun] at hx
        exact (hxnew hx).elim

theorem weightedGreedyFullRun_unmatched_close
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ)
    {x y : V}
    (hx : x ∈ (weightedGreedyFullRun G D w r).unmatched)
    (hlt : weightedGreedyFullRun_time G D w r x <
      weightedGreedyFullRun_time G D w r y)
    (hadj : G.Adj x y) :
    (D ⊔ (weightedGreedyFullRun G D w r).matching).edist x y ≤
      (r : ℕ∞) := by
  apply weightedGreedyRun_unmatched_close_final G D w r (Fintype.card V)
    weightedGreedyInitial (weightedGreedyFullRun G D w r)
    weightedGreedyInitial_isProcessPartition
    (List.prefix_refl _) le_rfl hx
    (by simp [weightedGreedyInitial]) hlt hadj
/-- A matching edge newly inserted by the run has its strictly heavier
endpoint selected first; its later, heavier G-neighbors are close in any
final extension. -/
theorem weightedGreedyRun_strict_pair_close_final
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r n : ℕ)
    (st final : WeightedGreedyState V)
    (hpartition : st.IsProcessPartition)
    (hprefix : (weightedGreedyRun G D w r n st).processedVertices <+:
      final.processedVertices)
    (hgraph : (weightedGreedyRun G D w r n st).matching ≤ final.matching)
    {x u y : V}
    (hpair : (weightedGreedyRun G D w r n st).matching.Adj x u)
    (hold : ¬st.matching.Adj x u)
    (hstrict : w u < w x)
    (hlt : final.processedVertices.idxOf x < final.processedVertices.idxOf y)
    (hadj : G.Adj x y)
    (hweight : w u < w y) :
    (D ⊔ final.matching).edist x y ≤ (r : ℕ∞) := by
  induction n generalizing st with
  | zero =>
      exact (hold hpair).elim
  | succ n ih =>
      by_cases hR : st.unprocessed.Nonempty
      · let c : GreedyChoice G D st.matching st.unprocessed w r :=
          Classical.choice
            (exists_greedyChoice G D st.matching st.unprocessed hR w r)
        let next := weightedGreedyAdvanceWithChoice st c
        have hrun : weightedGreedyRun G D w r (n + 1) st =
            weightedGreedyRun G D w r n next := by
          simp [weightedGreedyRun, hR, next, weightedGreedyAdvance, c]
        rw [hrun] at hpair hprefix hgraph
        have hpartNext : next.IsProcessPartition :=
          weightedGreedyAdvanceWithChoice_isProcessPartition st c hpartition
        by_cases hnext : next.matching.Adj x u
        · cases hp : c.partner with
          | none =>
              have hOld : st.matching.Adj x u := by
                simpa [next, weightedGreedyAdvanceWithChoice, hp] using hnext
              exact (hold hOld).elim
          | some v =>
              have hNew : (singletonEdgeGraph c.selected v).Adj x u := by
                have hSup : (st.matching ⊔ singletonEdgeGraph c.selected v).Adj x u := by
                  simpa [next, weightedGreedyAdvanceWithChoice, hp] using hnext
                rcases (SimpleGraph.sup_adj _ _ x u).mp hSup with hOld | hNew
                · exact (hold hOld).elim
                · exact hNew
              obtain ⟨hxu, _⟩ :=
                (singletonEdgeGraph_adj_iff c.selected v x u).mp hNew
              rcases hxu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · have hprefixSt : st.processedVertices <+: final.processedVertices :=
                  (weightedGreedyAdvanceWithChoice_processed_prefix st c).trans
                    ((weightedGreedyRun_processed_prefix G D w r n next).trans hprefix)
                have hgraphSt : st.matching ≤ final.matching :=
                  (weightedGreedyAdvanceWithChoice_matching_mono st c).trans
                    ((weightedGreedyRun_matching_mono G D w r n next).trans hgraph)
                exact c.heavier_neighbor_close_final hp hpartition final
                  hprefixSt hgraphSt hlt hadj hweight
              · exact (not_lt_of_ge (c.selected_weight_ge_partner hp) hstrict).elim
        · exact ih next hpartNext hprefix hgraph hpair hnext
      · have hrun : weightedGreedyRun G D w r (n + 1) st = st := by
          simp [weightedGreedyRun, hR]
        rw [hrun] at hpair
        exact (hold hpair).elim

theorem weightedGreedyFullRun_strict_pair_close
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ)
    {x u y : V}
    (hpair : (weightedGreedyFullRun G D w r).matching.Adj x u)
    (hstrict : w u < w x)
    (hlt : weightedGreedyFullRun_time G D w r x <
      weightedGreedyFullRun_time G D w r y)
    (hadj : G.Adj x y)
    (hweight : w u < w y) :
    (D ⊔ (weightedGreedyFullRun G D w r).matching).edist x y ≤
      (r : ℕ∞) := by
  apply weightedGreedyRun_strict_pair_close_final G D w r (Fintype.card V)
    weightedGreedyInitial (weightedGreedyFullRun G D w r)
    weightedGreedyInitial_isProcessPartition
    (List.prefix_refl _) le_rfl hpair
    (by simp [weightedGreedyInitial]) hstrict hlt hadj hweight
private noncomputable instance finiteGreedyEdgeSet
    {V : Type*} [Fintype V] (P : SimpleGraph V) : Fintype P.edgeSet :=
  Fintype.ofFinite _
/-- The completed greedy matching satisfies both quantitative conclusions of
the weighted matching lemma; the cycle condition is proved separately. -/
theorem weightedGreedyFullMatchingSorted_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (w : V → ℝ) (d r m : ℕ)
    (halpha : independenceNumber G ≤ m)
    (hdegree : ∀ x, D.degree x ≤ d)
    (hweight : ∀ v, 0 ≤ w v ∧ w v ≤ 1) :
    (weightedGreedyFullRun G D w r).unmatched.card ≤
        m * ((∑ n ∈ Finset.range (r + 1), (d + 1) ^ n) + 1) ∧
      (∑ i : (weightedGreedyFullRun G D w r).matching.edgeSet,
        |w ((weightedGreedyFullMatchingSorted G D w r).endpoint i false) -
          w ((weightedGreedyFullMatchingSorted G D w r).endpoint i true)|) ≤
        ((m * ((∑ n ∈ Finset.range (r + 1), (d + 1) ^ n) + 1) : ℕ) : ℝ) := by
  classical
  let M := weightedGreedyFullMatchingSorted G D w r
  let X := (weightedGreedyFullRun G D w r).unmatched
  let time := weightedGreedyFullRun_time G D w r
  let before : V → SimpleGraph V := fun _ => D ⊔ M.edgeGraph
  have hXclose : ∀ x ∈ X, ∀ y ∈ X,
      time x < time y → G.Adj x y →
      (before x).edist x y ≤ (r : ℕ∞) := by
    intro x hx y _ hlt hadj
    have h := weightedGreedyFullRun_unmatched_close G D w r hx hlt hadj
    simpa [before, M, weightedGreedyFullMatchingSorted_edgeGraph_eq] using h
  have hPclose : ∀ i j : (weightedGreedyFullRun G D w r).matching.edgeSet,
      w (M.endpoint i true) < w (M.endpoint i false) →
      time (M.endpoint i false) < time (M.endpoint j false) →
      w (M.endpoint i true) < w (M.endpoint j false) →
      G.Adj (M.endpoint i false) (M.endpoint j false) →
      (before (M.endpoint i false)).edist
        (M.endpoint i false) (M.endpoint j false) ≤ (r : ℕ∞) := by
    intro i j hstrict hlt hweight' hadj
    have hpair : (weightedGreedyFullRun G D w r).matching.Adj
        (M.endpoint i false) (M.endpoint i true) := by
      simpa [M, weightedGreedyFullMatchingSorted_edgeGraph_eq] using
        M.edgeGraph_adj_endpoints i
    have h := weightedGreedyFullRun_strict_pair_close G D w r
      hpair hstrict hlt hadj hweight'
    simpa [before, M, weightedGreedyFullMatchingSorted_edgeGraph_eq] using h
  exact matching_bounds_of_greedy_trace G D M X time
    (weightedGreedyFullRun_time_injective G D w r)
    before (fun _ => le_rfl) d r m halpha hdegree w hweight
    (weightedGreedyFullMatchingSorted_order G D w r) hXclose hPclose
/-- Removing any edge of a simple cycle leaves an alternate walk whose
length is at most one less than the cycle length. -/
theorem cycle_edge_alternative_walk
    {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) {a u v : V}
    (c : J.Walk a a) (hc : c.IsCycle)
    (he : s(u, v) ∈ c.edges) :
    ∃ p : (J.deleteEdges {s(u, v)}).Walk u v,
      p.length + 1 ≤ c.length := by
  classical
  let C : SimpleGraph V :=
    SimpleGraph.fromEdgeSet (c.edges.toFinset : Set (Sym2 V))
  have hCedge : C.edgeSet = (c.edges.toFinset : Set (Sym2 V)) := by
    simp only [C, SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    constructor
    · intro h
      exact h.1
    · intro h
      exact ⟨h, J.not_isDiag_of_mem_edgeSet
        (c.edges_subset_edgeSet (List.mem_toFinset.mp h))⟩
  have hCfin : C.edgeFinset = c.edges.toFinset := by
    ext e
    rw [C.mem_edgeFinset, hCedge]
    rfl
  have hCJ : C ≤ J := by
    intro x y hxy
    have hexy : s(x, y) ∈ C.edgeSet := C.mem_edgeSet.mpr hxy
    rw [hCedge] at hexy
    exact J.mem_edgeSet.mp (c.edges_subset_edgeSet (List.mem_toFinset.mp hexy))
  have hedge : ∀ e ∈ c.edges, e ∈ C.edgeSet := by
    intro e he'
    rw [hCedge]
    exact List.mem_toFinset.mpr he'
  let cC : C.Walk a a := c.transfer C hedge
  have hcC : cC.IsCycle := hc.transfer hedge
  have heC : s(u, v) ∈ cC.edges := by
    simpa [cC] using he
  have hReach : (C.deleteEdges {s(u, v)}).Reachable u v :=
    (SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle).mpr
      ⟨a, cC, hcC, heC⟩ |>.2
  obtain ⟨p⟩ := hReach
  let q : (C.deleteEdges {s(u, v)}).Path u v := p.toPath
  have hlen : (q : (C.deleteEdges {s(u, v)}).Walk u v).length ≤
      (C.deleteEdges {s(u, v)}).edgeFinset.card :=
    q.isTrail.length_le_card_edgeFinset
  have hcard : (C.deleteEdges {s(u, v)}).edgeFinset.card + 1 =
      c.length := by
    have hcard' :
        (C.deleteEdges (({s(u, v)} : Finset (Sym2 V)) : Set (Sym2 V))).edgeFinset.card + 1 =
          c.length := by
      rw [SimpleGraph.edgeFinset_deleteEdges, hCfin,
        Finset.sdiff_singleton_eq_erase]
      calc
        (c.edges.toFinset.erase s(u, v)).card + 1 =
            c.edges.toFinset.card :=
          Finset.card_erase_add_one (List.mem_toFinset.mpr he)
        _ = c.length := by
          exact (List.toFinset_card_of_nodup hc.isTrail.edges_nodup).trans
            c.length_edges
    have hs : (({s(u, v)} : Finset (Sym2 V)) : Set (Sym2 V)) =
        ({s(u, v)} : Set (Sym2 V)) := by
      ext e
      simp
    rw [← hs]
    exact hcard'
  have hdel : C.deleteEdges {s(u, v)} ≤ J.deleteEdges {s(u, v)} :=
    SimpleGraph.deleteEdges_mono hCJ
  let qJ : (J.deleteEdges {s(u, v)}).Walk u v :=
    (q : (C.deleteEdges {s(u, v)}).Walk u v).mapLe hdel
  refine ⟨qJ, ?_⟩
  have hlenEq : qJ.length = (q : (C.deleteEdges {s(u, v)}).Walk u v).length := by
    exact (q : (C.deleteEdges {s(u, v)}).Walk u v).length_map
      (SimpleGraph.Hom.ofLE hdel)
  omega
/-- Adding an edge whose endpoints were farther than r apart creates no
cycle of length at most r+1 using that new edge. -/
theorem no_short_cycle_contains_far_new_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (u v : V) (r : ℕ)
    (hfar : (r : ℕ∞) < H.edist u v)
    {a : V} (c : (H ⊔ singletonEdgeGraph u v).Walk a a)
    (hc : c.IsCycle) (hlen : c.length ≤ r + 1) :
    s(u, v) ∉ c.edges := by
  intro he
  obtain ⟨p, hp⟩ :=
    cycle_edge_alternative_walk (H ⊔ singletonEdgeGraph u v) c hc he
  have hdel : (H ⊔ singletonEdgeGraph u v).deleteEdges {s(u, v)} ≤ H := by
    intro x y hxy
    obtain ⟨hJ, hnot⟩ := (SimpleGraph.deleteEdges_adj).mp hxy
    rcases (SimpleGraph.sup_adj _ _ x y).mp hJ with hH | hE
    · exact hH
    · obtain ⟨hxy, _⟩ := (singletonEdgeGraph_adj_iff u v x y).mp hE
      have heq : s(x, y) = s(u, v) := by
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Sym2.eq_swap
      exact (hnot (by simp [heq])).elim
  let q : H.Walk u v := p.mapLe hdel
  have hlenp : p.length ≤ r := by omega
  have hdist : H.edist u v ≤ (r : ℕ∞) := by
    calc
      H.edist u v ≤ (q.length : ℕ∞) := q.edist_le
      _ = (p.length : ℕ∞) := by
        exact_mod_cast p.length_map (SimpleGraph.Hom.ofLE hdel)
      _ ≤ (r : ℕ∞) := by exact_mod_cast hlenp
  exact (not_lt_of_ge hdist) hfar
/-- Short cycles containing a marked edge remain excluded when a far edge
is added to both the graph and the marked-edge graph. -/
theorem no_short_marked_cycle_sup_far_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (H P : SimpleGraph V) (u v : V) (r : ℕ)
    (hshort : ∀ (a : V) (c : H.Walk a a),
      c.IsCycle → c.length ≤ r + 1 →
        ∀ e ∈ c.edges, e ∉ P.edgeSet)
    (hfar : (r : ℕ∞) < H.edist u v) :
    ∀ (a : V) (c : (H ⊔ singletonEdgeGraph u v).Walk a a),
      c.IsCycle → c.length ≤ r + 1 →
        ∀ e ∈ c.edges, e ∉ (P ⊔ singletonEdgeGraph u v).edgeSet := by
  intro a c hc hlen e he hem
  have hnoNew : s(u, v) ∉ c.edges :=
    no_short_cycle_contains_far_new_edge H u v r hfar c hc hlen
  have hnewEdge (f : Sym2 V)
      (hf : f ∈ (singletonEdgeGraph u v).edgeSet) : f = s(u, v) := by
    simp only [singletonEdgeGraph, SimpleGraph.edgeSet_fromEdgeSet,
      Set.mem_sdiff, Set.mem_singleton_iff] at hf
    exact hf.1
  have hedge : ∀ f ∈ c.edges, f ∈ H.edgeSet := by
    intro f hf
    have hmem : f ∈ (H ⊔ singletonEdgeGraph u v).edgeSet :=
      c.edges_subset_edgeSet hf
    rw [SimpleGraph.edgeSet_sup] at hmem
    rcases hmem with hH | hE
    · exact hH
    · exact (hnoNew ((hnewEdge f hE) ▸ hf)).elim
  rw [SimpleGraph.edgeSet_sup] at hem
  rcases hem with hP | hE
  · let cH : H.Walk a a := c.transfer H hedge
    have hcH : cH.IsCycle := hc.transfer hedge
    have hlenH : cH.length ≤ r + 1 := by
      simpa [cH] using hlen
    have heH : e ∈ cH.edges := by
      simpa [cH] using he
    exact hshort a cH hcH hlenH e heH hP
  · exact (hnoNew ((hnewEdge e hE) ▸ he)).elim
/-- No short cycle in D plus the current matching uses a matching edge. -/
def WeightedGreedyState.NoShortMatchingCycle
    {V : Type*} (D : SimpleGraph V) (r : ℕ)
    (st : WeightedGreedyState V) : Prop :=
  ∀ (a : V) (c : (D ⊔ st.matching).Walk a a),
    c.IsCycle → c.length ≤ r + 1 →
      ∀ e ∈ c.edges, e ∉ st.matching.edgeSet

theorem weightedGreedyInitial_noShortMatchingCycle
    {V : Type*} [Fintype V]
    (D : SimpleGraph V) (r : ℕ) :
    (weightedGreedyInitial (V := V)).NoShortMatchingCycle D r := by
  intro a c hc hlen e he
  simp [weightedGreedyInitial]

theorem weightedGreedyAdvanceWithChoice_noShortMatchingCycle
    {V : Type*} [Fintype V] [DecidableEq V]
    {G D : SimpleGraph V} {w : V → ℝ} {r : ℕ}
    (st : WeightedGreedyState V)
    (c : GreedyChoice G D st.matching st.unprocessed w r)
    (hshort : st.NoShortMatchingCycle D r) :
    (weightedGreedyAdvanceWithChoice st c).NoShortMatchingCycle D r := by
  cases h : c.partner with
  | none =>
      have hstep : (weightedGreedyAdvanceWithChoice st c).matching =
          st.matching := by
        simp [weightedGreedyAdvanceWithChoice, h]
      unfold WeightedGreedyState.NoShortMatchingCycle
      rw [hstep]
      exact hshort
  | some u =>
      have hfar : (r : ℕ∞) < (D ⊔ st.matching).edist c.selected u :=
        (c.partner_mem_unprocessed h).2.2.2
      have hnew := no_short_marked_cycle_sup_far_edge
        (D ⊔ st.matching) st.matching c.selected u r hshort hfar
      have hstep : (weightedGreedyAdvanceWithChoice st c).matching =
          st.matching ⊔ singletonEdgeGraph c.selected u := by
        simp [weightedGreedyAdvanceWithChoice, h]
      unfold WeightedGreedyState.NoShortMatchingCycle
      rw [hstep]
      have hassoc : D ⊔ st.matching ⊔ singletonEdgeGraph c.selected u =
          D ⊔ (st.matching ⊔ singletonEdgeGraph c.selected u) := by
        exact sup_assoc D st.matching (singletonEdgeGraph c.selected u)
      rw [hassoc] at hnew
      exact hnew

theorem weightedGreedyRun_noShortMatchingCycle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r n : ℕ)
    (st : WeightedGreedyState V)
    (hshort : st.NoShortMatchingCycle D r) :
    (weightedGreedyRun G D w r n st).NoShortMatchingCycle D r := by
  induction n generalizing st with
  | zero => exact hshort
  | succ n ih =>
      by_cases hR : st.unprocessed.Nonempty
      · simpa [weightedGreedyRun, hR] using
          ih (weightedGreedyAdvance G D w r st hR)
            (weightedGreedyAdvanceWithChoice_noShortMatchingCycle st _ hshort)
      · simpa [weightedGreedyRun, hR] using hshort

theorem weightedGreedyFullRun_noShortMatchingCycle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ) :
    (weightedGreedyFullRun G D w r).NoShortMatchingCycle D r :=
  weightedGreedyRun_noShortMatchingCycle G D w r (Fintype.card V)
    weightedGreedyInitial (weightedGreedyInitial_noShortMatchingCycle D r)
/-- The checked short-cycle conclusion stated for the indexed greedy matching. -/
theorem weightedGreedyFullMatchingSorted_noShortMatchingCycle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) (w : V → ℝ) (r : ℕ) :
    ∀ (a : V)
      (c : (D ⊔ (weightedGreedyFullMatchingSorted G D w r).edgeGraph).Walk a a),
      c.IsCycle → c.length ≤ r + 1 →
        ∀ e ∈ c.edges,
          e ∉ (weightedGreedyFullMatchingSorted G D w r).edgeGraph.edgeSet := by
  rw [weightedGreedyFullMatchingSorted_edgeGraph_eq]
  exact weightedGreedyFullRun_noShortMatchingCycle G D w r
end HadwigerLean
