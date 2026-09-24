import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Ends.Defs

/-!
# Parity lemmas for Reed--Seymour decompositions

The Reed--Seymour argument studies a minimal connected set meeting several terminal sets.
Its key obstruction is an odd path between two distinct terminal sets.  This file records
the graph-theoretic parity lemmas used in that argument, independently of weights and eggs.
-/

namespace HadwigerLean

namespace ReedSeymour

variable {V : Type*} {G : SimpleGraph V}

/-- A preconnected graph with no odd closed walk has a two-coloring. -/
theorem colorable_two_of_even_closed_walks (hconn : G.Preconnected)
    (heven : ∀ (v : V) (p : G.Walk v v), Even p.length) : G.Colorable 2 := by
  classical
  by_cases hV : Nonempty V
  · let r : V := Classical.choice hV
    let p (v : V) : G.Walk r v := (hconn r v).some
    let c (v : V) : Fin 2 := ⟨(p v).length % 2, Nat.mod_lt _ (by decide)⟩
    refine ⟨SimpleGraph.Coloring.mk c ?_⟩
    intro v w hadj hEq
    have hclosed : Even ((p v).append hadj.toWalk |>.append (p w).reverse).length :=
      heven r _
    have hlen : ((p v).append hadj.toWalk |>.append (p w).reverse).length =
        (p v).length + 1 + (p w).length := by
      simp [SimpleGraph.Walk.length_append]
    have hmod : (p v).length % 2 = (p w).length % 2 := by
      simpa [c] using congrArg Fin.val hEq
    rw [hlen] at hclosed
    have hclosedmod : ((p v).length + 1 + (p w).length) % 2 = 0 :=
      Nat.even_iff.mp hclosed
    clear hEq
    omega
  · haveI : IsEmpty V := not_nonempty_iff.mp hV
    exact SimpleGraph.Colorable.of_isEmpty 2


/-- In a preconnected graph, failure of bipartiteness produces an odd closed walk. -/
theorem exists_odd_closed_walk_of_not_colorable_two (hconn : G.Preconnected)
    (hnot : ¬ G.Colorable 2) :
    ∃ (v : V) (p : G.Walk v v), Odd p.length := by
  by_contra hnone
  apply hnot
  apply colorable_two_of_even_closed_walks hconn
  intro v p
  by_contra hneven
  exact hnone ⟨v, p, (Nat.not_even_iff_odd).mp hneven⟩

/-- Failure of bipartiteness in a connected graph yields an odd cycle. -/
theorem exists_odd_cycle_of_not_colorable_two (hconn : G.Connected)
    (hnot : ¬ G.Colorable 2) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Odd c.length := by
  classical
  obtain ⟨T, hTG, hT⟩ := hconn.exists_isTree_le
  let col : T.Coloring (Fin 2) := hT.isBipartite.some
  obtain ⟨u, v, huv, hcol⟩ :
      ∃ u v, G.Adj u v ∧ col u = col v := by
    by_contra h
    apply hnot
    refine ⟨SimpleGraph.Coloring.mk col ?_⟩
    intro u v huv heq
    exact h ⟨u, v, huv, heq⟩
  have hnotT : ¬ T.Adj u v := fun h => col.valid h hcol
  obtain ⟨p, hp⟩ := (hT.connected.preconnected u v).exists_isPath
  let b : T.Coloring Bool := T.recolorOfEquiv finTwoEquiv col
  have hb : b u = b v := by
    change finTwoEquiv (col u) = finTwoEquiv (col v)
    exact congrArg finTwoEquiv hcol
  have hEven : Even p.length := (b.even_length_iff_congr p).mpr (by simp [hb])
  let q : G.Walk v u := p.reverse.mapLe hTG
  have hq : q.IsPath := hp.reverse.mapLe hTG
  have hedge : s(u, v) ∉ q.edges := by
    intro he
    have heT : s(u, v) ∈ p.reverse.edges := by
      simpa only [q, SimpleGraph.Walk.edges_mapLe_eq_edges] using he
    exact hnotT (p.reverse.adj_of_mem_edges heT)
  have hcyc : (SimpleGraph.Walk.cons huv q).IsCycle :=
    SimpleGraph.Path.cons_isCycle (⟨q, hq⟩ : G.Path v u) huv hedge
  have hqLen : q.length = p.length := by
    change (p.reverse.map (SimpleGraph.Hom.ofLE hTG)).length = p.length
    rw [SimpleGraph.Walk.length_map, SimpleGraph.Walk.length_reverse]
  have hlen : (SimpleGraph.Walk.cons huv q).length = p.length + 1 := by
    simpa only [SimpleGraph.Walk.length_cons] using congrArg (· + 1) hqLen
  have hOdd : Odd (SimpleGraph.Walk.cons huv q).length := by
    rw [hlen]
    apply (Nat.not_even_iff_odd).mp
    have hm : p.length % 2 = 0 := Nat.even_iff.mp hEven
    intro he
    have hm' : (p.length + 1) % 2 = 0 := Nat.even_iff.mp he
    omega
  exact ⟨u, _, hcyc, hOdd⟩

/-- A Boolean label that flips on every edge of a walk agrees at the endpoints
exactly when the walk has even length. -/
theorem walk_even_length_iff_end_color_of_flip (f : V → Bool)
    {u v : V} (p : G.Walk u v)
    (hflip : ∀ x y, s(x, y) ∈ p.edges → f x ≠ f y) :
    Even p.length ↔ (f u ↔ f v) := by
  revert hflip
  induction p with
  | nil => simp
  | @cons u v w hadj p ih =>
      intro hflip
      have hfirst : f u ≠ f v := hflip u v (by simp)
      have hrest : ∀ x y, s(x, y) ∈ p.edges → f x ≠ f y := by
        intro x y he
        exact hflip x y (by simp [he])
      have hrec := ih hrest
      simp only [SimpleGraph.Walk.length_cons, Nat.even_add_one]
      have hfirst' : (¬f u ↔ f v) := by
        rw [← not_iff, ← Bool.eq_iff_iff]
        exact hfirst
      tauto

/-- Every Boolean labeling of the vertices of an odd closed walk is constant
across at least one edge of that walk. -/
theorem odd_closed_walk_has_equal_color_edge {u : V} (p : G.Walk u u)
    (hodd : Odd p.length) (f : V → Bool) :
    ∃ x y, s(x, y) ∈ p.edges ∧ f x = f y := by
  by_contra hnone
  have hflip : ∀ x y, s(x, y) ∈ p.edges → f x ≠ f y := by
    intro x y he heq
    exact hnone ⟨x, y, he, heq⟩
  have heven : Even p.length :=
    (walk_even_length_iff_end_color_of_flip f p hflip).mpr Iff.rfl
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- On an odd closed walk, any assignment of natural-number lengths gives
adjacent vertices with lengths of the same parity. -/
theorem odd_closed_walk_has_equal_parity_edge {u : V} (p : G.Walk u u)
    (hodd : Odd p.length) (d : V → ℕ) :
    ∃ x y, s(x, y) ∈ p.edges ∧ d x % 2 = d y % 2 := by
  let f (x : V) : Bool := decide (d x % 2 = 0)
  obtain ⟨x, y, hxy, hcolor⟩ := odd_closed_walk_has_equal_color_edge p hodd f
  refine ⟨x, y, hxy, ?_⟩
  rcases Nat.mod_two_eq_zero_or_one (d x) with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one (d y) with hy | hy <;>
    simp_all [f]

/-- A path between two terminal sets that meets each of them only at its designated endpoint. -/
structure IsTerminalConnector {I : Type*} (N : I → Set V) (i j : I)
    {a b : V} (p : G.Walk a b) : Prop where
  isPath : p.IsPath
  isChordless : p.IsChordless
  start_mem : a ∈ N i
  end_mem : b ∈ N j
  start_only : ∀ x, x ∈ p.support → x ∈ N i → x = a
  end_only : ∀ x, x ∈ p.support → x ∈ N j → x = b

/-- Every induced endpoint-only connector between distinct terminal sets has even length. -/
def NoOddConnector {I : Type*} (H : SimpleGraph V) (N : I → Set V) : Prop :=
  ∀ (i j : I), i ≠ j → ∀ {a b : V} (p : H.Walk a b),
    IsTerminalConnector N i j p → Even p.length

/-- Equal parities on two connector paths make their joined path odd. -/
theorem odd_add_one_of_same_parity {a b : ℕ} (h : a % 2 = b % 2) :
    Odd (a + 1 + b) := by
  apply (Nat.not_even_iff_odd).mp
  intro he
  have hm : (a + 1 + b) % 2 = 0 := Nat.even_iff.mp he
  omega

/-- A shortest walk between its endpoints has no chord. This supplements
`Walk.isPath_of_length_eq_dist` from Mathlib. -/
theorem shortest_walk_isChordless {a b : V} (p : G.Walk a b)
    (hshort : p.length = G.dist a b) : p.IsChordless := by
  classical
  rw [SimpleGraph.Walk.isChordless_iff_forall_mem_edges]
  intro x y hx hy hxy
  obtain ⟨i, hi, hiBound⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
  obtain ⟨j, hj, hjBound⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hy
  have forward {i j : ℕ} (hij : i < j)
      (hadj : G.Adj (p.getVert i) (p.getVert j)) :
      s(p.getVert i, p.getVert j) ∈ p.edges := by
    let q := (p.drop i).take (j - i)
    have hsub : q.IsSubwalk p :=
      ((p.drop i).isSubwalk_take (j - i)).trans (p.isSubwalk_drop i)
    have hqDist : q.length =
        G.dist (p.getVert i) ((p.drop i).getVert (j - i)) :=
      SimpleGraph.length_eq_dist_of_subwalk hshort hsub
    have hqEnd : (p.drop i).getVert (j - i) = p.getVert j := by
      rw [SimpleGraph.Walk.drop_getVert]
      congr 1
      omega
    have hqLen : q.length = 1 := by
      calc
        q.length = G.dist (p.getVert i) ((p.drop i).getVert (j - i)) := hqDist
        _ = G.dist (p.getVert i) (p.getVert j) :=
          congrArg (G.dist (p.getVert i)) hqEnd
        _ = 1 := G.dist_eq_one_iff_adj.mpr hadj
    have hadjQ : G.Adj (p.getVert i) ((p.drop i).getVert (j - i)) := by
      simpa only [hqEnd] using hadj
    have hqEq : q = hadjQ.toWalk :=
      SimpleGraph.Walk.eq_of_length_le_one hqLen.le (by simp)
    have hmemQ : s(p.getVert i, (p.drop i).getVert (j - i)) ∈ q.edges := by
      rw [hqEq]
      simp
    have hmemP := hsub.edges_subset hmemQ
    simpa only [hqEnd] using hmemP
  have hij : i ≠ j := by
    intro heq
    apply hxy.ne
    calc x = p.getVert i := hi.symm
      _ = p.getVert j := by rw [heq]
      _ = y := hj
  rcases lt_or_gt_of_ne hij with hij | hji
  · simpa only [hi, hj] using forward hij (by simpa only [hi, hj] using hxy)
  · have h := forward hji (by simpa only [hi, hj] using hxy.symm)
    have h' : s(p.getVert i, p.getVert j) ∈ p.edges := by
      simpa only [Sym2.eq_swap] using h
    simpa only [hi, hj] using h'

/-- Among walks from `A` to `B`, a shortest one is an induced path and
meets each terminal set only at its corresponding endpoint. -/
theorem exists_shortest_terminal_connector (hconn : G.Preconnected)
    {A B : Set V} (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ (a b : V) (p : G.Walk a b), a ∈ A ∧ b ∈ B ∧
      p.IsPath ∧ p.IsChordless ∧
      (∀ x, x ∈ p.support → x ∈ A → x = a) ∧
      (∀ x, x ∈ p.support → x ∈ B → x = b) := by
  classical
  let P (n : ℕ) : Prop :=
    ∃ (a : V), a ∈ A ∧ ∃ (b : V), b ∈ B ∧
      ∃ (p : G.Walk a b), p.length = n
  have hP : ∃ n, P n := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    let q : G.Walk a b := (hconn a b).some
    exact ⟨q.length, a, ha, b, hb, q, rfl⟩
  obtain ⟨a, ha, b, hb, p, hpn⟩ := (Nat.find_spec hP : P (Nat.find hP))
  have hmin : ∀ (a' : V), a' ∈ A → ∀ (b' : V), b' ∈ B →
      ∀ (q : G.Walk a' b'), p.length ≤ q.length := by
    intro a' ha' b' hb' q
    rw [hpn]
    exact Nat.find_min' hP ⟨a', ha', b', hb', q, rfl⟩
  have hshort : p.length = G.dist a b := by
    obtain ⟨q, hq⟩ := (hconn a b).exists_walk_length_eq_dist
    have hle := hmin a ha b hb q
    have hge := G.dist_le p
    omega
  refine ⟨a, b, p, ha, hb, p.isPath_of_length_eq_dist hshort,
    shortest_walk_isChordless p hshort, ?_, ?_⟩
  · intro x hx hAx
    by_contra hne
    have hlt := p.length_dropUntil_lt_length hx hne
    have hle := hmin x hAx b hb (p.dropUntil x hx)
    omega
  · intro x hx hBx
    by_contra hne
    have hlt := p.length_takeUntil_lt_length hx hne
    have hle := hmin a ha x hBx (p.takeUntil x hx)
    omega

/-- A terminal set can force a walk to another nonempty set through at most
one vertex of that target set. This gives distinct gate indices on a cycle. -/
theorem unique_gate_for_terminal_set (hconn : G.Preconnected)
    {A B : Set V} (hA : A.Nonempty) (hB : B.Nonempty)
    {x y : V} (hx : x ∈ B) (hy : y ∈ B)
    (hgateX : ∀ (a : V), a ∈ A → ∀ (b : V), b ∈ B →
      ∀ (p : G.Walk a b), x ∈ p.support)
    (hgateY : ∀ (a : V), a ∈ A → ∀ (b : V), b ∈ B →
      ∀ (p : G.Walk a b), y ∈ p.support) : x = y := by
  obtain ⟨a, b, p, ha, hb, _, _, _, hlast⟩ :=
    exists_shortest_terminal_connector hconn hA hB
  have hxb : x = b := hlast x (hgateX a ha b hb p) hx
  have hyb : y = b := hlast y (hgateY a ha b hb p) hy
  exact hxb.trans hyb.symm

/-- If all terminal-to-target walks pass through `x` in the target set,
a shortest such walk ends exactly at `x`. -/
theorem exists_shortest_stem_to_gate (hconn : G.Preconnected)
    {A B : Set V} (hA : A.Nonempty) (hB : B.Nonempty)
    {x : V} (hx : x ∈ B)
    (hgate : ∀ (a : V), a ∈ A → ∀ (b : V), b ∈ B →
      ∀ (p : G.Walk a b), x ∈ p.support) :
    ∃ (a : V) (p : G.Walk a x), a ∈ A ∧ p.IsPath ∧ p.IsChordless ∧
      (∀ z, z ∈ p.support → z ∈ A → z = a) ∧
      (∀ z, z ∈ p.support → z ∈ B → z = x) := by
  obtain ⟨a, b, p, ha, hb, hpath, hchord, hfirst, hlast⟩ :=
    exists_shortest_terminal_connector hconn hA hB
  have hxb : x = b := hlast x (hgate a ha b hb p) hx
  subst b
  exact ⟨a, p, ha, hpath, hchord, hfirst, hlast⟩
/-- Minimality among connected sets meeting every terminal set. -/
def IsMinimalConnectedTransversal {I : Type*} (H : SimpleGraph V)
    (N : I → Set V) : Prop :=
  H.Connected ∧ (∀ i, (N i).Nonempty) ∧
    ∀ S : Set V, (H.induce S).Connected →
      (∀ i, ∃ v, v ∈ N i ∧ v ∈ S) → S = Set.univ

/-- A walk avoiding the deleted vertex stays in its starting component. -/
theorem walk_end_mem_componentCompl_of_avoid {x a b : V}
    (C : G.ComponentCompl {x}) (p : G.Walk a b)
    (ha : a ∈ C) (hx : x ∉ p.support) : b ∈ C := by
  induction p with
  | nil => simpa using ha
  | @cons u v w huv q ih =>
      have hvx : v ≠ x := by
        intro hvx
        apply hx
        subst v
        simp
      have hvC : v ∈ C :=
        SimpleGraph.ComponentCompl.mem_of_adj u v ha (by simpa using hvx) huv
      apply ih hvC
      intro hq
      exact hx (by simp [hq])
/-- The vertices of a component after deleting one vertex induce a connected graph. -/
theorem connected_induce_componentCompl {x : V}
    (C : G.ComponentCompl {x}) : (G.induce (C : Set V)).Connected := by
  let f : {z : ({x}ᶜ : Set V) // z ∈ SimpleGraph.ConnectedComponent.supp C} →
      (C : Set V) := fun z => ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
  let hom : C.toSimpleGraph →g G.induce (C : Set V) := {
    toFun := f
    map_rel' := by
      intro u v huv
      exact huv
  }
  have hf : Function.Surjective hom := by
    rintro ⟨v, hv⟩
    obtain ⟨hvc, hvcC⟩ := hv
    refine ⟨⟨⟨v, hvc⟩, hvcC⟩, ?_⟩
    rfl
  exact C.connected_toSimpleGraph.map hom hf
/-- A component left after deleting a vertex of a minimal connected
transversal must miss at least one terminal set. -/
theorem minimal_component_misses_terminal {I : Type*} {N : I → Set V}
    (hmin : IsMinimalConnectedTransversal G N) {x : V}
    (C : G.ComponentCompl {x}) :
    ∃ i : I, ∀ v, v ∈ N i → v ∉ C := by
  classical
  by_contra hn
  push Not at hn
  have hS : (C : Set V) = Set.univ :=
    hmin.2.2 (C : Set V) (connected_induce_componentCompl C) hn
  have hxC : x ∈ C := by
    change x ∈ (C : Set V)
    rw [hS]
    trivial
  exact (SimpleGraph.ComponentCompl.notMem_of_mem hxC) (by simp)

/-- If a terminal set misses a deletion component, its deleted vertex is a
gate for every walk from that terminal set into the component. -/
theorem component_missing_terminal_is_gate {I : Type*} {N : I → Set V}
    {x : V} (C : G.ComponentCompl {x}) {i : I}
    (hmiss : ∀ v, v ∈ N i → v ∉ C)
    {B : Set V} (hB : ∀ b, b ∈ B → b = x ∨ b ∈ C) :
    ∀ (a : V), a ∈ N i → ∀ (b : V), b ∈ B →
      ∀ (p : G.Walk a b), x ∈ p.support := by
  intro a ha b hb p
  rcases hB b hb with rfl | hbC
  · exact p.end_mem_support
  · by_contra hx
    have hr : x ∉ p.reverse.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hx
    have haC := walk_end_mem_componentCompl_of_avoid C p.reverse hbC hr
    exact hmiss a ha haC
/-- Every vertex of a walk avoiding the deleted vertex remains in its
starting deletion component. -/
theorem walk_support_subset_componentCompl_of_avoid {x a b : V}
    (C : G.ComponentCompl {x}) (p : G.Walk a b)
    (ha : a ∈ C) (hx : x ∉ p.support) :
    ∀ v, v ∈ p.support → v ∈ C := by
  classical
  intro v hv
  apply walk_end_mem_componentCompl_of_avoid C (p.takeUntil v hv) ha
  intro hxprefix
  exact hx (p.support_takeUntil_subset_support hv hxprefix)
/-- All vertices of a cycle except one lie in the same component after
that vertex is deleted. -/
theorem cycle_except_vertex_in_one_component {u x : V}
    (c : G.Walk u u) (hc : c.IsCycle) (hx : x ∈ c.support) :
    ∃ C : G.ComponentCompl {x},
      ∀ y, y ∈ c.support → y ≠ x → y ∈ C := by
  classical
  let r := c.rotate x hx
  have hr : r.IsCycle := hc.rotate hx
  let q := r.tail.dropLast
  have htailNN : ¬ r.tail.Nil := by
    intro hnil
    have hlen : r.tail.length = 0 := hnil.length_eq_zero
    have hplus := r.length_tail_add_one hr.not_nil
    have hthree := hr.three_le_length
    omega
  have hqSupport : r.tail.support = q.support ++ [x] := by
    exact (r.tail.support_dropLast_concat htailNN).symm
  have hxq : x ∉ q.support := by
    have hnodup : (q.support ++ [x]).Nodup := by
      rw [← hqSupport]
      exact hr.isPath_tail.support_nodup
    have hdis := List.disjoint_of_nodup_append hnodup
    intro h
    exact hdis h (by simp)
  have hfirst : r.getVert 1 ≠ x := by
    have hadj : G.Adj (r.getVert 0) (r.getVert 1) :=
      r.adj_getVert_succ (by have hthree := hr.three_le_length; omega)
    have h : G.Adj x (r.getVert 1) := by simpa using hadj
    exact h.ne.symm
  let C : G.ComponentCompl {x} :=
    G.componentComplMk (K := {x}) (by simpa using hfirst)
  refine ⟨C, ?_⟩
  intro y hy hyx
  have hyr : y ∈ r.support :=
    (c.mem_support_rotate_iff x hx).mpr hy
  have hmemq : y ∈ q.support := by
    have hrSupport : r.support = x :: r.tail.support :=
      (r.cons_support_tail hr.not_nil).symm
    rw [hrSupport, hqSupport] at hyr
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hyr
    rcases hyr with hyx' | hyr
    · exact (hyx hyx').elim
    · rcases hyr with h | h
      · exact h
      · exact (hyx h).elim
  have hstart : r.getVert 1 ∈ C :=
    G.componentComplMk_mem (K := {x}) (by simpa using hfirst)
  exact walk_support_subset_componentCompl_of_avoid C q hstart hxq y hmemq
/-- Every vertex on a cycle in a minimal connected transversal has a
terminal label whose walks into the cycle must pass that vertex. -/
theorem cycle_vertex_has_gate {I : Type*} {N : I → Set V}
    (hmin : IsMinimalConnectedTransversal G N)
    {u : V} (c : G.Walk u u) (hc : c.IsCycle)
    {x : V} (hx : x ∈ c.support) :
    ∃ i : I, ∀ (a : V), a ∈ N i → ∀ (b : V), b ∈ c.support →
      ∀ (p : G.Walk a b), x ∈ p.support := by
  obtain ⟨C, hcycle⟩ := cycle_except_vertex_in_one_component c hc hx
  obtain ⟨i, hmiss⟩ := minimal_component_misses_terminal hmin C
  refine ⟨i, component_missing_terminal_is_gate C hmiss ?_⟩
  intro b hb
  by_cases hbx : b = x
  · exact Or.inl hbx
  · exact Or.inr (hcycle b hb hbx)

/-- Distinct cycle vertices cannot carry the same gate label. -/
theorem cycle_gate_injective {I : Type*} {N : I → Set V}
    (hconn : G.Preconnected)
    {u : V} (c : G.Walk u u)
    {x y : V} {i : I} (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hA : (N i).Nonempty)
    (hgateX : ∀ (a : V), a ∈ N i → ∀ (b : V), b ∈ c.support →
      ∀ (p : G.Walk a b), x ∈ p.support)
    (hgateY : ∀ (a : V), a ∈ N i → ∀ (b : V), b ∈ c.support →
      ∀ (p : G.Walk a b), y ∈ p.support) : x = y := by
  exact unique_gate_for_terminal_set hconn hA ⟨x, hx⟩ hx hy hgateX hgateY
/-- A shortest induced stem from a terminal set to a cycle vertex, together
with its gate property. -/
structure GatedCycleStem {I : Type*} (H : SimpleGraph V) (N : I → Set V)
    {u : V} (c : H.Walk u u) (x : V) where
  index : I
  start : V
  path : H.Walk start x
  cycle_mem : x ∈ c.support
  start_mem : start ∈ N index
  isPath : path.IsPath
  isChordless : path.IsChordless
  terminal_only : ∀ z, z ∈ path.support → z ∈ N index → z = start
  cycle_only : ∀ z, z ∈ path.support → z ∈ c.support → z = x
  gate : ∀ (a : V), a ∈ N index → ∀ (b : V), b ∈ c.support →
    ∀ (p : H.Walk a b), x ∈ p.support

/-- Every cycle vertex in a minimal connected transversal admits a gated
induced stem from one of the terminal sets. -/
theorem exists_gated_cycle_stem {I : Type*} {N : I → Set V}
    (hmin : IsMinimalConnectedTransversal G N)
    {u : V} (c : G.Walk u u) (hc : c.IsCycle)
    {x : V} (hx : x ∈ c.support) :
    Nonempty (GatedCycleStem G N c x) := by
  obtain ⟨i, hgate⟩ := cycle_vertex_has_gate hmin c hc hx
  obtain ⟨a, p, ha, hp, hc', hterminal, hcycle⟩ :=
    exists_shortest_stem_to_gate hmin.1.preconnected
      (hmin.2.1 i) ⟨x, hx⟩ hx hgate
  exact ⟨{
    index := i
    start := a
    path := p
    cycle_mem := hx
    start_mem := ha
    isPath := hp
    isChordless := hc'
    terminal_only := hterminal
    cycle_only := hcycle
    gate := hgate
  }⟩

/-- Gated stems attached to distinct cycle vertices use distinct labels. -/
theorem GatedCycleStem.index_ne_of_vertex_ne
    {I : Type*} {N : I → Set V}
    (hmin : IsMinimalConnectedTransversal G N)
    {u : V} {c : G.Walk u u} {x y : V}
    (sx : GatedCycleStem G N c x) (sy : GatedCycleStem G N c y)
    (hxy : x ≠ y) : sx.index ≠ sy.index := by
  intro hi
  have hxy' := cycle_gate_injective hmin.1.preconnected c
    sx.cycle_mem sy.cycle_mem (hmin.2.1 sx.index) sx.gate
    (hi ▸ sy.gate)
  exact hxy hxy'
/-- An odd cycle has adjacent vertices whose chosen gated stems have
lengths of the same parity. -/
theorem odd_cycle_has_equal_parity_gated_stems
    {I : Type*} {N : I → Set V}
    (hmin : IsMinimalConnectedTransversal G N)
    {u : V} (c : G.Walk u u) (hc : c.IsCycle) (hodd : Odd c.length) :
    ∃ x y, s(x, y) ∈ c.edges ∧
      ∃ (sx : GatedCycleStem G N c x) (sy : GatedCycleStem G N c y),
        sx.path.length % 2 = sy.path.length % 2 := by
  classical
  let stem (z : {v : V // v ∈ c.support}) : GatedCycleStem G N c z.1 :=
    Classical.choice (exists_gated_cycle_stem hmin c hc z.2)
  let d (z : V) : ℕ :=
    if hz : z ∈ c.support then (stem ⟨z, hz⟩).path.length else 0
  obtain ⟨x, y, hxy, hparity⟩ :=
    odd_closed_walk_has_equal_parity_edge c hodd d
  have hx : x ∈ c.support := c.fst_mem_support_of_mem_edges hxy
  have hy : y ∈ c.support := c.snd_mem_support_of_mem_edges hxy
  refine ⟨x, y, hxy, stem ⟨x, hx⟩, stem ⟨y, hy⟩, ?_⟩
  simpa only [d, dif_pos hx, dif_pos hy] using hparity
/-- The equal-parity stems selected on an odd cycle necessarily have
different terminal labels. -/
theorem odd_cycle_has_distinct_equal_parity_gated_stems
    {I : Type*} {N : I → Set V}
    (hmin : IsMinimalConnectedTransversal G N)
    {u : V} (c : G.Walk u u) (hc : c.IsCycle) (hodd : Odd c.length) :
    ∃ x y, s(x, y) ∈ c.edges ∧
      ∃ (sx : GatedCycleStem G N c x) (sy : GatedCycleStem G N c y),
        sx.index ≠ sy.index ∧
        sx.path.length % 2 = sy.path.length % 2 := by
  obtain ⟨x, y, hxy, sx, sy, hparity⟩ :=
    odd_cycle_has_equal_parity_gated_stems hmin c hc hodd
  have hxy' : x ≠ y := (c.adj_of_mem_edges hxy).ne
  exact ⟨x, y, hxy, sx, sy,
    sx.index_ne_of_vertex_ne hmin sy hxy', hparity⟩
end ReedSeymour

end HadwigerLean
