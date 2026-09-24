import HadwigerLean.ReedSeymour.Parity

/-!
# Joining gated stems on an odd cycle

The two stems used in Reed--Seymour's parity argument are forced apart by
their gate vertices. This module turns them into an induced terminal
connector.
-/

namespace HadwigerLean
namespace ReedSeymour

variable {V : Type*} {G : SimpleGraph V}

theorem gated_stems_disjoint {a b u v : V}
    (p : G.Walk a u) (q : G.Walk b v)
    (hp : p.IsPath) (huq : u ∉ q.support)
    (hgate : ∀ r : G.Walk a v, u ∈ r.support) :
    p.support.Disjoint q.support := by
  classical
  apply List.disjoint_left.mpr
  intro x hxp hxq
  have hxu : x ≠ u := by
    intro h
    exact huq (h ▸ hxq)
  let r : G.Walk a v :=
    (p.takeUntil x hxp).append (q.dropUntil x hxq)
  have hgateR := hgate r
  have hnotLeft : u ∉ (p.takeUntil x hxp).support :=
    SimpleGraph.Walk.endpoint_notMem_support_takeUntil hp hxp hxu.symm
  have hnotRight : u ∉ (q.dropUntil x hxq).support := by
    intro h
    exact huq (q.support_dropUntil_subset_support hxq h)
  exact (by simpa only [r, SimpleGraph.Walk.mem_support_append_iff] using hgateR :
    u ∈ (p.takeUntil x hxp).support ∨ u ∈ (q.dropUntil x hxq).support).elim
      hnotLeft hnotRight

theorem gated_stems_cross_edge {a b u v : V}
    (p : G.Walk a u) (q : G.Walk b v)
    (hp : p.IsPath) (huq : u ∉ q.support)
    (hgate : ∀ r : G.Walk a v, u ∈ r.support)
    {x y : V} (hx : x ∈ p.support) (hy : y ∈ q.support)
    (hxy : G.Adj x y) : x = u := by
  classical
  by_contra hxu
  let r : G.Walk a v :=
    ((p.takeUntil x hx).concat hxy).append (q.dropUntil y hy)
  have hgateR := hgate r
  have hnotPrefix : u ∉ (p.takeUntil x hx).support :=
    SimpleGraph.Walk.endpoint_notMem_support_takeUntil hp hx (Ne.symm hxu)
  have hnotLeft : u ∉ ((p.takeUntil x hx).concat hxy).support := by
    simpa only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton]
      using (show ¬ (u ∈ (p.takeUntil x hx).support ∨ u = y) from
        fun h => h.elim hnotPrefix (fun h => huq (h ▸ hy)))
  have hnotRight : u ∉ (q.dropUntil y hy).support := by
    intro h
    exact huq (q.support_dropUntil_subset_support hy h)
  exact (by simpa only [r, SimpleGraph.Walk.mem_support_append_iff] using hgateR :
    u ∈ ((p.takeUntil x hx).concat hxy).support ∨
      u ∈ (q.dropUntil y hy).support).elim hnotLeft hnotRight

theorem gated_stem_avoids_terminal {I : Type*} (N : I → Set V)
    {u v b : V} {i : I} (q : G.Walk b v)
    (huq : u ∉ q.support)
    (hgate : ∀ (z : V), z ∈ N i → ∀ r : G.Walk z v, u ∈ r.support) :
    ∀ z, z ∈ q.support → z ∈ N i → False := by
  classical
  intro z hz hNi
  have h := hgate z hNi (q.dropUntil z hz)
  exact huq (q.support_dropUntil_subset_support hz h)

/-- Two vertex-disjoint paths joined by an edge form a path. -/
theorem joined_disjoint_paths_isPath {a b u v : V}
    (p : G.Walk a u) (q : G.Walk b v)
    (hp : p.IsPath) (hq : q.IsPath)
    (hdisj : p.support.Disjoint q.support)
    (huv : G.Adj u v) :
    ((p.concat huv).append q.reverse).IsPath := by
  have hvnot : v ∉ p.support := by
    intro hv
    exact (List.disjoint_left.mp hdisj hv) q.end_mem_support
  have hp' : (p.concat huv).IsPath := hp.concat hvnot huv
  have hq' : q.reverse.IsPath := hq.reverse
  have hvnotTail : v ∉ q.reverse.support.tail := by
    have hn := hq'.support_nodup
    rw [← q.reverse.cons_tail_support] at hn
    exact (List.nodup_cons.mp hn).1
  have htail : ∀ z, z ∈ q.reverse.support.tail → z ∈ q.support := by
    intro z hz
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using
      (List.mem_of_mem_tail hz : z ∈ q.reverse.support)
  have hdisj' : (p.concat huv).support.Disjoint q.reverse.support.tail := by
    apply List.disjoint_left.mpr
    intro z hz hzt
    rw [SimpleGraph.Walk.support_concat, List.mem_append] at hz
    rcases hz with hzp | hzv
    · exact (List.disjoint_left.mp hdisj hzp) (htail z hzt)
    · simp only [List.mem_singleton] at hzv
      exact hvnotTail (hzv ▸ hzt)
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
    List.nodup_append']
  exact ⟨hp'.support_nodup, hq'.support_nodup.tail, hdisj'⟩

/-- A joined stem has exactly the vertices of the two original stems. -/
theorem mem_joined_stems_support_iff {a b u v z : V}
    (p : G.Walk a u) (q : G.Walk b v) (huv : G.Adj u v) :
    z ∈ ((p.concat huv).append q.reverse).support ↔
      z ∈ p.support ∨ z ∈ q.support := by
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_concat, List.mem_append]
  simp only [List.mem_singleton, SimpleGraph.Walk.support_reverse,
    List.mem_reverse]
  constructor
  · rintro ((h | rfl) | h)
    · exact Or.inl h
    · exact Or.inr q.end_mem_support
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h


/-- If all cross edges are the joining edge, the joined path is induced. -/
theorem joined_disjoint_paths_isChordless {a b u v : V}
    (p : G.Walk a u) (q : G.Walk b v)
    (hcp : p.IsChordless) (hcq : q.IsChordless)
    (huv : G.Adj u v)
    (hcross : ∀ x, x ∈ p.support → ∀ y, y ∈ q.support →
      G.Adj x y → x = u ∧ y = v) :
    ((p.concat huv).append q.reverse).IsChordless := by
  rw [SimpleGraph.Walk.isChordless_iff_forall_mem_edges]
  intro x y hx hy hxy
  have hx' := (mem_joined_stems_support_iff p q huv).mp hx
  have hy' := (mem_joined_stems_support_iff p q huv).mp hy
  rcases hx' with hxp | hxq
  · rcases hy' with hyp | hyq
    · have he := hcp.mem_edges hxp hyp hxy
      simp [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_concat, he]
    · obtain ⟨rfl, rfl⟩ := hcross x hxp y hyq hxy
      simp [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_concat]
  · rcases hy' with hyp | hyq
    · obtain ⟨rfl, rfl⟩ := hcross y hyp x hxq hxy.symm
      simp [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_concat, Sym2.eq_swap]
    · have he := hcq.mem_edges hxq hyq hxy
      simp [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse,
        SimpleGraph.Walk.edges_concat, he]

/-- Adjacent gated stems of equal length parity give an induced odd connector
between their terminal sets. -/
theorem odd_connector_of_gated_stems {I : Type*} {N : I → Set V}
    {u x y : V} (c : G.Walk u u)
    (sx : GatedCycleStem G N c x) (sy : GatedCycleStem G N c y)
    (hxy : G.Adj x y)
    (hparity : sx.path.length % 2 = sy.path.length % 2) :
    ∃ r : G.Walk sx.start sy.start,
      IsTerminalConnector N sx.index sy.index r ∧ Odd r.length := by
  have hxq : x ∉ sy.path.support := by
    intro hx
    exact hxy.ne (sy.cycle_only x hx sx.cycle_mem)
  have hyp : y ∉ sx.path.support := by
    intro hy
    exact hxy.ne (sx.cycle_only y hy sy.cycle_mem).symm
  have hgateX : ∀ r : G.Walk sx.start y, x ∈ r.support :=
    sx.gate sx.start sx.start_mem y sy.cycle_mem
  have hgateY : ∀ r : G.Walk sy.start x, y ∈ r.support :=
    sy.gate sy.start sy.start_mem x sx.cycle_mem
  have hdisj : sx.path.support.Disjoint sy.path.support :=
    gated_stems_disjoint sx.path sy.path sx.isPath hxq hgateX
  have hcross : ∀ z, z ∈ sx.path.support → ∀ t, t ∈ sy.path.support →
      G.Adj z t → z = x ∧ t = y := by
    intro z hz t ht hzt
    exact ⟨gated_stems_cross_edge sx.path sy.path sx.isPath hxq hgateX
      hz ht hzt,
      gated_stems_cross_edge sy.path sx.path sy.isPath hyp hgateY
        ht hz hzt.symm⟩
  let r : G.Walk sx.start sy.start :=
    (sx.path.concat hxy).append sy.path.reverse
  have hrPath : r.IsPath :=
    joined_disjoint_paths_isPath sx.path sy.path sx.isPath sy.isPath hdisj hxy
  have hrChord : r.IsChordless :=
    joined_disjoint_paths_isChordless sx.path sy.path sx.isChordless sy.isChordless
      hxy hcross
  have hNix : ∀ z, z ∈ sy.path.support → z ∈ N sx.index → False :=
    gated_stem_avoids_terminal N sy.path hxq
      (fun z hz p => sx.gate z hz y sy.cycle_mem p)
  have hNjy : ∀ z, z ∈ sx.path.support → z ∈ N sy.index → False :=
    gated_stem_avoids_terminal N sx.path hyp
      (fun z hz p => sy.gate z hz x sx.cycle_mem p)
  refine ⟨r, ⟨hrPath, hrChord, sx.start_mem, sy.start_mem, ?_, ?_⟩, ?_⟩
  · intro z hz hNi
    rcases (mem_joined_stems_support_iff sx.path sy.path hxy).mp hz with hzP | hzQ
    · exact sx.terminal_only z hzP hNi
    · exact False.elim (hNix z hzQ hNi)
  · intro z hz hNj
    rcases (mem_joined_stems_support_iff sx.path sy.path hxy).mp hz with hzP | hzQ
    · exact False.elim (hNjy z hzP hNj)
    · exact sy.terminal_only z hzQ hNj
  · have hrLen : r.length = sx.path.length + 1 + sy.path.length := by
      simp [r, SimpleGraph.Walk.length_append]
    rw [hrLen]
    exact odd_add_one_of_same_parity hparity
end ReedSeymour
end HadwigerLean
