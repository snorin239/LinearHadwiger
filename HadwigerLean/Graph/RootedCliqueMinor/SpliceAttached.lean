import HadwigerLean.Graph.RootedCliqueMinor.TorsoConnectivity
import HadwigerLean.Graph.RootedCliqueMinor.ContractionAttached

/-!
# Splicing an attached clique model across a separation

Disjoint paths from original roots to every boundary vertex extend an
attached clique model on the far shore back to the original roots. The
initial vertex of each path is excluded from its new branch.
-/

namespace HadwigerLean

universe v

namespace RootAttachedCliqueModel

variable {V : Type v} {G : SimpleGraph V}

/-- The path vertices after the first vertex. For a singleton path this is
empty; for a nontrivial path it is the support of the path's tail. -/
def pathAfterStart {u w : V} (p : G.Path u w) : Set V :=
  pathVertexSet p \ {u}

theorem pathAfterStart_subset {u w : V} (p : G.Path u w) :
    pathAfterStart p ⊆ pathVertexSet p :=
  Set.diff_subset

theorem start_not_mem_pathAfterStart {u w : V} (p : G.Path u w) :
    u ∉ pathAfterStart p := by
  simp [pathAfterStart]

theorem pathAfterStart_eq_empty_of_nil {u w : V}
    (p : G.Path u w) (hnil : (p : G.Walk u w).Nil) :
    pathAfterStart p = ∅ := by
  have huw : u = w := hnil.eq
  subst w
  rw [p.loop_eq]
  simp [pathAfterStart, pathVertexSet]

theorem start_not_mem_tail_support {u w : V}
    (p : G.Path u w) (hnil : ¬(p : G.Walk u w).Nil) :
    u ∉ (p : G.Walk u w).tail.support := by
  have hnodup := p.property.support_nodup
  rw [← (p : G.Walk u w).cons_support_tail hnil] at hnodup
  exact (List.nodup_cons.mp hnodup).1

theorem pathAfterStart_eq_tail_support {u w : V}
    (p : G.Path u w) (hnil : ¬(p : G.Walk u w).Nil) :
    pathAfterStart p =
      {x | x ∈ (p : G.Walk u w).tail.support} := by
  ext x
  have hsupport := (p : G.Walk u w).cons_support_tail hnil
  have hnot := start_not_mem_tail_support p hnil
  simp only [pathAfterStart, pathVertexSet, Set.mem_diff,
    Set.mem_singleton_iff, Set.mem_setOf_eq, ← hsupport, List.mem_cons]
  constructor
  · rintro ⟨hx | hx, hne⟩
    · exact (hne hx).elim
    · exact hx
  · intro hx
    exact ⟨Or.inr hx, fun heq => hnot (heq ▸ hx)⟩

theorem pathAfterStart_connected {u w : V}
    (p : G.Path u w) (hnil : ¬(p : G.Walk u w).Nil) :
    (G.induce (pathAfterStart p)).Connected := by
  rw [pathAfterStart_eq_tail_support p hnil]
  exact (p : G.Walk u w).tail.connected_induce_support

/-- The far-side clique model can be enlarged by the interior of a
vertex-disjoint linkage whose finishes each attach to the assigned branch.
All branches avoid the linkage paths. -/
noncomputable def extendAlongLinkage {r : ℕ}
    {P : IndexedPairs (Fin r) V} (L : IndexedLinkage G P)
    (N : MinorModel (SimpleGraph.completeGraph (Fin r)) G)
    (havoid : ∀ i j, Disjoint (N.branch i) (pathVertexSet (L.path j)))
    (hattach : ∀ i, ∃ y ∈ N.branch i, G.Adj (P.finish i) y) :
    RootAttachedCliqueModel G P.start := by
  let B : Fin r → Set V := fun i =>
    N.branch i ∪ pathAfterStart (L.path i)
  have htailPath (i : Fin r) :
      pathAfterStart (L.path i) ⊆ pathVertexSet (L.path i) :=
    pathAfterStart_subset (L.path i)
  refine {
    branch := B
    root_injective := L.start_injective
    connected := ?_
    disjoint := ?_
    avoids_roots := ?_
    adjacent := ?_
    attached := ?_
  }
  · intro i
    obtain ⟨y, hy, hxy⟩ := hattach i
    by_cases hnil : (L.path i : G.Walk (P.start i) (P.finish i)).Nil
    · have htail : pathAfterStart (L.path i) = ∅ :=
        pathAfterStart_eq_empty_of_nil (L.path i) hnil
      change (G.induce (N.branch i ∪ pathAfterStart (L.path i))).Connected
      rw [htail, Set.union_empty]
      exact N.connected i
    · have hfinish : P.finish i ∈ pathAfterStart (L.path i) := by
        rw [pathAfterStart_eq_tail_support (L.path i) hnil]
        rw [(L.path i : G.Walk (P.start i) (P.finish i)).support_tail_of_not_nil hnil]
        exact (L.path i : G.Walk (P.start i) (P.finish i)).end_mem_tail_support hnil
      exact G.connected_induce_union
        (N.connected i).preconnected
        (pathAfterStart_connected (L.path i) hnil).preconnected
        hy hfinish hxy.symm
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    rcases hxi with hxi | hxi
    · rcases hxj with hxj | hxj
      · exact (Set.disjoint_left.mp (N.disjoint hij)) hxi hxj
      · exact (Set.disjoint_left.mp (havoid i j)) hxi (htailPath j hxj)
    · rcases hxj with hxj | hxj
      · exact (Set.disjoint_left.mp (havoid j i)) hxj (htailPath i hxi)
      · exact (Set.disjoint_left.mp (L.disjoint hij))
          (htailPath i hxi) (htailPath j hxj)
  · intro i j hx
    rcases hx with hx | hx
    · exact (Set.disjoint_left.mp (havoid i j)) hx
        (pathVertexSet.start_mem (L.path j))
    · have hpath : P.start j ∈ pathVertexSet (L.path i) :=
        htailPath i hx
      by_cases hij : i = j
      · subst j
        exact start_not_mem_pathAfterStart (L.path i) hx
      · exact (Set.disjoint_left.mp (L.disjoint hij)) hpath
          (pathVertexSet.start_mem (L.path j))
  · intro i j hij
    obtain ⟨x, hx, y, hy, hxy⟩ := N.adjacent hij
    exact ⟨x, Or.inl hx, y, Or.inl hy, hxy⟩
  · intro i
    by_cases hnil : (L.path i : G.Walk (P.start i) (P.finish i)).Nil
    · obtain ⟨y, hy, hxy⟩ := hattach i
      have heq : P.start i = P.finish i := hnil.eq
      exact ⟨y, Or.inl hy, heq ▸ hxy⟩
    · let w : G.Walk (P.start i) (P.finish i) := L.path i
      refine ⟨w.snd, Or.inr ?_, w.adj_snd hnil⟩
      rw [pathAfterStart_eq_tail_support (L.path i) hnil]
      rw [w.support_tail_of_not_nil hnil]
      exact w.snd_mem_tail_support hnil
end RootAttachedCliqueModel

/-- Splice a far-side attached clique model to the original roots along
disjoint paths ending at every boundary vertex of a separation. -/
noncomputable def spliceAcrossSeparation
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : VertexSeparation G) {r : ℕ}
    {P : IndexedPairs (Fin r) V} (L : IndexedLinkage G P)
    (xroot : Fin r → S.right)
    (hfinish : ∀ i, P.finish i = (xroot i).1)
    (hboundary : ∀ x ∈ S.separatorFinset, ∃ i, P.finish i = x)
    (hleft : ∀ i, pathVertexSet (L.path i) ⊆ S.left)
    (A : RootAttachedCliqueModel (G.induce S.right) xroot) :
    RootAttachedCliqueModel G P.start := by
  let N : MinorModel (SimpleGraph.completeGraph (Fin r)) G :=
    A.toMinorModel.map (SimpleGraph.Embedding.induce S.right).toHom
      Subtype.coe_injective
  have hNstrict : ∀ i, N.branch i ⊆ S.strictRight := by
    intro i v hv
    obtain ⟨w, hw, rfl⟩ := hv
    refine ⟨w.property, ?_⟩
    intro hwl
    have hwX : (w : V) ∈ S.separatorFinset :=
      (S.mem_separatorFinset w).mpr ⟨hwl, w.property⟩
    obtain ⟨j, hj⟩ := hboundary w hwX
    have hroot : w = xroot j := by
      apply Subtype.ext
      exact hj.symm.trans (hfinish j)
    exact A.avoids_roots i j (hroot ▸ hw)
  apply RootAttachedCliqueModel.extendAlongLinkage L N
  · intro i j
    apply Set.disjoint_left.mpr
    intro v hv hp
    exact (hNstrict i hv).2 (hleft j hp)
  · intro i
    obtain ⟨w, hw, hadj⟩ := A.attached i
    refine ⟨(w : V), ⟨w, hw, rfl⟩, ?_⟩
    rw [hfinish i]
    exact hadj
end HadwigerLean
