import HadwigerLean.Graph.Linkedness.TorsoIncidence
import HadwigerLean.Graph.Linkedness.FirstHit

/-! Trim torso paths before and after their adhesion visits. -/

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A torso path meeting the completed adhesion in at most one vertex uses no artificial edge. -/
theorem torso_path_transfer_of_unique_boundary
    (G : SimpleGraph V) (S : VertexSeparation G)
    {s t z : S.left} (p : (torsoGraph G S).Path s t)
    (hunique : ∀ u ∈ pathVertexSet p,
      (u : V) ∈ S.right → u = z) :
    ∃ q : (G.induce S.left).Path s t,
      pathVertexSet q = pathVertexSet p := by
  let K := torsoGraph G S
  let w : K.Walk s t := p
  have hedge : ∀ e ∈ w.edges, e ∈ (G.induce S.left).edgeSet := by
    intro e he
    have heK : e ∈ K.edgeSet := w.edges_subset_edgeSet he
    induction e using Sym2.ind with | h u v =>
      have huv : K.Adj u v := K.mem_edgeSet.mp heK
      rcases huv with hG | ⟨huZ,hvZ,huv⟩
      · exact (G.induce S.left).mem_edgeSet.mpr hG
      · have huP : u ∈ pathVertexSet p := w.fst_mem_support_of_mem_edges he
        have hvP : v ∈ pathVertexSet p := w.snd_mem_support_of_mem_edges he
        exact False.elim (huv ((hunique u huP huZ).trans (hunique v hvP hvZ).symm))
  let q : (G.induce S.left).Path s t :=
    ⟨w.transfer (G.induce S.left) hedge, p.property.transfer hedge⟩
  exact ⟨q, by ext x; simp [q, pathVertexSet, SimpleGraph.Walk.support_transfer]; rfl⟩

/-- The adhesion vertices, represented as a finite set in the torso. -/
noncomputable def torsoBoundaryFinset (G : SimpleGraph V)
    (S : VertexSeparation G) : Finset S.left := by
  classical
  letI : Fintype S.left := Fintype.ofFinite S.left
  exact Finset.univ.filter (fun u : S.left => (u : V) ∈ S.right)

@[simp] theorem mem_torsoBoundaryFinset (G : SimpleGraph V)
    (S : VertexSeparation G) (u : S.left) :
    u ∈ torsoBoundaryFinset G S ↔ (u : V) ∈ S.right := by
  simp [torsoBoundaryFinset]

/-- Choose a first hit whenever a path meets the target set. -/
theorem FirstHit.exists_of_support_hit
    {W : Type*} [DecidableEq W] {H : SimpleGraph W} {s t : W}
    (p : H.Path s t) (J : Finset W)
    (hhit : ∃ x, x ∈ J ∧ x ∈ pathVertexSet p) :
    Nonempty (FirstHit p J) := by
  let w : H.Walk s t := p
  have hhit' : {x ∈ J | x ∈ w.support}.Nonempty := by
    obtain ⟨x,hxJ,hxP⟩ := hhit
    exact ⟨x, Finset.mem_filter.mpr ⟨hxJ,hxP⟩⟩
  obtain ⟨u,huJ,huW,hfirst⟩ :=
    w.exists_mem_support_forall_mem_support_imp_eq J hhit'
  let q : H.Path s u := ⟨w.takeUntil u huW, p.property.takeUntil huW⟩
  exact ⟨{
    finish := u
    finish_mem := huJ
    path := q
    path_subset := by
      intro x hx
      exact w.support_takeUntil_subset_support huW hx
    unique_hit := by
      intro x hx hxJ
      exact hfirst x hxJ hx
  }⟩

/-- The two outer pieces of a torso path are genuine near-side paths. -/
structure TorsoPathEnds (G : SimpleGraph V) (S : VertexSeparation G)
    {s t : S.left} (p : (torsoGraph G S).Path s t) where
  first : S.left
  last : S.left
  first_mem : (first : V) ∈ S.right
  last_mem : (last : V) ∈ S.right
  prefixPath : (G.induce S.left).Path s first
  suffixPath : (G.induce S.left).Path last t
  prefix_subset : pathVertexSet prefixPath ⊆ pathVertexSet p
  suffix_subset : pathVertexSet suffixPath ⊆ pathVertexSet p
  prefix_unique : ∀ x ∈ pathVertexSet prefixPath,
    (x : V) ∈ S.right → x = first
  suffix_unique : ∀ x ∈ pathVertexSet suffixPath,
    (x : V) ∈ S.right → x = last

/-- Trim from both endpoints at the first encounter with the adhesion. -/
theorem TorsoPathEnds.exists_of_boundary_hit
    (G : SimpleGraph V) (S : VertexSeparation G)
    {s t : S.left} (p : (torsoGraph G S).Path s t)
    (hhit : ∃ x, x ∈ pathVertexSet p ∧ (x : V) ∈ S.right) :
    Nonempty (TorsoPathEnds G S p) := by
  classical
  let J := torsoBoundaryFinset G S
  have hhitJ : ∃ x, x ∈ J ∧ x ∈ pathVertexSet p := by
    obtain ⟨x,hxP,hxZ⟩ := hhit
    exact ⟨x, (mem_torsoBoundaryFinset G S x).mpr hxZ, hxP⟩
  let F : FirstHit p J := Classical.choice (FirstHit.exists_of_support_hit p J hhitJ)
  have hhitRev : ∃ x, x ∈ J ∧ x ∈ pathVertexSet p.reverse := by
    obtain ⟨x,hxJ,hxP⟩ := hhitJ
    exact ⟨x,hxJ,by simpa [pathVertexSet, SimpleGraph.Path.reverse,
      SimpleGraph.Walk.support_reverse] using hxP⟩
  let B : FirstHit p.reverse J :=
    Classical.choice (FirstHit.exists_of_support_hit p.reverse J hhitRev)
  have hFunique : ∀ x ∈ pathVertexSet F.path,
      (x : V) ∈ S.right → x = F.finish := by
    intro x hx hxZ
    exact F.unique_hit x hx ((mem_torsoBoundaryFinset G S x).mpr hxZ)
  have hBunique : ∀ x ∈ pathVertexSet B.path,
      (x : V) ∈ S.right → x = B.finish := by
    intro x hx hxZ
    exact B.unique_hit x hx ((mem_torsoBoundaryFinset G S x).mpr hxZ)
  obtain ⟨qF,hqF⟩ := torso_path_transfer_of_unique_boundary G S F.path hFunique
  obtain ⟨qB,hqB⟩ := torso_path_transfer_of_unique_boundary G S B.path hBunique
  have hrev (q : (torsoGraph G S).Path t s) (x : S.left) :
      x ∈ pathVertexSet q.reverse ↔ x ∈ pathVertexSet q := by
    simp [pathVertexSet, SimpleGraph.Path.reverse, SimpleGraph.Walk.support_reverse]
  have hrevG (q : (G.induce S.left).Path t B.finish) (x : S.left) :
      x ∈ pathVertexSet q.reverse ↔ x ∈ pathVertexSet q := by
    simp [pathVertexSet, SimpleGraph.Path.reverse, SimpleGraph.Walk.support_reverse]
  exact ⟨{
    first := F.finish
    last := B.finish
    first_mem := (mem_torsoBoundaryFinset G S F.finish).mp F.finish_mem
    last_mem := (mem_torsoBoundaryFinset G S B.finish).mp B.finish_mem
    prefixPath := qF
    suffixPath := qB.reverse
    prefix_subset := by
      intro x hx
      exact F.path_subset (hqF ▸ hx)
    suffix_subset := by
      intro x hx
      have hxB : x ∈ pathVertexSet B.path := hqB ▸ (hrevG qB x).mp hx
      have hxpR : x ∈ pathVertexSet p.reverse := B.path_subset hxB
      simpa [pathVertexSet, SimpleGraph.Path.reverse,
        SimpleGraph.Walk.support_reverse] using hxpR
    prefix_unique := by
      intro x hx hxZ
      exact hFunique x (hqF ▸ hx) hxZ
    suffix_unique := by
      intro x hx hxZ
      exact hBunique x (hqB ▸ (hrevG qB x).mp hx) hxZ
  }⟩
/-- The selected first adhesion vertex lies on the original torso path. -/
theorem TorsoPathEnds.first_mem_path
    (G : SimpleGraph V) (S : VertexSeparation G)
    {s t : S.left} {p : (torsoGraph G S).Path s t}
    (E : TorsoPathEnds G S p) : E.first ∈ pathVertexSet p :=
  E.prefix_subset (pathVertexSet.finish_mem E.prefixPath)

/-- The selected last adhesion vertex lies on the original torso path. -/
theorem TorsoPathEnds.last_mem_path
    (G : SimpleGraph V) (S : VertexSeparation G)
    {s t : S.left} {p : (torsoGraph G S).Path s t}
    (E : TorsoPathEnds G S p) : E.last ∈ pathVertexSet p :=
  E.suffix_subset (pathVertexSet.start_mem E.suffixPath)

/-- A torso path missing the adhesion transfers unchanged to the near-side graph. -/
theorem torso_path_transfer_of_no_boundary
    (G : SimpleGraph V) (S : VertexSeparation G)
    {s t : S.left} (p : (torsoGraph G S).Path s t)
    (hno : ¬ ∃ x, x ∈ pathVertexSet p ∧ (x : V) ∈ S.right) :
    ∃ q : (G.induce S.left).Path s t,
      pathVertexSet q = pathVertexSet p := by
  apply torso_path_transfer_of_unique_boundary G S (z := s) p
  intro u hu huZ
  exact False.elim (hno ⟨u,hu,huZ⟩)
end Linkedness
end HadwigerLean
