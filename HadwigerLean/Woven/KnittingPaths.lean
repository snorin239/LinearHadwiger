import HadwigerLean.Woven.KnittingProxy
import HadwigerLean.Woven.ThreeChildLinkage

/-!
# Paths for a finite family of repeated-endpoint knitting edges

Each desired edge between specified vertices receives two distinct
neighbor proxies outside the specified set. Quantitative linkedness after
deleting the specified vertices joins the proxy pairs by disjoint paths.
-/

namespace HadwigerLean
namespace Woven

variable {V ι : Type*} [Fintype V] [DecidableEq V]
  [Fintype ι] [DecidableEq ι]
private theorem linkage_vertices_cast {G : SimpleGraph V}
    {P Q : IndexedPairs ι V} (h : P = Q)
    (L : IndexedLinkage G P) :
    (h ▸ L).vertices = L.vertices := by
  cases h
  rfl

/-- `33p`-connectivity simultaneously routes at most `p` prescribed
terminal pairs, even when the original terminal vertices repeat across
pairs. The proxy paths avoid every original specified vertex. -/
theorem exists_knitting_proxy_linkage
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : ℕ) (X : Finset V)
    (hX : X.card ≤ p)
    (edgeStart edgeFinish : ι → V)
    (hstartX : ∀ i, edgeStart i ∈ X)
    (hfinishX : ∀ i, edgeFinish i ∈ X)
    (hI : Fintype.card ι ≤ p)
    (hconn : VertexConnected G (33 * p)) :
    ∃ (proxy : ι × Fin 2 → V)
      (L : IndexedLinkage G
        ⟨fun i => proxy (i,0), fun i => proxy (i,1)⟩),
      Function.Injective proxy ∧
      (∀ i, G.Adj (edgeStart i) (proxy (i,0))) ∧
      (∀ i, G.Adj (edgeFinish i) (proxy (i,1))) ∧
      (∀ i b, proxy (i,b) ∉ X) ∧
      (∀ v, v ∈ L.vertices → v ∉ X) := by
  classical
  let role : ι × Fin 2 → V :=
    fun slot => if slot.2 = 0 then edgeStart slot.1
      else edgeFinish slot.1
  have hdegree (slot : ι × Fin 2) :
      X.card + Fintype.card (ι × Fin 2) ≤ G.degree (role slot) := by
    have hdeg := Linkedness.degree_ge_of_vertexConnected hconn (role slot)
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  obtain ⟨proxy,hproxyinj,hadj,houtside⟩ :=
    exists_injective_neighbor_proxies_finite G role X hdegree
  let D : Set V := (X : Set V)ᶜ
  let k := Fintype.card ι
  have hdelete : VertexConnected (G.induce D) (16 * k) := by
    apply hconn.induce_compl X (16 * k)
    omega
  have hlinked : Linkedness.KLinked (G.induce D) k :=
    Linkedness.kLinked_of_sixteen_mul_vertexConnected
      (G.induce D) k hdelete
  let e : Fin k ≃ ι := (Fintype.equivFin ι).symm
  let f : ι × Fin 2 → D := fun slot =>
    ⟨proxy slot, houtside slot⟩
  have hfinj : Function.Injective f := by
    intro s t h
    exact hproxyinj (congrArg Subtype.val h)
  let P' : IndexedPairs (Fin k) D :=
    ⟨fun i => f (e i,0), fun i => f (e i,1)⟩
  have hP'start : Function.Injective P'.start := by
    intro i j h
    exact e.injective (congrArg Prod.fst (hfinj h))
  have hP'finish : Function.Injective P'.finish := by
    intro i j h
    exact e.injective (congrArg Prod.fst (hfinj h))
  have hP'st : Disjoint (Set.range P'.start) (Set.range P'.finish) := by
    apply Set.disjoint_left.mpr
    intro v hvS hvT
    obtain ⟨i,hi⟩ := hvS
    obtain ⟨j,hj⟩ := hvT
    have heq : (e i, (0 : Fin 2)) = (e j, (1 : Fin 2)) :=
      hfinj (hi.trans hj.symm)
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.snd heq)
  have hP'dis : P'.DisjointTerminals :=
    disjointTerminals_of_injective_ends P'
      hP'start hP'finish hP'st
  have hP'ne (i : Fin k) : P'.start i ≠ P'.finish i := by
    intro h
    exact (Set.disjoint_left.mp hP'st) ⟨i,rfl⟩ ⟨i,h.symm⟩
  obtain ⟨L'⟩ := hlinked P' hP'dis hP'ne
  let L₁ := L'.mapInduce
  let Q : IndexedPairs ι V :=
    ⟨fun i => proxy (i,0), fun i => proxy (i,1)⟩
  let P₀ : IndexedPairs ι V :=
    ⟨fun i => (P'.start (e.symm i) : V),
      fun i => (P'.finish (e.symm i) : V)⟩
  have hPQ : P₀ = Q := by
    have hs : P₀.start = Q.start := by
      funext i
      change proxy (e (e.symm i),0) = proxy (i,0)
      rw [e.apply_symm_apply]
    have ht : P₀.finish = Q.finish := by
      funext i
      change proxy (e (e.symm i),1) = proxy (i,1)
      rw [e.apply_symm_apply]
    cases e₁ : P₀ with
    | mk s t =>
      cases e₂ : Q with
      | mk s' t' =>
        have hs' : s = s' := by simpa [e₁,e₂] using hs
        have ht' : t = t' := by simpa [e₁,e₂] using ht
        cases hs'
        cases ht'
        rfl
  let L₀ : IndexedLinkage G P₀ := L₁.reindex e.symm.toEmbedding
  let L : IndexedLinkage G Q := hPQ ▸ L₀
  have hLverts : L.vertices = L₀.vertices :=
    linkage_vertices_cast hPQ L₀
  have hLavoid : ∀ v, v ∈ L.vertices → v ∉ X := by
    intro v hv
    rw [hLverts] at hv
    have hv₁ : v ∈ L₁.vertices := by
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hv
      exact Set.mem_iUnion.mpr ⟨e.symm i, hi⟩
    exact IndexedLinkage.mapInduce_vertices_subset L' hv₁
  refine ⟨proxy,L,hproxyinj,?_,?_,?_,hLavoid⟩
  · intro i
    simpa [role] using hadj (i,0)
  · intro i
    simpa [role] using hadj (i,1)
  · intro i b
    exact houtside (i,b)

end Woven
end HadwigerLean




