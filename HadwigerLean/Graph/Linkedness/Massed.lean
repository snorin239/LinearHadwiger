import HadwigerLean.Graph.MassedPair
import HadwigerLean.Graph.SetMengerTheorem
import HadwigerLean.Graph.TouchingQuotient
import HadwigerLean.Graph.ContractionEdges
import HadwigerLean.Graph.EdgeIncidenceMono

/-!
# Rooted linkedness and massed pairs

A rooted linkage connects prescribed distinct pairs of roots by disjoint
paths whose interior avoids the entire root set. This is the stronger rooted
form of linkedness used in Appendix D of the proof manuscript.
-/

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All prescribed path interiors avoid the root set. -/
def InteriorsAvoid {G : SimpleGraph V} {ι : Type*}
    {P : IndexedPairs ι V} (L : IndexedLinkage G P) (X : Finset V) : Prop :=
  ∀ i v, v ∈ pathVertexSet (L.path i) → v ∈ X → v ∈ P.terminals i

/-- Every pairing of an even subset of `X` has a disjoint linkage whose
interiors avoid all of `X`. -/
def RootedLinked (G : SimpleGraph V) (X : Finset V) : Prop :=
  ∀ n (P : IndexedPairs (Fin n) V), P.DisjointTerminals →
    (∀ i, P.start i ≠ P.finish i) →
    (∀ i, P.terminals i ⊆ (X : Set V)) →
      ∃ L : IndexedLinkage G P, InteriorsAvoid L X

/-- A linkage in a subgraph remains a linkage after adding edges. -/
def IndexedLinkage.mono_graph {ι : Type*} {G H : SimpleGraph V}
    {P : IndexedPairs ι V} (hGH : G ≤ H) (L : IndexedLinkage G P) :
    IndexedLinkage H P where
  path := fun i => SimpleGraph.Path.map (.ofLE hGH) Function.injective_id (L.path i)
  disjoint := by
    intro i j hij
    simpa only [pathVertexSet, SimpleGraph.Path.map, SimpleGraph.Walk.support_mapLe_eq_support]
      using L.disjoint hij

/-- Adding edges does not alter the vertices of existing linkage paths. -/
theorem InteriorsAvoid.mono_graph {ι : Type*} {G H : SimpleGraph V}
    {P : IndexedPairs ι V} (hGH : G ≤ H) (L : IndexedLinkage G P)
    (X : Finset V) (hL : InteriorsAvoid L X) :
    InteriorsAvoid (IndexedLinkage.mono_graph hGH L) X := by
  intro i v hv hroot
  exact hL i v (by
    simpa only [IndexedLinkage.mono_graph, pathVertexSet, SimpleGraph.Path.map,
      SimpleGraph.Walk.support_mapLe_eq_support] using hv) hroot

/-- Rooted linkedness is monotone under graph edge addition. -/
theorem RootedLinked.mono_graph {G H : SimpleGraph V}
    (hGH : G ≤ H) (X : Finset V) (hG : RootedLinked G X) :
    RootedLinked H X := by
  intro n P hP hne hX
  obtain ⟨L,hL⟩ := hG n P hP hne hX
  exact ⟨IndexedLinkage.mono_graph hGH L, InteriorsAvoid.mono_graph hGH L X hL⟩
/-- Rooted linkedness of an induced graph transfers to the ambient graph when all roots lie inside the induced set. -/
theorem RootedLinked.of_induce (G : SimpleGraph V)
    (S : Set V) (X : Finset V) (Y : Finset S)
    (hXS : (X : Set V) ⊆ S)
    (hY : ∀ u : S, u ∈ Y ↔ (u : V) ∈ X)
    (h : RootedLinked (G.induce S) Y) :
    RootedLinked G X := by
  classical
  intro n P hP hne hPX
  let P' : IndexedPairs (Fin n) S := {
    start := fun i => ⟨P.start i, hXS (hPX i (by simp [IndexedPairs.terminals]))⟩
    finish := fun i => ⟨P.finish i, hXS (hPX i (by simp [IndexedPairs.terminals]))⟩
  }
  have hterm_iff (i : Fin n) (u : S) :
      u ∈ P'.terminals i ↔ (u : V) ∈ P.terminals i := by
    simp only [IndexedPairs.terminals, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (hu | hu)
      · left
        simpa [P'] using congrArg Subtype.val hu
      · right
        simpa [P'] using congrArg Subtype.val hu
    · rintro (hu | hu)
      · left
        apply Subtype.ext
        simpa [P'] using hu
      · right
        apply Subtype.ext
        simpa [P'] using hu
  have hP' : P'.DisjointTerminals := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro u hui huj
    exact (Set.disjoint_left.mp (hP hij))
      ((hterm_iff i u).mp hui) ((hterm_iff j u).mp huj)
  have hne' : ∀ i, P'.start i ≠ P'.finish i := by
    intro i heq
    exact hne i (congrArg Subtype.val heq)
  have hPY : ∀ i, P'.terminals i ⊆ (Y : Set S) := by
    intro i u hu
    exact (hY u).mpr (hPX i ((hterm_iff i u).mp hu))
  obtain ⟨L',hL'⟩ := h n P' hP' hne' hPY
  let e : (G.induce S).Embedding G := SimpleGraph.Embedding.induce S
  let q (i : Fin n) : G.Path (P.start i) (P.finish i) :=
    (L'.path i).mapEmbedding e
  have hsupport (i : Fin n) (v : V) :
      v ∈ pathVertexSet (q i) ↔
        ∃ u : S, u ∈ pathVertexSet (L'.path i) ∧ (u : V) = v := by
    change v ∈ ((L'.path i : (G.induce S).Walk (P'.start i) (P'.finish i)).map e.toHom).support ↔
      ∃ u : S, u ∈ (L'.path i : (G.induce S).Walk (P'.start i) (P'.finish i)).support ∧
        (u : V) = v
    rw [SimpleGraph.Walk.support_map]
    simp only [List.mem_map]
    constructor
    · rintro ⟨u, hu, huv⟩
      exact ⟨u, hu, huv⟩
    · rintro ⟨u, hu, huv⟩
      exact ⟨u, hu, huv⟩
  let L : IndexedLinkage G P := {
    path := q
    disjoint := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro v hvi hvj
      obtain ⟨u, hu, hval⟩ := (hsupport i v).mp hvi
      obtain ⟨w, hw, hval'⟩ := (hsupport j v).mp hvj
      have huw : u = w := Subtype.val_injective (hval.trans hval'.symm)
      subst w
      exact (Set.disjoint_left.mp (L'.disjoint hij)) hu hw
  }
  refine ⟨L, ?_⟩
  intro i v hv hvX
  obtain ⟨u,hu,hval⟩ := (hsupport i v).mp hv
  have huY : u ∈ Y := (hY u).mpr (hval ▸ hvX)
  have hterm := hL' i u hu huY
  have hterm' : (u : V) ∈ P.terminals i := (hterm_iff i u).mp hterm
  simpa [hval] using hterm'

/-- A rooted linkage path never traverses an edge joining another prescribed pair of roots. -/
theorem InteriorsAvoid.other_root_edge_not_used
    {G : SimpleGraph V} {ι : Type*} {P : IndexedPairs ι V}
    (L : IndexedLinkage G P) (X : Finset V) (hL : InteriorsAvoid L X)
    (i : ι) (u v : V) (huX : u ∈ X) (hvX : v ∈ X)
    (huv : u ≠ v)
    (hother : s(u,v) ≠ s(P.start i,P.finish i)) :
    s(u,v) ∉ (L.path i : G.Walk (P.start i) (P.finish i)).edges := by
  intro he
  let p : G.Walk (P.start i) (P.finish i) := L.path i
  change s(u,v) ∈ p.edges at he
  have huS : u ∈ pathVertexSet (L.path i) := by
    change u ∈ (L.path i : G.Walk (P.start i) (P.finish i)).support
    exact p.fst_mem_support_of_mem_edges he
  have hvS : v ∈ pathVertexSet (L.path i) := by
    change v ∈ (L.path i : G.Walk (P.start i) (P.finish i)).support
    exact p.snd_mem_support_of_mem_edges he
  have hu := hL i u huS huX
  have hv := hL i v hvS hvX
  simp only [IndexedPairs.terminals, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact huv (hu.trans hv.symm)
  · exact hother (by rw [hu,hv])
  · exact hother (by rw [hu,hv,Sym2.eq_swap])
  · exact huv (hu.trans hv.symm)
/-- A rooted linkage transfers to a graph missing one root edge when that edge is not a prescribed pair and all other edges remain. -/
theorem InteriorsAvoid.transfer_avoiding_root_edge
    {G H : SimpleGraph V} {ι : Type*} {P : IndexedPairs ι V}
    (L : IndexedLinkage H P) (X : Finset V) (hL : InteriorsAvoid L X)
    (u v : V) (huX : u ∈ X) (hvX : v ∈ X) (huv : u ≠ v)
    (hother : ∀ i, s(u,v) ≠ s(P.start i,P.finish i))
    (hHG : ∀ e ∈ H.edgeSet, e ≠ s(u,v) → e ∈ G.edgeSet) :
    ∃ L' : IndexedLinkage G P, InteriorsAvoid L' X := by
  have hedge (i : ι) : ∀ e, e ∈ (L.path i : H.Walk (P.start i) (P.finish i)).edges →
      e ∈ G.edgeSet := by
    intro e he
    let p : H.Walk (P.start i) (P.finish i) := L.path i
    change e ∈ p.edges at he
    have heH : e ∈ H.edgeSet := p.edges_subset_edgeSet he
    by_cases heq : e = s(u,v)
    · subst e
      exact False.elim ((hL.other_root_edge_not_used L X i u v huX hvX huv (hother i)) he)
    · exact hHG e heH heq
  let q (i : ι) : G.Path (P.start i) (P.finish i) :=
    ⟨(L.path i : H.Walk (P.start i) (P.finish i)).transfer G (hedge i),
      (L.path i).property.transfer (hedge i)⟩
  have hvertex (i : ι) : pathVertexSet (q i) = pathVertexSet (L.path i) := by
    ext x
    simp [q, pathVertexSet, SimpleGraph.Walk.support_transfer]
  let L' : IndexedLinkage G P := {
    path := q
    disjoint := by
      intro i j hij
      simpa only [hvertex] using L.disjoint hij
  }
  refine ⟨L', ?_⟩
  intro i x hx hroot
  apply hL i x
  · simpa only [L', hvertex] using hx
  · exact hroot
/-- Standard linkedness for `k` prescribed, disjoint, nontrivial pairs. -/
def KLinked (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ P : IndexedPairs (Fin k) V, P.DisjointTerminals →
    (∀ i, P.start i ≠ P.finish i) → Nonempty (IndexedLinkage G P)

/-- The set of terminals of all prescribed pairs. -/
noncomputable def terminalFinset {ι : Type*} [Fintype ι]
    (P : IndexedPairs ι V) : Finset V := by
  classical
  exact (Finset.univ.image P.start) ∪ (Finset.univ.image P.finish)

@[simp] theorem mem_terminalFinset {ι : Type*} [Fintype ι]
    (P : IndexedPairs ι V) (v : V) :
    v ∈ terminalFinset P ↔ (∃ i, P.start i = v) ∨ (∃ i, P.finish i = v) := by
  classical
  simp [terminalFinset]

theorem terminals_subset_terminalFinset {ι : Type*} [Fintype ι]
    (P : IndexedPairs ι V) (i : ι) :
    P.terminals i ⊆ (terminalFinset P : Set V) := by
  intro v hv
  rcases hv with rfl | rfl
  · exact (mem_terminalFinset P _).mpr (Or.inl ⟨i, rfl⟩)
  · exact (mem_terminalFinset P _).mpr (Or.inr ⟨i, rfl⟩)

theorem terminalFinset_card_le {ι : Type*} [Fintype ι]
    (P : IndexedPairs ι V) :
    (terminalFinset P).card ≤ 2 * Fintype.card ι := by
  classical
  calc
    (terminalFinset P).card ≤
        (Finset.univ.image P.start).card +
          (Finset.univ.image P.finish).card := by
            exact Finset.card_union_le _ _
    _ ≤ Fintype.card ι + Fintype.card ι := by
          have h1 := Finset.card_image_le (s := (Finset.univ : Finset ι))
            (f := P.start)
          have h2 := Finset.card_image_le (s := (Finset.univ : Finset ι))
            (f := P.finish)
          simpa using Nat.add_le_add h1 h2
    _ = 2 * Fintype.card ι := by omega

/-- A family of `k` disjoint nontrivial terminal pairs uses exactly `2k`
distinct vertices. -/
theorem terminalFinset_card_eq_two_mul (k : ℕ)
    (P : IndexedPairs (Fin k) V) (hP : P.DisjointTerminals)
    (hne : ∀ i, P.start i ≠ P.finish i) :
    (terminalFinset P).card = 2 * k := by
  classical
  have hdis : Disjoint (Finset.univ.image P.start)
      (Finset.univ.image P.finish) := by
    apply Finset.disjoint_left.mpr
    intro v hvstart hvfinish
    obtain ⟨i, -, hiv⟩ := Finset.mem_image.mp hvstart
    obtain ⟨j, -, hjv⟩ := Finset.mem_image.mp hvfinish
    have heq : P.start i = P.finish j := hiv.trans hjv.symm
    by_cases hij : i = j
    · subst j
      exact hne i heq
    · have ha : P.start i ∈ P.terminals i := by
        simp [IndexedPairs.terminals]
      have hb : P.start i ∈ P.terminals j := by
        simp [IndexedPairs.terminals, heq]
      exact (Set.disjoint_left.mp (hP hij)) ha hb
  unfold terminalFinset
  rw [Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injective _ (IndexedPairs.start_injective hP),
    Finset.card_image_of_injective _ (IndexedPairs.finish_injective hP)]
  simp
  omega
/-- Uniform rooted linkedness for all root sets of size at most `2k`
implies ordinary `k`-linkedness. -/
theorem kLinked_of_rootedLinked (G : SimpleGraph V) (k : ℕ)
    (h : ∀ X : Finset V, X.card ≤ 2 * k → RootedLinked G X) :
    KLinked G k := by
  intro P hP hne
  let X := terminalFinset P
  obtain ⟨L, _⟩ := h X (by simpa [X] using terminalFinset_card_le P)
    k P hP hne (terminals_subset_terminalFinset P)
  exact ⟨L⟩

/-- In a sufficiently connected graph, a separation containing the roots on
its near side and having adhesion below the number of roots has no far side. -/
theorem no_small_far_shore {G : SimpleGraph V} {r : ℕ}
    (hconn : VertexConnected G r) (X : Finset V)
    (hX : X.card ≤ r) (S : VertexSeparation G)
    (hroot : (X : Set V) ⊆ S.left)
    (hsep : S.separatorFinset.card < X.card) :
    S.strictRight = ∅ := by
  classical
  have hnot : ¬ X ⊆ S.separatorFinset := by
    intro hsubset
    have hcard := Finset.card_le_card hsubset
    omega
  have hex : ∃ x ∈ X, x ∉ S.separatorFinset := by
    simpa [Finset.subset_iff] using hnot
  obtain ⟨x, hxX, hxnot⟩ := hex
  have hxleft : x ∈ S.strictLeft := by
    refine ⟨hroot hxX, ?_⟩
    intro hright
    exact hxnot ((S.mem_separatorFinset x).mpr ⟨hroot hxX, hright⟩)
  ext y
  constructor
  · intro hy
    exfalso
    have hsmall : S.separatorFinset.card < r := lt_of_lt_of_le hsep hX
    exact (S.not_two_strict_sides hconn hsmall) ⟨⟨x, hxleft⟩, ⟨y, hy⟩⟩
  · intro hy
    exact False.elim hy
/-- Vertex connectivity makes the massed-pair shore condition automatic;
only the global incidence inequality remains to be verified. -/
theorem massed_of_vertexConnected_and_global {G : SimpleGraph V}
    (X : Finset V) (r : ℕ) (α : ℝ)
    (hconn : VertexConnected G r) (hX : X.card ≤ r)
    (hglobal : α * (Nat.card {v : V // v ∉ (X : Set V)} : ℝ) <
      (edgeIncidenceSetCount G (X : Set V)ᶜ : ℝ)) :
    MassedPair G (X : Set V) α := by
  refine ⟨hglobal, ?_⟩
  intro S hroot hsep
  have hsepFin : S.separatorFinset.card < X.card := by
    have hEq : Nat.card S.separator = S.separatorFinset.card := by
      classical
      simp [VertexSeparation.separatorFinset]
    rw [hEq] at hsep
    simpa using hsep
  have hfar := no_small_far_shore hconn X hX S hroot hsepFin
  rw [hfar]
  simp [edgeIncidenceSetCount, edgeIncidenceSet]

/-- Vertex connectivity forces the expected lower bound on every degree. -/
theorem degree_ge_of_vertexConnected {G : SimpleGraph V} [DecidableRel G.Adj]
    {r : ℕ} (hconn : VertexConnected G r) (v : V) :
    r ≤ G.degree v := by
  by_contra hdeg
  have hdeg' : G.degree v < r := by omega
  let U := G.neighborFinset v
  let W : Set V := (U : Set V)ᶜ
  have hU : U.card = G.degree v := G.card_neighborFinset_eq_degree v
  have hvU : v ∉ U := G.notMem_neighborFinset_self v
  have hcardC : Fintype.card W = (Uᶜ : Finset V).card := by
    apply Fintype.card_of_finset' (Uᶜ)
    intro x
    simp [W]
  have hsum : Fintype.card W + U.card = Fintype.card V := by
    rw [hcardC]
    exact Finset.card_compl_add_card U
  have htwo : 1 < Fintype.card W := by
    have := hconn.order_gt
    omega
  letI : Nontrivial W :=
    Fintype.one_lt_card_iff_nontrivial.mp htwo
  have hconnected : (G.induce W).Connected := by
    apply hconn.connected_delete U
    omega
  let vv : W := ⟨v, hvU⟩
  have hisolated : (G.induce W).IsIsolated vv := by
    intro w hadj
    have hw : (w : V) ∈ U := by
      simpa [U] using (hadj : G.Adj v (w : V))
    exact w.property hw
  exact hconnected.preconnected.not_isIsolated vv hisolated

theorem incidenceSetCount_eq_finsetCount (G : SimpleGraph V)
    (S : Finset V) :
    edgeIncidenceSetCount G (S : Set V) = edgeIncidenceCount G S := by
  classical
  let F : Finset G.edgeSet := Finset.univ.filter
    (fun e => ∃ v ∈ S, v ∈ (e.1 : Sym2 V))
  have himage : F.image (fun e : G.edgeSet => (e.1 : Sym2 V)) =
      G.edgeFinset.filter (fun e => ∃ v ∈ S, v ∈ e) := by
    ext e
    simp [F, SimpleGraph.mem_edgeFinset, and_comm]
  have hinj : Function.Injective (fun e : G.edgeSet => (e.1 : Sym2 V)) :=
    Subtype.val_injective
  have hcard : F.card = (G.edgeFinset.filter (fun e => ∃ v ∈ S, v ∈ e)).card := by
    rw [← himage, Finset.card_image_of_injective _ hinj]
  calc
    edgeIncidenceSetCount G (S : Set V) =
        Nat.card {e : G.edgeSet // ∃ v ∈ S, v ∈ (e.1 : Sym2 V)} := by
          simpa [edgeIncidenceSetCount, edgeIncidenceSet] using
            (Fintype.card_subtype (p := fun e : G.edgeSet => ∃ v ∈ S, v ∈ (e.1 : Sym2 V))).symm
    _ = F.card := by
          rw [Nat.card_eq_fintype_card]
          apply Fintype.card_ofFinset F

    _ = edgeIncidenceCount G S := by
          have hsame :
              (G.edgeFinset.filter (fun e => ∃ v ∈ S, v ∈ e)).card =
                edgeIncidenceCount G S := by
            unfold edgeIncidenceCount
            congr 1
            ext e
            simp [SimpleGraph.mem_edgeFinset]
          exact hcard.trans hsame

/-- Handshaking turns a uniform degree bound into an edge-count bound. -/
theorem edgeCount_lower_of_minDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (hdeg : ∀ v, 2 * r ≤ G.degree v) :
    r * Fintype.card V ≤ edgeCount G := by
  have hsum : (∑ _v : V, 2 * r) ≤ ∑ v : V, G.degree v := by
    apply Finset.sum_le_sum
    intro v hv
    exact hdeg v
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [sum_degree_eq_two_edgeCount] at hsum
  nlinarith


/-- Every edge either meets the complement of `X` or lies inside `X`. -/
theorem edgeCount_le_incidence_add_internal (G : SimpleGraph V) (X : Finset V) :
    edgeCount G ≤ edgeIncidenceCount G Xᶜ + (X.card + 1).choose 2 := by
  classical
  let q : Sym2 V → Prop := fun e => ∃ v ∈ Xᶜ, v ∈ e
  let J := G.edgeFinset.filter (fun e => ¬ q e)
  have hJ : J.card ≤ X.sym2.card := by
    apply Finset.card_le_card
    intro e he
    simp only [J, Finset.mem_filter] at he
    rw [Finset.mem_sym2_iff]
    intro v hve
    by_contra hvX
    exact he.2 ⟨v, Finset.mem_compl.mpr hvX, hve⟩
  have hpart : edgeIncidenceCount G Xᶜ + J.card = G.edgeFinset.card := by
    simpa [edgeIncidenceCount, q, J] using
      (Finset.card_filter_add_card_filter_not (s := G.edgeFinset) q)
  rw [edgeCount_eq_card_edgeFinset, Finset.card_sym2] at *
  omega

theorem choose_two_internal_lt (k : ℕ) (hk : 0 < k) :
    (2 * k + 1).choose 2 < (8 * k) * (2 * k) := by
  rw [Nat.choose_two_right]
  have hsub : 2 * k + 1 - 1 = 2 * k := by omega
  rw [hsub]
  have hmul : (2 * k + 1) * (2 * k) = 2 * (k * (2 * k + 1)) := by ring
  rw [hmul, Nat.mul_div_cancel_left] <;> norm_num
  nlinarith
/-- The global massed-pair incidence inequality for exactly `2k` roots. -/
theorem global_incidence_of_vertexConnected (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hk : 0 < k) (hconn : VertexConnected G (16 * k))
    (X : Finset V) (hX : X.card = 2 * k) :
    ((8 * k : ℕ) : ℝ) *
        (Nat.card {v : V // v ∉ (X : Set V)} : ℝ) <
      (edgeIncidenceSetCount G (X : Set V)ᶜ : ℝ) := by
  classical
  have hdeg : ∀ v, 2 * (8 * k) ≤ G.degree v := by
    intro v
    have hv := degree_ge_of_vertexConnected hconn v
    omega
  have hE : (8 * k) * Fintype.card V ≤ edgeCount G :=
    edgeCount_lower_of_minDegree G (8 * k) hdeg
  have hupper := edgeCount_le_incidence_add_internal G X
  have hchoose : (X.card + 1).choose 2 < (8 * k) * X.card := by
    rw [hX]
    exact choose_two_internal_lt k hk
  have hsize : (Xᶜ).card + X.card = Fintype.card V :=
    Finset.card_compl_add_card X
  have hmul : (8 * k) * Fintype.card V =
      (8 * k) * (Xᶜ).card + (8 * k) * X.card := by
    rw [← hsize, mul_add]
  have hnat : (8 * k) * (Xᶜ).card < edgeIncidenceCount G Xᶜ := by
    omega
  have hsub : Nat.card {v : V // v ∉ (X : Set V)} = (Xᶜ).card := by
    rw [Nat.card_eq_fintype_card]
    apply Fintype.card_of_finset' (p := {v : V | v ∉ (X : Set V)}) (Xᶜ)
    intro v
    simp
  rw [hsub]
  have hinc : edgeIncidenceSetCount G (X : Set V)ᶜ =
      edgeIncidenceCount G Xᶜ := by
    simpa using incidenceSetCount_eq_finsetCount G Xᶜ
  rw [hinc]
  exact_mod_cast hnat

/-- A `16k`-connected graph and any `2k` roots form an `8k`-massed pair. -/
theorem massed_of_vertexConnected (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (hk : 0 < k)
    (hconn : VertexConnected G (16 * k))
    (X : Finset V) (hX : X.card = 2 * k) :
    MassedPair G (X : Set V) ((8 * k : ℕ) : ℝ) := by
  apply massed_of_vertexConnected_and_global X (16 * k)
    ((8 * k : ℕ) : ℝ) hconn
  · omega
  · exact global_incidence_of_vertexConnected G k hk hconn X hX
/-- Every root of a massed pair has a neighbor outside the root set. -/
theorem root_has_outside_neighbor (G : SimpleGraph V) (X : Finset V)
    (α : ℝ) (hm : MassedPair G (X : Set V) α)
    (x : V) (hx : x ∈ X) :
    ∃ v : V, v ∉ X ∧ G.Adj x v := by
  classical
  by_contra hnot
  have hnon : ∀ v : V, v ∉ X → ¬ G.Adj x v := by
    intro v hv hadj
    exact hnot ⟨v, hv, hadj⟩
  let S : VertexSeparation G := {
    left := (X : Set V)
    right := ({x} : Set V)ᶜ
    cover := by
      ext v
      by_cases hv : v = x
      · subst v
        simp [hx]
      · simp [hv]
    no_cross := by
      intro a b ha ha' hb hb' hab
      have hax : a = x := by simpa using ha'
      subst a
      exact hnon b hb' hab
  }
  have hsepFin : S.separatorFinset = X.erase x := by
    ext v
    simp [S, VertexSeparation.separatorFinset, VertexSeparation.separator, and_comm]
  have hsep : Nat.card S.separator < Nat.card (X : Set V) := by
    have h1 : Nat.card S.separator = S.separatorFinset.card := by
      simp [VertexSeparation.separatorFinset]
    have h2 : Nat.card (X : Set V) = X.card := by simp
    rw [h1, h2, hsepFin]
    exact Finset.card_erase_lt_of_mem hx
  have hstrict : S.strictRight = (X : Set V)ᶜ := by
    ext v
    simp only [S, VertexSeparation.strictRight, Set.mem_sdiff, Set.mem_compl_iff, Set.mem_singleton_iff, Finset.mem_coe]
    constructor
    · intro h; exact h.2
    · intro hv; exact ⟨by intro hvx; exact hv (hvx.symm ▸ hx), hv⟩
  have hshore := hm.shore S (by simp [S]) hsep
  rw [hstrict] at hshore
  exact (not_lt_of_ge hshore) hm.global

/-- Common neighbors along one edge bound a root outside degree. -/
theorem root_outdegree_of_common_neighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (x v : V) (r : ℕ)
    (hr : 0 < r) (hx : x ∈ X) (hv : v ∉ X) (hAdj : G.Adj x v)
    (hcommon : r - 1 ≤ (G.neighborFinset x ∩ G.neighborFinset v).card) :
    r + 1 ≤ ((G.neighborFinset x) \ X).card + X.card := by
  let C := G.neighborFinset x ∩ G.neighborFinset v
  have hxC : x ∉ C := by
    simp [C, G.notMem_neighborFinset_self]
  have hinside : (C ∩ X).card + 1 ≤ X.card := by
    have hsub : C ∩ X ⊆ X.erase x := by
      intro w hw
      have hwC := (Finset.mem_inter.mp hw).1
      have hwX := (Finset.mem_inter.mp hw).2
      apply Finset.mem_erase.mpr
      exact ⟨by intro heq; subst w; exact hxC hwC, hwX⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_erase_add_one hx
    omega
  have hvnotC : v ∉ C := by
    simp [C, G.notMem_neighborFinset_self]
  have hsuboutside : insert v (C \ X) ⊆ G.neighborFinset x \ X := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset x _).mpr hAdj, hv⟩
    · exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp
        (Finset.mem_sdiff.mp hw).1).1, (Finset.mem_sdiff.mp hw).2⟩
  have hvnot : v ∉ C \ X := by
    intro h
    exact hvnotC (Finset.mem_sdiff.mp h).1
  have hout : (C \ X).card + 1 ≤ (G.neighborFinset x \ X).card := by
    rw [← Finset.card_insert_of_notMem hvnot]
    exact Finset.card_le_card hsuboutside
  have hsplit := Finset.card_inter_add_card_sdiff C X
  change r - 1 ≤ C.card at hcommon
  omega

/-- The numerical root-degree estimate (D.4), assuming the edge common-neighbor bound. -/
theorem root_outdegree_ge_six_k (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (k : ℕ) (hk : 0 < k)
    (hX : X.card ≤ 2 * k)
    (hm : MassedPair G (X : Set V) ((8 * k : ℕ) : ℝ))
    (hcommon : ∀ x v : V, x ∈ X → v ∉ X → G.Adj x v →
      8 * k - 1 ≤ (G.neighborFinset x ∩ G.neighborFinset v).card)
    (x : V) (hx : x ∈ X) :
    6 * k + 1 ≤ (G.neighborFinset x \ X).card := by
  obtain ⟨v, hv, hadj⟩ := root_has_outside_neighbor G X _ hm x hx
  have hbase := root_outdegree_of_common_neighbors G X x v (8 * k)
    (by omega) hx hv hadj (hcommon x v hx hv hadj)
  omega
section Partition
variable {I : Type*} {G : SimpleGraph V}

/-- The unique block containing a vertex of a connected partition. -/
noncomputable def partitionIndex (P : ConnectedPartition G I) (x : V) : I :=
  Classical.choose (P.existsUnique_block x)

theorem partitionIndex_mem (P : ConnectedPartition G I) (x : V) :
    x ∈ P.block (partitionIndex P x) :=
  (Classical.choose_spec (P.existsUnique_block x)).1

theorem partitionIndex_eq_of_mem (P : ConnectedPartition G I)
    (x : V) (i : I) (h : x ∈ P.block i) :
    partitionIndex P x = i :=
  ((Classical.choose_spec (P.existsUnique_block x)).2 i h).symm

theorem partitionIndex_adj (P : ConnectedPartition G I)
    {x y : V} (hxy : G.Adj x y) :
    partitionIndex P x = partitionIndex P y ∨
      P.touchingQuotient.Adj (partitionIndex P x) (partitionIndex P y) := by
  by_cases hidx : partitionIndex P x = partitionIndex P y
  · exact Or.inl hidx
  · exact Or.inr ⟨hidx, x, partitionIndex_mem P x,
      y, partitionIndex_mem P y, hxy⟩

/-- Pulling a quotient separation back through the partition gives a separation. -/
def partitionPullbackSeparation (P : ConnectedPartition G I)
    (S : VertexSeparation P.touchingQuotient) : VertexSeparation G where
  left := {x | partitionIndex P x ∈ S.left}
  right := {x | partitionIndex P x ∈ S.right}
  cover := by
    ext x
    have h : partitionIndex P x ∈ S.left ∪ S.right := by
      rw [S.cover]
      trivial
    simpa using h
  no_cross := by
    intro x y hxL hxR hyR hyL hxy
    rcases partitionIndex_adj P hxy with heq | hadj
    · change partitionIndex P x ∉ S.right at hxR
      change partitionIndex P y ∈ S.right at hyR
      exact hxR (heq.symm ▸ hyR)
    · exact S.no_cross hxL hxR hyR hyL hadj

theorem partitionPullbackSeparation_separator (P : ConnectedPartition G I)
    (S : VertexSeparation P.touchingQuotient) :
    (partitionPullbackSeparation P S).separator =
      partitionIndex P ⁻¹' S.separator := by
  ext x
  rfl

end Partition

theorem edgeContraction_index_some {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) (x : V) (hxa : x ≠ a) (hxb : x ≠ b) :
    partitionIndex (edgeContractionPartition G hab) x =
      some (⟨x, hxa, hxb⟩ : EdgeOutside a b) := by
  apply partitionIndex_eq_of_mem
  simp [edgeContractionPartition, edgeContractionBlock]

theorem edgeContraction_index_inj_away {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) {x y : V}
    (hx : partitionIndex (edgeContractionPartition G hab) x ≠ none)
    (hxy : partitionIndex (edgeContractionPartition G hab) x =
      partitionIndex (edgeContractionPartition G hab) y) : x = y := by
  let P := edgeContractionPartition G hab
  cases hq : partitionIndex P x with
  | none => exact False.elim (hx hq)
  | some z =>
      have hxmem : x ∈ P.block (some z) := by
        rw [← hq]
        exact partitionIndex_mem P x
      have hymem : y ∈ P.block (some z) := by
        rw [← hq, hxy]
        exact partitionIndex_mem P y
      have hxval : x = z.1 := by
        simpa [P, edgeContractionPartition, edgeContractionBlock] using hxmem
      have hyval : y = z.1 := by
        simpa [P, edgeContractionPartition, edgeContractionBlock] using hymem
      exact hxval.trans hyval.symm

/-- Pulling back a contraction separation preserves adhesion order when the
contracted vertex is outside the adhesion. -/
theorem edgeContraction_pullback_separator_card_away {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (S : VertexSeparation (edgeContraction G hab))
    (hnone : none ∉ S.separator) :
    Nat.card (partitionPullbackSeparation (edgeContractionPartition G hab) S).separator =
      Nat.card S.separator := by
  classical
  let P := edgeContractionPartition G hab
  let U : Set V := (partitionPullbackSeparation P S).separator
  let T : Set (EdgeContractionVertex a b) := S.separator
  let f : U → T := fun x => ⟨partitionIndex P x, by
    have hx : (x : V) ∈ (partitionPullbackSeparation P S).separator := x.property
    rw [partitionPullbackSeparation_separator] at hx
    exact hx⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply edgeContraction_index_inj_away hab
    · intro hn
      exact hnone (by rw [←hn]; exact (f x).property)
    · exact congrArg Subtype.val hxy
  have hsurj : Function.Surjective f := by
    intro q
    cases hq : q.1 with
    | none => exact False.elim (hnone (by rw [←hq]; exact q.property))
    | some z =>
        have hzidx : partitionIndex P z.1 = some z := by
          have hz : z.1 ≠ a ∧ z.1 ≠ b := z.property
          simpa [P] using edgeContraction_index_some hab z.1 hz.1 hz.2
        have hzT : partitionIndex P z.1 ∈ T := by
          rw [hzidx, ←hq]
          exact q.property
        have hzU : z.1 ∈ U := by
          change z.1 ∈ (partitionPullbackSeparation P S).separator
          rw [partitionPullbackSeparation_separator]
          exact hzT
        refine ⟨⟨z.1, hzU⟩, ?_⟩
        apply Subtype.ext
        exact hzidx.trans hq.symm
  have hcard : Nat.card U = Nat.card T := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  exact hcard

section QuotientIncidence
variable {I : Type*} {G : SimpleGraph V} [Fintype I]

private theorem quotient_edgeWitness (P : ConnectedPartition G I)
    (e : P.touchingQuotient.edgeSet) :
    ∃ f : G.edgeSet, Sym2.map (partitionIndex P) f.1 = e.1 := by
  let i := e.1.out.1
  let j := e.1.out.2
  have hij : P.touchingQuotient.Adj i j := by
    change P.touchingQuotient.Adj e.1.out.1 e.1.out.2
    apply (P.touchingQuotient.mem_edgeSet).mp
    simpa only [Sym2.mk, e.1.out_eq] using e.property
  obtain ⟨_, x, hx, y, hy, hxy⟩ :=
    (P.touchingQuotient_adj_iff i j).mp hij
  let f : G.edgeSet := ⟨s(x, y), (G.mem_edgeSet).mpr hxy⟩
  refine ⟨f, ?_⟩
  change s(partitionIndex P x, partitionIndex P y) = e.1
  rw [partitionIndex_eq_of_mem P x i hx,
    partitionIndex_eq_of_mem P y j hy]
  exact e.1.out_eq

/-- The edge incidence of a quotient shore is at most that of its
preimage in the original graph, by an injective choice of edge witnesses. -/
theorem quotient_incidence_le_original
    (P : ConnectedPartition G I) (B : Set I) :
    edgeIncidenceSetCount P.touchingQuotient B ≤
      edgeIncidenceSetCount G (partitionIndex P ⁻¹' B) := by
  classical
  let witness (e : P.touchingQuotient.edgeSet) : G.edgeSet :=
    Classical.choose (quotient_edgeWitness P e)
  have hw (e : P.touchingQuotient.edgeSet) :
      Sym2.map (partitionIndex P) (witness e).1 = e.1 :=
    Classical.choose_spec (quotient_edgeWitness P e)
  let lift : edgeIncidenceSet P.touchingQuotient B →
      edgeIncidenceSet G (partitionIndex P ⁻¹' B) := fun e =>
    ⟨witness e.1, by
      obtain ⟨i, hiB, hiMem⟩ := e.property
      have hiMap : i ∈ Sym2.map (partitionIndex P) (witness e.1).1 := by
        rw [hw e.1]
        exact hiMem
      obtain ⟨v, hv, hvIdx⟩ := Sym2.mem_map.mp hiMap
      refine ⟨v, ?_, hv⟩
      change partitionIndex P v ∈ B
      rw [hvIdx]
      exact hiB⟩
  have hinj : Function.Injective lift := by
    intro e f hef
    apply Subtype.ext
    have hval : witness e.1 = witness f.1 := congrArg Subtype.val hef
    have hmap := congrArg (fun q : G.edgeSet =>
      Sym2.map (partitionIndex P) q.1) hval
    have heq : e.1.1 = f.1.1 := (hw e.1).symm.trans (hmap.trans (hw f.1))
    exact Subtype.ext heq
  unfold edgeIncidenceSetCount
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_injective lift hinj

end QuotientIncidence

/-- An edge contraction preserves the cardinality of any vertex set not
containing the contracted vertex when pulled back to the original graph. -/
theorem edgeContraction_preimage_card_away {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) (B : Set (EdgeContractionVertex a b))
    (hnone : none ∉ B) :
    Nat.card (partitionIndex (edgeContractionPartition G hab) ⁻¹' B) =
      Nat.card B := by
  classical
  let P := edgeContractionPartition G hab
  let U : Set V := partitionIndex P ⁻¹' B
  let f : U → B := fun x => ⟨partitionIndex P x, x.property⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply edgeContraction_index_inj_away hab
    · intro hn
      exact hnone (by rw [← hn]; exact (f x).property)
    · exact congrArg Subtype.val hxy
  have hsurj : Function.Surjective f := by
    intro q
    cases hq : q.1 with
    | none => exact False.elim (hnone (by rw [←hq]; exact q.property))
    | some z =>
        have hzidx : partitionIndex P z.1 = some z := by
          have hz : z.1 ≠ a ∧ z.1 ≠ b := z.property
          simpa [P] using edgeContraction_index_some hab z.1 hz.1 hz.2
        have hzU : z.1 ∈ U := by
          change partitionIndex P z.1 ∈ B
          rw [hzidx, ←hq]
          exact q.property
        refine ⟨⟨z.1, hzU⟩, ?_⟩
        apply Subtype.ext
        exact hzidx.trans hq.symm
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

/-- A massed-pair shore bound survives an edge contraction for separations
whose far side avoids the contracted vertex. -/
theorem edgeContraction_shore_away {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) (X : Finset V) (α : ℝ)
    (hm : MassedPair G (X : Set V) α)
    (S : VertexSeparation (edgeContraction G hab))
    (hroot : (partitionIndex (edgeContractionPartition G hab) '' (X : Set V)) ⊆ S.left)
    (hsep : Nat.card S.separator <
      Nat.card (partitionIndex (edgeContractionPartition G hab) '' (X : Set V)))
    (hnone : none ∉ S.right) :
    (edgeIncidenceSetCount (edgeContraction G hab) S.strictRight : ℝ) ≤
      α * (Nat.card S.strictRight : ℝ) := by
  classical
  let P := edgeContractionPartition G hab
  let T := partitionPullbackSeparation P S
  have hrootT : (X : Set V) ⊆ T.left := by
    intro x hx
    exact hroot ⟨x, hx, rfl⟩
  have himage : Nat.card (partitionIndex P '' (X : Set V)) ≤
      Nat.card (X : Set V) := by
    let f : {x : V // x ∈ X} →
        {y : EdgeContractionVertex a b // y ∈ partitionIndex P '' (X : Set V)} :=
      fun x => ⟨partitionIndex P x.1, ⟨x.1, x.2, rfl⟩⟩
    have hsurj : Function.Surjective f := by
      rintro ⟨y, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_surjective f hsurj
  have hnoneSep : none ∉ S.separator := by
    intro hn
    exact hnone hn.2
  have hsepT : Nat.card T.separator < Nat.card (X : Set V) := by
    have hcard : Nat.card T.separator = Nat.card S.separator := by
      exact edgeContraction_pullback_separator_card_away hab S hnoneSep
    have hsepP : Nat.card S.separator < Nat.card (partitionIndex P '' (X : Set V)) := by
      simpa [P] using hsep
    omega
  have hshore := hm.shore T hrootT hsepT
  have hfarT : T.strictRight = partitionIndex P ⁻¹' S.strictRight := by
    ext x
    rfl
  rw [hfarT] at hshore
  have hnoneFar : none ∉ S.strictRight := by
    intro h
    exact hnone h.1
  have hcardFar : Nat.card (partitionIndex P ⁻¹' S.strictRight) =
      Nat.card S.strictRight :=
    edgeContraction_preimage_card_away hab S.strictRight hnoneFar
  rw [hcardFar] at hshore
  have hinc : edgeIncidenceSetCount (edgeContraction G hab) S.strictRight ≤
      edgeIncidenceSetCount G (partitionIndex P ⁻¹' S.strictRight) :=
    quotient_incidence_le_original P S.strictRight
  have hincR : (edgeIncidenceSetCount (edgeContraction G hab) S.strictRight : ℝ) ≤
      (edgeIncidenceSetCount G (partitionIndex P ⁻¹' S.strictRight) : ℝ) := by
    exact_mod_cast hinc
  exact hincR.trans hshore

theorem edgeContraction_index_left {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) :
    partitionIndex (edgeContractionPartition G hab) a = none := by
  apply partitionIndex_eq_of_mem
  simp [edgeContractionPartition, edgeContractionBlock]

theorem edgeContraction_index_right {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) :
    partitionIndex (edgeContractionPartition G hab) b = none := by
  apply partitionIndex_eq_of_mem
  simp [edgeContractionPartition, edgeContractionBlock]

/-- A set containing the contracted vertex has one extra vertex in its
pullback: that vertex splits into the two original endpoints. -/
theorem edgeContraction_preimage_card_of_mem_contract {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) (B : Set (EdgeContractionVertex a b))
    (hnone : none ∈ B) :
    Nat.card (partitionIndex (edgeContractionPartition G hab) ⁻¹' B) =
      Nat.card B + 1 := by
  classical
  let P := edgeContractionPartition G hab
  let U : Set V := partitionIndex P ⁻¹' B
  let B0 : Set (EdgeContractionVertex a b) := B \ {none}
  let W : Set V := partitionIndex P ⁻¹' B0
  have ha : partitionIndex P a = none := by simpa [P] using edgeContraction_index_left hab
  have hb : partitionIndex P b = none := by simpa [P] using edgeContraction_index_right hab
  have hpair : ({a, b} : Set V).ncard = 2 := by
    simp [hab.ne]
  have hU : U = ({a, b} : Set V) ∪ W := by
    ext x
    constructor
    · intro hx
      by_cases hidx : partitionIndex P x = none
      · have hmem : x ∈ P.block none := by
          rw [←hidx]
          exact partitionIndex_mem P x
        have hxpair : x = a ∨ x = b := by
          simpa [P, edgeContractionPartition, edgeContractionBlock] using hmem
        exact Or.inl hxpair
      · exact Or.inr ⟨hx, hidx⟩
    · rintro (hx | hx)
      · rcases hx with hxa | hxb
        · change partitionIndex P x ∈ B
          rw [hxa, ha]
          exact hnone
        · change partitionIndex P x ∈ B
          rw [hxb, hb]
          exact hnone
      · exact hx.1
  have hdis : Disjoint ({a, b} : Set V) W := by
    apply Set.disjoint_left.mpr
    intro x hx hW
    rcases hx with rfl | rfl
    · exact hW.2 ha
    · exact hW.2 hb
  have hW : Nat.card W = Nat.card B0 := by
    exact edgeContraction_preimage_card_away hab B0 (by simp [B0])
  have hB : Nat.card B0 + 1 = Nat.card B := by
    change B0.ncard + 1 = B.ncard
    simpa only [B0] using Set.ncard_sdiff_singleton_add_one hnone
  change W.ncard = B0.ncard at hW
  change B0.ncard + 1 = B.ncard at hB
  change U.ncard = B.ncard + 1
  rw [hU, Set.ncard_union_eq hdis, hpair]
  omega

/-- Contracting an edge with an endpoint outside the root set keeps all roots distinct. -/
theorem edgeContraction_index_injOn_roots {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) (X : Finset V) (hb : b ∉ X) :
    Set.InjOn (partitionIndex (edgeContractionPartition G hab)) (X : Set V) := by
  let P := edgeContractionPartition G hab
  have hnone_a (x : V) (hx : x ∈ X) (hidx : partitionIndex P x = none) :
      x = a := by
    have hxmem : x ∈ P.block none := by
      rw [←hidx]
      exact partitionIndex_mem P x
    have hor : x = a ∨ x = b := by
      simpa [P, edgeContractionPartition, edgeContractionBlock] using hxmem
    rcases hor with h | h
    · exact h
    · exact False.elim (hb (h ▸ hx))
  intro x hx y hy hxy
  by_cases hxnone : partitionIndex P x = none
  · have hynone : partitionIndex P y = none := hxy.symm.trans hxnone
    exact (hnone_a x hx hxnone).trans (hnone_a y hy hynone).symm
  · exact edgeContraction_index_inj_away hab hxnone hxy

/-- Numerical core of (D.2): when contraction destroys strict mass and costs
`1 + c + ε` incidences with `ε ≤ 1`, the endpoints have at least `λ-1`
common neighbors. -/
theorem common_neighbor_lower_of_mass_drop
    (m before after c ε r : ℕ) (hm : 0 < m)
    (hbefore : r * m < before)
    (hafter : after ≤ r * (m - 1))
    (hbalance : after + 1 + c + ε = before)
    (hepsilon : ε ≤ 1) :
    r - 1 ≤ c := by
  have hmstep : m - 1 + 1 = m := by omega
  have hmul : r * m = r * (m - 1) + r := by
    calc
      r * m = r * ((m - 1) + 1) := congrArg (r * ·) hmstep.symm
      _ = r * (m - 1) + r := by ring
  omega

/-- Contracting an edge disjoint from the roots leaves the induced root graph
unchanged up to isomorphism. -/
noncomputable def edgeContraction_rootInduceIso {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) (X : Finset V) (ha : a ∉ X) (hb : b ∉ X) :
    let P := edgeContractionPartition G hab
    let Y : Set (EdgeContractionVertex a b) := partitionIndex P '' (X : Set V)
    (G.induce (X : Set V)) ≃g ((edgeContraction G hab).induce Y) := by
  intro P Y
  let f : {x : V // x ∈ X} → {q : EdgeContractionVertex a b // q ∈ Y} := fun x =>
    ⟨partitionIndex P x.1, ⟨x.1, x.2, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact (edgeContraction_index_injOn_roots hab X hb) x.property y.property
      (congrArg Subtype.val hxy)
  have hsurj : Function.Surjective f := by
    rintro ⟨q, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  let e : {x : V // x ∈ X} ≃ {q : EdgeContractionVertex a b // q ∈ Y} := Equiv.ofBijective f ⟨hinj, hsurj⟩
  refine {
    toEquiv := e
    map_rel_iff' := ?_
  }
  intro x y
  have hxA : (x : V) ≠ a := by
    intro heq
    exact ha (heq ▸ x.property)
  have hxB : (x : V) ≠ b := by
    intro heq
    exact hb (heq ▸ x.property)
  have hyA : (y : V) ≠ a := by
    intro heq
    exact ha (heq ▸ y.property)
  have hyB : (y : V) ≠ b := by
    intro heq
    exact hb (heq ▸ y.property)
  have hxidx : partitionIndex P (x : V) = some (⟨x, hxA, hxB⟩ : EdgeOutside a b) :=
    edgeContraction_index_some hab x hxA hxB
  have hyidx : partitionIndex P (y : V) = some (⟨y, hyA, hyB⟩ : EdgeOutside a b) :=
    edgeContraction_index_some hab y hyA hyB
  change (edgeContraction G hab).Adj (partitionIndex P x) (partitionIndex P y) ↔
    G.Adj x y
  rw [hxidx, hyidx]
  exact edgeContraction_adj_some_some (G := G) hab _ _

/-- Contracting an edge disjoint from the roots drops the exterior incidence
count by exactly one plus the number of common neighbors. -/
theorem edgeContraction_incidence_drop_outside {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} (hab : G.Adj a b)
    (X : Finset V) (ha : a ∉ X) (hb : b ∉ X) :
    let P := edgeContractionPartition G hab
    let Y : Set (EdgeContractionVertex a b) := partitionIndex P '' (X : Set V)
    edgeIncidenceCount (edgeContraction G hab) Y.toFinsetᶜ + 1 +
      (G.neighborFinset a ∩ G.neighborFinset b).card =
        edgeIncidenceCount G Xᶜ := by
  classical
  intro P Y
  let Q := edgeContraction G hab
  have hXset : (((Xᶜ)ᶜ : Finset V) : Set V) = (X : Set V) := by
    ext v
    simp
  have hYset : (((Y.toFinsetᶜ)ᶜ : Finset (EdgeContractionVertex a b)) : Set (EdgeContractionVertex a b)) = Y := by
    ext v
    simp
  have hG := edgeCount_induce_compl_add_incidence (G := G) Xᶜ
  have hQ := edgeCount_induce_compl_add_incidence (G := Q) Y.toFinsetᶜ
  rw [hXset] at hG
  rw [hYset] at hQ
  have hiso : edgeCount (G.induce (X : Set V)) = edgeCount (Q.induce Y) :=
    edgeCount_eq_of_iso (edgeContraction_rootInduceIso hab X ha hb)
  have htotal := edgeContraction_edgeCount_add_one_add_common hab
  change edgeCount Q + 1 + (G.neighborFinset a ∩ G.neighborFinset b).card = edgeCount G at htotal
  change edgeIncidenceCount Q Y.toFinsetᶜ + 1 +
    (G.neighborFinset a ∩ G.neighborFinset b).card = edgeIncidenceCount G Xᶜ
  omega

/-- The exterior-edge case of (D.2): if contracting an edge disjoint from
the roots destroys the strict global mass inequality, then its endpoints
have at least `r-1` common neighbors. -/
theorem common_neighbors_ge_of_exterior_contraction_mass_failure {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} (hab : G.Adj a b) (X : Finset V)
    (ha : a ∉ X) (hb : b ∉ X) (r : ℕ)
    (hm : MassedPair G (X : Set V) (r : ℝ)) :
    let P := edgeContractionPartition G hab
    let Y : Set (EdgeContractionVertex a b) := partitionIndex P '' (X : Set V)
    (edgeIncidenceSetCount (edgeContraction G hab) Yᶜ : ℝ) ≤
        (r : ℝ) * ((Yᶜ).ncard : ℝ) →
      r - 1 ≤ (G.neighborFinset a ∩ G.neighborFinset b).card := by
  classical
  intro P Y hfail
  let Q := edgeContraction G hab
  have hnoneY : none ∉ Y := by
    rintro ⟨x, hx, hidx⟩
    have hxa : x ≠ a := by intro h; exact ha (h ▸ hx)
    have hxb : x ≠ b := by intro h; exact hb (h ▸ hx)
    have hs : partitionIndex P x = some (⟨x, hxa, hxb⟩ : EdgeOutside a b) :=
      edgeContraction_index_some hab x hxa hxb
    rw [hs] at hidx
    cases hidx
  have hpre : partitionIndex P ⁻¹' Yᶜ = (X : Set V)ᶜ := by
    ext x
    constructor
    · intro hx hroot
      exact hx ⟨x, hroot, rfl⟩
    · intro hx himage
      obtain ⟨y, hy, heq⟩ := himage
      have hya : y ≠ a := by intro h; exact ha (h ▸ hy)
      have hyb : y ≠ b := by intro h; exact hb (h ▸ hy)
      have hySome : partitionIndex P y ≠ none := by
        rw [edgeContraction_index_some hab y hya hyb]
        simp
      have hxSome : partitionIndex P x ≠ none := by
        rw [←heq]
        exact hySome
      have hxy : x = y := edgeContraction_index_inj_away hab hxSome heq.symm
      exact hx (hxy ▸ hy)
  have hnoneComp : none ∈ Yᶜ := hnoneY
  have hsize : ((X : Set V)ᶜ).ncard = (Yᶜ).ncard + 1 := by
    rw [←hpre]
    exact edgeContraction_preimage_card_of_mem_contract hab Yᶜ hnoneComp
  have hmpos : 0 < ((X : Set V)ᶜ).ncard := by
    change 0 < ((X : Set V)ᶜ).ncard
    exact (Set.ncard_pos).mpr ⟨a, ha⟩
  have hdrop : edgeIncidenceSetCount Q Yᶜ + 1 +
      (G.neighborFinset a ∩ G.neighborFinset b).card =
        edgeIncidenceSetCount G (X : Set V)ᶜ := by
    have hfin := edgeContraction_incidence_drop_outside hab X ha hb
    change edgeIncidenceCount Q Y.toFinsetᶜ + 1 +
      (G.neighborFinset a ∩ G.neighborFinset b).card =
        edgeIncidenceCount G Xᶜ at hfin
    have hQ : edgeIncidenceCount Q Y.toFinsetᶜ =
        edgeIncidenceSetCount Q Yᶜ := by
      simpa using (incidenceSetCount_eq_finsetCount Q Y.toFinsetᶜ).symm
    have hG : edgeIncidenceCount G Xᶜ =
        edgeIncidenceSetCount G (X : Set V)ᶜ := by
      simpa using (incidenceSetCount_eq_finsetCount G Xᶜ).symm
    rw [hQ, hG] at hfin
    exact hfin
  have hcardRoot : Nat.card {v : V // v ∉ (X : Set V)} =
      ((X : Set V)ᶜ).ncard := by rfl
  have hbefore : r * ((X : Set V)ᶜ).ncard <
      edgeIncidenceSetCount G (X : Set V)ᶜ := by
    have hglobal := hm.global
    rw [hcardRoot] at hglobal
    exact_mod_cast hglobal
  have hafter : edgeIncidenceSetCount Q Yᶜ ≤ r * (Yᶜ).ncard := by
    exact_mod_cast hfail
  apply common_neighbor_lower_of_mass_drop
    (((X : Set V)ᶜ).ncard) (edgeIncidenceSetCount G (X : Set V)ᶜ)
    (edgeIncidenceSetCount Q Yᶜ)
    (G.neighborFinset a ∩ G.neighborFinset b).card 0 r hmpos hbefore
  · simpa [hsize] using hafter
  · simpa using hdrop
  · omega

private theorem induced_degree_eq_neighbor_inter_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) [Fintype S] (a : V) (ha : a ∈ S) :
    (G.induce S).degree (⟨a, ha⟩ : S) =
      (G.neighborFinset a ∩ S.toFinset).card := by
  classical
  have hmap : ((G.induce S).neighborFinset (⟨a,ha⟩ : S)).map
      (Function.Embedding.subtype (· ∈ S)) =
      G.neighborFinset a ∩ S.toFinset := by
    ext x
    simp
  simpa only [SimpleGraph.degree, Finset.card_map] using congrArg Finset.card hmap


private noncomputable def edgeContraction_rootEraseIso {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) (X : Finset V) (ha : a ∈ X) (hb : b ∉ X) :
    let P := edgeContractionPartition G hab
    let Y : Set (EdgeContractionVertex a b) := partitionIndex P '' (X : Set V)
    let xa : (X : Set V) := ⟨a, ha⟩
    let q0 : Y := ⟨none, ⟨a, ha, edgeContraction_index_left hab⟩⟩
    ((G.induce (X : Set V)).induce ({xa} : Set (X : Set V))ᶜ) ≃g
      (((edgeContraction G hab).induce Y).induce ({q0} : Set Y)ᶜ) := by
  classical
  intro P Y xa q0
  let Q := edgeContraction G hab
  let f : {x : (X : Set V) // x ∈ ({xa} : Set (X : Set V))ᶜ} →
      {q : Y // q ∈ ({q0} : Set Y)ᶜ} := fun x =>
    ⟨⟨partitionIndex P x.1.1, ⟨x.1.1, x.1.2, rfl⟩⟩, by
      have hxa : x.1.1 ≠ a := by
        intro heq
        have he : x.1 = xa := Subtype.ext heq
        exact x.2 he
      have hxb : x.1.1 ≠ b := by
        intro heq
        exact hb (heq ▸ x.1.2)
      have hs := edgeContraction_index_some hab x.1.1 hxa hxb
      intro heq
      have hn : partitionIndex P x.1.1 = none := congrArg (fun t : Y => (t : EdgeContractionVertex a b)) heq
      rw [hs] at hn
      cases hn⟩
  have hinj : Function.Injective f := by
    intro x y heq
    apply Subtype.ext
    apply Subtype.ext
    apply edgeContraction_index_injOn_roots hab X hb x.1.2 y.1.2
    exact congrArg (fun t : {q : Y // q ∈ ({q0} : Set Y)ᶜ} => (t.1 : EdgeContractionVertex a b)) heq
  have hsurj : Function.Surjective f := by
    rintro ⟨⟨q, x, hx, hidx⟩, hq⟩
    have hxa : x ≠ a := by
      intro heq
      subst x
      have hnone : q = none := by simpa [P] using hidx.symm.trans (edgeContraction_index_left hab)
      exact hq (Subtype.ext hnone)
    let xx : {x : (X : Set V) // x ∈ ({xa} : Set (X : Set V))ᶜ} :=
      ⟨⟨x,hx⟩, by
        intro heq
        exact hxa (congrArg Subtype.val heq)⟩
    refine ⟨xx, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hidx
  let e := Equiv.ofBijective f ⟨hinj,hsurj⟩
  refine {toEquiv := e, map_rel_iff' := ?_}
  intro x y
  have hxa : x.1.1 ≠ a := by
    intro heq
    exact x.2 (Subtype.ext heq)
  have hxb : x.1.1 ≠ b := by
    intro heq
    exact hb (heq ▸ x.1.2)
  have hya : y.1.1 ≠ a := by
    intro heq
    exact y.2 (Subtype.ext heq)
  have hyb : y.1.1 ≠ b := by
    intro heq
    exact hb (heq ▸ y.1.2)
  change Q.Adj (partitionIndex P x.1.1) (partitionIndex P y.1.1) ↔ G.Adj x.1.1 y.1.1
  rw [edgeContraction_index_some hab x.1.1 hxa hxb,
    edgeContraction_index_some hab y.1.1 hya hyb]
  exact edgeContraction_adj_some_some (G := G) hab _ _


private theorem edgeContraction_rootDegree {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} (hab : G.Adj a b) (X : Finset V) (hb : b ∉ X)
    [DecidableRel (edgeContraction G hab).Adj]
    (Y : Set (EdgeContractionVertex a b)) [Fintype Y]
    (hY : Y = partitionIndex (edgeContractionPartition G hab) '' (X : Set V))
    (q0 : Y) (hq0 : (q0 : EdgeContractionVertex a b) = none) :
    ((edgeContraction G hab).induce Y).degree q0 =
      (((G.neighborFinset a ∪ G.neighborFinset b) ∩ X.erase a)).card := by
  classical
  let P := edgeContractionPartition G hab
  let Q := edgeContraction G hab
  obtain ⟨q0,hq0Y⟩ := q0
  change q0 = none at hq0
  subst q0
  have hdeg := induced_degree_eq_neighbor_inter_card Q Y none hq0Y
  change (Q.induce Y).degree (⟨none,hq0Y⟩ : Y) =
    (Q.neighborFinset none ∩ Y.toFinset).card at hdeg
  rw [hdeg]
  symm
  apply Finset.card_bij (fun x _ => partitionIndex P x)
  · intro x hx
    have hxX : x ∈ X := (Finset.mem_erase.mp (Finset.mem_inter.mp hx).2).2
    have hxa : x ≠ a := (Finset.mem_erase.mp (Finset.mem_inter.mp hx).2).1
    have hxb : x ≠ b := by intro heq; exact hb (heq ▸ hxX)
    have hadj : G.Adj a x ∨ G.Adj b x := by
      simpa using (Finset.mem_union.mp (Finset.mem_inter.mp hx).1)
    apply Finset.mem_inter.mpr
    constructor
    · apply (Q.mem_neighborFinset none _).2
      rw [edgeContraction_index_some hab x hxa hxb]
      exact (edgeContraction_adj_none_some (G := G) hab ⟨x,hxa,hxb⟩).2 hadj
    · apply Set.mem_toFinset.mpr
      rw [hY]
      exact ⟨x,hxX,rfl⟩
  · intro x hx y hy hxy
    apply edgeContraction_index_injOn_roots hab X hb
    · exact (Finset.mem_erase.mp (Finset.mem_inter.mp hx).2).2
    · exact (Finset.mem_erase.mp (Finset.mem_inter.mp hy).2).2
    · exact hxy
  · intro q hq
    have hqY : q ∈ Y := Set.mem_toFinset.mp (Finset.mem_inter.mp hq).2
    rw [hY] at hqY
    obtain ⟨x,hxX,rfl⟩ := hqY
    have hxa : x ≠ a := by
      intro heq
      subst x
      have hn : partitionIndex P a = none := edgeContraction_index_left hab
      have hqadj : Q.Adj none (partitionIndex P a) :=
        (Q.mem_neighborFinset none _).1 (Finset.mem_inter.mp hq).1
      rw [hn] at hqadj
      exact Q.irrefl hqadj
    have hxb : x ≠ b := by intro heq; exact hb (heq ▸ hxX)
    have hadj : G.Adj a x ∨ G.Adj b x := by
      have hqadj : Q.Adj none (partitionIndex P x) :=
        (Q.mem_neighborFinset none _).1 (Finset.mem_inter.mp hq).1
      rw [edgeContraction_index_some hab x hxa hxb] at hqadj
      exact (edgeContraction_adj_none_some (G := G) hab ⟨x,hxa,hxb⟩).1 hqadj
    refine ⟨x, ?_, rfl⟩
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_union.mpr (by simpa using hadj)
    · exact Finset.mem_erase.mpr ⟨hxa,hxX⟩

private theorem edgeContraction_rootEpsilon_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (a b : V) :
    ((G.neighborFinset a ∪ G.neighborFinset b) ∩ X.erase a).card =
      (G.neighborFinset a ∩ X).card +
      ((G.neighborFinset b ∩ X.erase a) \ G.neighborFinset a).card := by
  classical
  let A := G.neighborFinset a ∩ X.erase a
  let B := G.neighborFinset b ∩ X.erase a
  have hA : (G.neighborFinset a ∩ X).card = A.card := by
    congr 1
    ext x
    simp only [A, Finset.mem_inter, Finset.mem_erase, G.mem_neighborFinset]
    constructor
    · rintro ⟨hax,hx⟩
      exact ⟨hax,hax.ne.symm,hx⟩
    · rintro ⟨hax,_,hx⟩
      exact ⟨hax,hx⟩
  have hU : ((G.neighborFinset a ∪ G.neighborFinset b) ∩ X.erase a) = A ∪ B := by
    ext x
    simp only [A, B, Finset.mem_inter, Finset.mem_erase, Finset.mem_union,
      G.mem_neighborFinset]
    tauto
  have hD : (G.neighborFinset b ∩ X.erase a) \ G.neighborFinset a = B \ A := by
    ext x
    simp only [A, B, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_erase,
      G.mem_neighborFinset]
    tauto
  rw [hU, hA, hD]
  have h1 := Finset.card_union_add_card_inter A B
  have h2 := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at h2
  omega

/-- The extra root-edge loss at a contraction is at most one when each root has at most one missing root neighbor. -/
theorem edgeContraction_rootEpsilon_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (a b : V) (ha : a ∈ X)
    (hmissing : ∀ x ∈ X, (X.erase x \ G.neighborFinset x).card ≤ 1) :
    ((G.neighborFinset b ∩ X.erase a) \ G.neighborFinset a).card ≤ 1 := by
  apply (Finset.card_le_card ?_).trans (hmissing a ha)
  intro x hx
  simp only [Finset.mem_sdiff, Finset.mem_inter] at hx ⊢
  exact ⟨hx.1.2,hx.2⟩

private theorem edgeContraction_internal_root_add_epsilon {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} (hab : G.Adj a b) (X : Finset V) (ha : a ∈ X) (hb : b ∉ X)
    [DecidableRel (edgeContraction G hab).Adj]
    (Y : Set (EdgeContractionVertex a b)) [Fintype Y]
    (hY : Y = partitionIndex (edgeContractionPartition G hab) '' (X : Set V))
    (q0 : Y) (hq0 : (q0 : EdgeContractionVertex a b) = none) :
    edgeCount ((edgeContraction G hab).induce Y) =
      edgeCount (G.induce (X : Set V)) +
        ((G.neighborFinset b ∩ X.erase a) \ G.neighborFinset a).card := by
  classical
  subst Y
  let Q := edgeContraction G hab
  let xa : (X : Set V) := ⟨a,ha⟩
  let yy : Set (EdgeContractionVertex a b) :=
    partitionIndex (edgeContractionPartition G hab) '' (X : Set V)
  let y0 : yy := ⟨none, ⟨a,ha,edgeContraction_index_left hab⟩⟩
  have hq : q0 = y0 := Subtype.ext hq0
  subst q0
  have hG := edgeCount_induce_compl_singleton_add_degree (G.induce (X : Set V)) xa
  have hQ := edgeCount_induce_compl_singleton_add_degree (Q.induce yy) y0
  have hiso := edgeCount_eq_of_iso (edgeContraction_rootEraseIso hab X ha hb)
  have hdG := induced_degree_eq_neighbor_inter_card G (X : Set V) a ha
  have hdQ := edgeContraction_rootDegree hab X hb yy rfl y0 rfl
  have heps := edgeContraction_rootEpsilon_card G X a b
  change edgeCount ((G.induce (X : Set V)).induce ({xa} : Set (X : Set V))ᶜ) +
      (G.induce (X : Set V)).degree xa = edgeCount (G.induce (X : Set V)) at hG
  change edgeCount ((Q.induce yy).induce ({y0} : Set yy)ᶜ) +
      (Q.induce yy).degree y0 = edgeCount (Q.induce yy) at hQ
  change edgeCount ((G.induce (X : Set V)).induce ({xa} : Set (X : Set V))ᶜ) =
      edgeCount ((Q.induce yy).induce ({y0} : Set yy)ᶜ) at hiso
  have hdGx : (G.induce (X : Set V)).degree xa = (G.neighborFinset a ∩ X).card := by
    simpa [xa] using hdG
  change edgeCount (Q.induce yy) = edgeCount (G.induce (X : Set V)) +
    ((G.neighborFinset b ∩ X.erase a) \ G.neighborFinset a).card
  have hdQx : (Q.induce yy).degree y0 =
    ((G.neighborFinset a ∪ G.neighborFinset b) ∩ X.erase a).card := by
    simpa [Q] using hdQ
  omega

/-- Exact incidence loss for an edge contraction with one endpoint in the root set. -/
theorem edgeContraction_incidence_drop_root {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} (hab : G.Adj a b)
    (X : Finset V) (ha : a ∈ X) (hb : b ∉ X) :
    let P := edgeContractionPartition G hab
    let Y : Set (EdgeContractionVertex a b) := partitionIndex P '' (X : Set V)
    edgeIncidenceCount (edgeContraction G hab) Y.toFinsetᶜ + 1 +
      (G.neighborFinset a ∩ G.neighborFinset b).card +
      ((G.neighborFinset b ∩ X.erase a) \ G.neighborFinset a).card =
        edgeIncidenceCount G Xᶜ := by
  classical
  intro P Y
  let Q := edgeContraction G hab
  let q0 : Y := ⟨none, ⟨a, ha, edgeContraction_index_left hab⟩⟩
  have hXset : (((Xᶜ)ᶜ : Finset V) : Set V) = (X : Set V) := by
    ext v
    simp
  have hYset : (((Y.toFinsetᶜ)ᶜ : Finset (EdgeContractionVertex a b)) : Set (EdgeContractionVertex a b)) = Y := by
    ext v
    simp
  have hG := edgeCount_induce_compl_add_incidence (G := G) Xᶜ
  have hQ := edgeCount_induce_compl_add_incidence (G := Q) Y.toFinsetᶜ
  rw [hXset] at hG
  rw [hYset] at hQ
  have hinner : edgeCount (Q.induce Y) =
      edgeCount (G.induce (X : Set V)) +
        ((G.neighborFinset b ∩ X.erase a) \ G.neighborFinset a).card := by
    simpa [Q, Y, P] using edgeContraction_internal_root_add_epsilon hab X ha hb Y rfl q0 rfl
  have htotal := edgeContraction_edgeCount_add_one_add_common hab
  change edgeCount Q + 1 + (G.neighborFinset a ∩ G.neighborFinset b).card = edgeCount G at htotal
  change edgeIncidenceCount Q Y.toFinsetᶜ + 1 +
      (G.neighborFinset a ∩ G.neighborFinset b).card +
      ((G.neighborFinset b ∩ X.erase a) \ G.neighborFinset a).card = edgeIncidenceCount G Xᶜ
  omega

/-- Contracting a root-outside edge decreases the number of outside vertices by one. -/
theorem edgeContraction_root_compl_card {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) (X : Finset V) (ha : a ∈ X) (hb : b ∉ X) :
    let P := edgeContractionPartition G hab
    let Y : Set (EdgeContractionVertex a b) := partitionIndex P '' (X : Set V)
    ((X : Set V)ᶜ).ncard = (Yᶜ).ncard + 1 := by
  classical
  intro P Y
  have hnoneY : none ∈ Y := ⟨a, ha, edgeContraction_index_left hab⟩
  have hnoneComp : none ∉ Yᶜ := by
    intro h
    exact h hnoneY
  have hpre : partitionIndex P ⁻¹' Yᶜ = (X : Set V)ᶜ \ {b} := by
    ext x
    constructor
    · intro hx
      constructor
      · intro hX
        exact hx ⟨x,hX,rfl⟩
      · intro hxb
        subst x
        exact hx (by
          rw [edgeContraction_index_right hab]
          exact hnoneY)
    · rintro ⟨hxX,hxb⟩ himage
      obtain ⟨y,hy,heq⟩ := himage
      have hxa : x ≠ a := by intro h; exact hxX (h ▸ ha)
      have hxSome : partitionIndex P x ≠ none := by
        rw [edgeContraction_index_some hab x hxa hxb]
        simp
      have hySome : partitionIndex P y ≠ none := by
        rw [heq]
        exact hxSome
      have hxy : x = y := edgeContraction_index_inj_away hab hxSome heq.symm
      exact hxX (hxy ▸ hy)
  have hcard : ((X : Set V)ᶜ \ {b}).ncard = (Yᶜ).ncard := by
    rw [←hpre]
    exact edgeContraction_preimage_card_away hab Yᶜ hnoneComp
  have hplus : ((X : Set V)ᶜ \ {b}).ncard + 1 = ((X : Set V)ᶜ).ncard := by
    exact Set.ncard_sdiff_singleton_add_one (by simpa using hb)
  omega

/-- Root-outside case of (D.2): failure of strict global mass after contraction forces many common neighbors. -/
theorem common_neighbors_ge_of_root_contraction_mass_failure {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} (hab : G.Adj a b) (X : Finset V)
    (ha : a ∈ X) (hb : b ∉ X) (r : ℕ)
    (hm : MassedPair G (X : Set V) (r : ℝ))
    (hmissing : ∀ x ∈ X, (X.erase x \ G.neighborFinset x).card ≤ 1) :
    let P := edgeContractionPartition G hab
    let Y : Set (EdgeContractionVertex a b) := partitionIndex P '' (X : Set V)
    (edgeIncidenceSetCount (edgeContraction G hab) Yᶜ : ℝ) ≤
        (r : ℝ) * ((Yᶜ).ncard : ℝ) →
      r - 1 ≤ (G.neighborFinset a ∩ G.neighborFinset b).card := by
  classical
  intro P Y hfail
  let Q := edgeContraction G hab
  let ε := ((G.neighborFinset b ∩ X.erase a) \ G.neighborFinset a).card
  have hsize : ((X : Set V)ᶜ).ncard = (Yᶜ).ncard + 1 :=
    edgeContraction_root_compl_card hab X ha hb
  have hmpos : 0 < ((X : Set V)ᶜ).ncard := by
    exact (Set.ncard_pos).mpr ⟨b,hb⟩
  have hdrop : edgeIncidenceSetCount Q Yᶜ + 1 +
      (G.neighborFinset a ∩ G.neighborFinset b).card + ε =
        edgeIncidenceSetCount G (X : Set V)ᶜ := by
    have hfin := edgeContraction_incidence_drop_root hab X ha hb
    change edgeIncidenceCount Q Y.toFinsetᶜ + 1 +
      (G.neighborFinset a ∩ G.neighborFinset b).card + ε =
        edgeIncidenceCount G Xᶜ at hfin
    have hQ : edgeIncidenceCount Q Y.toFinsetᶜ = edgeIncidenceSetCount Q Yᶜ := by
      simpa using (incidenceSetCount_eq_finsetCount Q Y.toFinsetᶜ).symm
    have hG : edgeIncidenceCount G Xᶜ = edgeIncidenceSetCount G (X : Set V)ᶜ := by
      simpa using (incidenceSetCount_eq_finsetCount G Xᶜ).symm
    rw [hQ,hG] at hfin
    exact hfin
  have hbefore : r * ((X : Set V)ᶜ).ncard <
      edgeIncidenceSetCount G (X : Set V)ᶜ := by
    have hglobal := hm.global
    have hcardRoot : Nat.card {v : V // v ∉ (X : Set V)} =
        ((X : Set V)ᶜ).ncard := by rfl
    rw [hcardRoot] at hglobal
    exact_mod_cast hglobal
  have hafter : edgeIncidenceSetCount Q Yᶜ ≤ r * (Yᶜ).ncard := by
    exact_mod_cast hfail
  apply common_neighbor_lower_of_mass_drop
    (((X : Set V)ᶜ).ncard) (edgeIncidenceSetCount G (X : Set V)ᶜ)
    (edgeIncidenceSetCount Q Yᶜ)
    (G.neighborFinset a ∩ G.neighborFinset b).card ε r hmpos hbefore
  · simpa [hsize] using hafter
  · simpa using hdrop
  · exact edgeContraction_rootEpsilon_le_one G X a b ha hmissing
private theorem add_root_edge_other_edge_old {G : SimpleGraph V} (u v : V) :
    ∀ e ∈ (G ⊔ SimpleGraph.fromEdgeSet {s(u,v)}).edgeSet,
      e ≠ s(u,v) → e ∈ G.edgeSet := by
  intro e he hne
  simp only [SimpleGraph.edgeSet_sup, Set.mem_union] at he
  rcases he with h | h
  · exact h
  · simp only [SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, Set.mem_singleton_iff] at h
    exact False.elim (hne h.1)

/-- Adding a root edge that is not a prescribed pair cannot link a fixed bad pairing. -/
theorem fixed_pair_nonlinked_add_other_root_edge
    {G : SimpleGraph V} {ι : Type*} {P : IndexedPairs ι V}
    (X : Finset V) (u v : V) (huX : u ∈ X) (hvX : v ∈ X) (huv : u ≠ v)
    (hother : ∀ i, s(u,v) ≠ s(P.start i,P.finish i))
    (hbad : ¬∃ L : IndexedLinkage G P, InteriorsAvoid L X) :
    ¬∃ L : IndexedLinkage (G ⊔ SimpleGraph.fromEdgeSet {s(u,v)}) P,
      InteriorsAvoid L X := by
  rintro ⟨L,hL⟩
  obtain ⟨L',hL'⟩ := hL.transfer_avoiding_root_edge L X u v huX hvX huv hother
    (add_root_edge_other_edge_old u v)
  exact hbad ⟨L',hL'⟩

/-- Two nested graphs have the same incidence count on S when every edge of the larger graph meeting S already lies in the smaller graph. -/
theorem incidence_eq_of_agree_on_incident_edges
    {G H : SimpleGraph V} (S : Set V) (hGH : G ≤ H)
    (hHG : ∀ e ∈ H.edgeSet, (∃ w ∈ S, w ∈ (e : Sym2 V)) → e ∈ G.edgeSet) :
    edgeIncidenceSetCount H S = edgeIncidenceSetCount G S := by
  have hle : edgeIncidenceSetCount H S ≤ edgeIncidenceSetCount G S := by
    let f : edgeIncidenceSet H S → edgeIncidenceSet G S := fun e =>
      ⟨⟨e.1.1, hHG e.1.1 e.1.2 e.2⟩, e.2⟩
    have hinj : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : edgeIncidenceSet G S => z.1.1) hxy
    exact Nat.card_le_card_of_injective f hinj
  have hge := edgeIncidenceSetCount_mono hGH S
  omega

/-- A new edge joining two roots does not change edge incidence away from them. -/
theorem incidence_add_root_edge
    {G : SimpleGraph V} (S : Set V) (u v : V)
    (hu : u ∉ S) (hv : v ∉ S) :
    edgeIncidenceSetCount (G ⊔ SimpleGraph.fromEdgeSet {s(u,v)}) S =
      edgeIncidenceSetCount G S := by
  apply incidence_eq_of_agree_on_incident_edges S le_sup_left
  intro e heH hS
  obtain ⟨w,hwS,hwe⟩ := hS
  have hne : e ≠ s(u,v) := by
    intro heq
    have hwuv : w = u ∨ w = v := by simpa [heq] using hwe
    rcases hwuv with hwu | hwv
    · exact hu (hwu ▸ hwS)
    · exact hv (hwv ▸ hwS)
  exact add_root_edge_other_edge_old u v e heH hne

/-- Adding an edge inside the root set preserves both massed-pair inequalities. -/
theorem massed_add_root_edge
    {G : SimpleGraph V} (X : Finset V) (α : ℝ)
    (hm : MassedPair G (X : Set V) α)
    (u v : V) (huX : u ∈ X) (hvX : v ∈ X) :
    MassedPair (G ⊔ SimpleGraph.fromEdgeSet {s(u,v)}) (X : Set V) α := by
  let H : SimpleGraph V := G ⊔ SimpleGraph.fromEdgeSet {s(u,v)}
  refine ⟨?_, ?_⟩
  · have hcount := incidence_add_root_edge (G := G) (X : Set V)ᶜ u v
      (by simpa using huX) (by simpa using hvX)
    change edgeIncidenceSetCount H (X : Set V)ᶜ =
      edgeIncidenceSetCount G (X : Set V)ᶜ at hcount
    rw [hcount]
    exact hm.global
  · intro S hroot hsmall
    let T : VertexSeparation G := {
      left := S.left
      right := S.right
      cover := S.cover
      no_cross := by
        intro x y hxL hxNotR hyR hyNotL hG
        exact (S.no_cross hxL hxNotR hyR hyNotL) ((show G ≤ H from le_sup_left) hG)
    }
    have hT : (X : Set V) ⊆ T.left := hroot
    have hsmallT : Nat.card T.separator < Nat.card (X : Set V) := hsmall
    have hshore := hm.shore T hT hsmallT
    have huNot : u ∉ S.strictRight := by
      intro hu
      exact hu.2 (hroot huX)
    have hvNot : v ∉ S.strictRight := by
      intro hv
      exact hv.2 (hroot hvX)
    have hcount := incidence_add_root_edge (G := G) S.strictRight u v huNot hvNot
    change edgeIncidenceSetCount H S.strictRight = edgeIncidenceSetCount G T.strictRight at hcount
    rw [hcount]
    exact hshore
/-- If every missing root edge is a prescribed pair, each root has at most one missing root neighbor. -/
theorem root_at_most_one_nonedge_of_pairable
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (X : Finset V) {ι : Type*} (P : IndexedPairs ι V)
    (hP : P.DisjointTerminals)
    (hpairable : ∀ u ∈ X, ∀ v ∈ X, u ≠ v → ¬G.Adj u v →
      ∃ i, s(u,v) = s(P.start i,P.finish i))
    (u : V) (hu : u ∈ X) :
    (X.erase u \ G.neighborFinset u).card ≤ 1 := by
  apply Finset.card_le_one_iff.mpr
  intro v w hv hw
  have hvX : v ∈ X := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hv).1).2
  have hwX : w ∈ X := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hw).1).2
  have huv : u ≠ v := ((Finset.mem_erase.mp (Finset.mem_sdiff.mp hv).1).1).symm
  have huw : u ≠ w := ((Finset.mem_erase.mp (Finset.mem_sdiff.mp hw).1).1).symm
  have hnv : ¬G.Adj u v := by
    intro hadj
    exact (Finset.mem_sdiff.mp hv).2 ((G.mem_neighborFinset u v).mpr hadj)
  have hnw : ¬G.Adj u w := by
    intro hadj
    exact (Finset.mem_sdiff.mp hw).2 ((G.mem_neighborFinset u w).mpr hadj)
  obtain ⟨i,hi⟩ := hpairable u hu v hvX huv hnv
  obtain ⟨j,hj⟩ := hpairable u hu w hwX huw hnw
  have hui : u ∈ P.terminals i := by
    have hmem : u ∈ s(u,v) := by simp
    rw [hi] at hmem
    simpa [IndexedPairs.terminals] using hmem
  have huj : u ∈ P.terminals j := by
    have hmem : u ∈ s(u,w) := by simp
    rw [hj] at hmem
    simpa [IndexedPairs.terminals] using hmem
  have hij : i = j := by
    by_contra hne
    exact (Set.disjoint_left.mp (hP hne)) hui huj
  subst j
  have he : s(u,v) = s(u,w) := hi.trans hj.symm
  rcases (Sym2.eq_iff.mp he) with h | h
  · exact h.2
  · exact False.elim (huv h.2.symm)

/-- In an edge-maximal massed counterexample, a root has at most one nonneighbor among the roots. -/
theorem root_missing_le_one_of_edge_maximal_bad_pair
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (X : Finset V) (α : ℝ) (hm : MassedPair G (X : Set V) α)
    {ι : Type*} (P : IndexedPairs ι V) (hP : P.DisjointTerminals)
    (hbad : ¬∃ L : IndexedLinkage G P, InteriorsAvoid L X)
    (hmax : ∀ u ∈ X, ∀ v ∈ X, u ≠ v → ¬G.Adj u v →
      MassedPair (G ⊔ SimpleGraph.fromEdgeSet {s(u,v)}) (X : Set V) α →
      ∃ L : IndexedLinkage (G ⊔ SimpleGraph.fromEdgeSet {s(u,v)}) P,
        InteriorsAvoid L X)
    (u : V) (hu : u ∈ X) :
    (X.erase u \ G.neighborFinset u).card ≤ 1 := by
  apply root_at_most_one_nonedge_of_pairable X P hP ?_ u hu
  intro x hx y hy hxy hnxy
  by_contra hnone
  have hother : ∀ i, s(x,y) ≠ s(P.start i,P.finish i) := by
    intro i he
    exact hnone ⟨i,he⟩
  have hbadH := fixed_pair_nonlinked_add_other_root_edge X x y hx hy hxy hother hbad
  have hmH := massed_add_root_edge X α hm x y hx hy
  exact hbadH (hmax x hx y hy hxy hnxy hmH)
/-- If the contracted vertex lies in the strict far shore, pulling back the shore gives a bound with one extra vertex. -/
theorem edgeContraction_shore_strictRight_relaxed {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) (X : Finset V) (α : ℝ)
    (hm : MassedPair G (X : Set V) α)
    (S : VertexSeparation (edgeContraction G hab))
    (hroot : (partitionIndex (edgeContractionPartition G hab) '' (X : Set V)) ⊆ S.left)
    (hsep : Nat.card S.separator <
      Nat.card (partitionIndex (edgeContractionPartition G hab) '' (X : Set V)))
    (hnone : none ∈ S.strictRight) :
    (edgeIncidenceSetCount (edgeContraction G hab) S.strictRight : ℝ) ≤
      α * ((Nat.card S.strictRight + 1 : ℕ) : ℝ) := by
  classical
  let P := edgeContractionPartition G hab
  let T := partitionPullbackSeparation P S
  have hrootT : (X : Set V) ⊆ T.left := by
    intro x hx
    exact hroot ⟨x, hx, rfl⟩
  have himage : Nat.card (partitionIndex P '' (X : Set V)) ≤
      Nat.card (X : Set V) := by
    let f : {x : V // x ∈ X} →
        {y : EdgeContractionVertex a b // y ∈ partitionIndex P '' (X : Set V)} :=
      fun x => ⟨partitionIndex P x.1, ⟨x.1, x.2, rfl⟩⟩
    have hsurj : Function.Surjective f := by
      rintro ⟨y, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_surjective f hsurj
  have hnoneSep : none ∉ S.separator := by
    intro hn
    exact hnone.2 hn.1
  have hsepT : Nat.card T.separator < Nat.card (X : Set V) := by
    have hcard : Nat.card T.separator = Nat.card S.separator := by
      exact edgeContraction_pullback_separator_card_away hab S hnoneSep
    have hsepP : Nat.card S.separator < Nat.card (partitionIndex P '' (X : Set V)) := by
      simpa [P] using hsep
    omega
  have hshore := hm.shore T hrootT hsepT
  have hfarT : T.strictRight = partitionIndex P ⁻¹' S.strictRight := by
    ext x
    rfl
  rw [hfarT] at hshore
  have hcardFar : Nat.card (partitionIndex P ⁻¹' S.strictRight) =
      Nat.card S.strictRight + 1 :=
    edgeContraction_preimage_card_of_mem_contract hab S.strictRight hnone
  rw [hcardFar] at hshore
  have hinc : edgeIncidenceSetCount (edgeContraction G hab) S.strictRight ≤
      edgeIncidenceSetCount G (partitionIndex P ⁻¹' S.strictRight) :=
    quotient_incidence_le_original P S.strictRight
  have hincR : (edgeIncidenceSetCount (edgeContraction G hab) S.strictRight : ℝ) ≤
      (edgeIncidenceSetCount G (partitionIndex P ⁻¹' S.strictRight) : ℝ) := by
    exact_mod_cast hinc
  exact hincR.trans hshore


/-- If the contracted vertex lies in the adhesion and expansion is still smaller than the root set, the quotient shore inequality holds. -/
theorem edgeContraction_shore_separator_small {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) (X : Finset V) (α : ℝ)
    (hm : MassedPair G (X : Set V) α)
    (S : VertexSeparation (edgeContraction G hab))
    (hroot : (partitionIndex (edgeContractionPartition G hab) '' (X : Set V)) ⊆ S.left)
    (hsep : Nat.card S.separator + 1 < Nat.card (X : Set V))
    (hnone : none ∈ S.separator) :
    (edgeIncidenceSetCount (edgeContraction G hab) S.strictRight : ℝ) ≤
      α * (Nat.card S.strictRight : ℝ) := by
  classical
  let P := edgeContractionPartition G hab
  let T := partitionPullbackSeparation P S
  have hrootT : (X : Set V) ⊆ T.left := by
    intro x hx
    exact hroot ⟨x,hx,rfl⟩
  have hsepT : Nat.card T.separator < Nat.card (X : Set V) := by
    have hcard : Nat.card T.separator = Nat.card S.separator + 1 := by
      exact edgeContraction_preimage_card_of_mem_contract hab S.separator hnone
    omega
  have hshore := hm.shore T hrootT hsepT
  have hfarT : T.strictRight = partitionIndex P ⁻¹' S.strictRight := by
    ext x
    rfl
  rw [hfarT] at hshore
  have hnoneFar : none ∉ S.strictRight := by
    intro h
    exact h.2 hnone.1
  have hcardFar : Nat.card (partitionIndex P ⁻¹' S.strictRight) =
      Nat.card S.strictRight :=
    edgeContraction_preimage_card_away hab S.strictRight hnoneFar
  rw [hcardFar] at hshore
  have hinc : edgeIncidenceSetCount (edgeContraction G hab) S.strictRight ≤
      edgeIncidenceSetCount G (partitionIndex P ⁻¹' S.strictRight) :=
    quotient_incidence_le_original P S.strictRight
  have hincR : (edgeIncidenceSetCount (edgeContraction G hab) S.strictRight : ℝ) ≤
      (edgeIncidenceSetCount G (partitionIndex P ⁻¹' S.strictRight) : ℝ) := by
    exact_mod_cast hinc
  exact hincR.trans hshore

/-- The common-neighbor bound (D.2) for any edge meeting the outside of the roots,
provided its contraction fails the strict global mass condition. -/
theorem common_neighbors_ge_of_contraction_mass_failure {G : SimpleGraph V}
    [DecidableRel G.Adj] {a b : V} (hab : G.Adj a b)
    (X : Finset V) (hb : b ∉ X) (r : ℕ)
    (hm : MassedPair G (X : Set V) (r : ℝ))
    (hmissing : ∀ x ∈ X, (X.erase x \ G.neighborFinset x).card ≤ 1) :
    let P := edgeContractionPartition G hab
    let Y : Set (EdgeContractionVertex a b) := partitionIndex P '' (X : Set V)
    (edgeIncidenceSetCount (edgeContraction G hab) Yᶜ : ℝ) ≤
      (r : ℝ) * ((Yᶜ).ncard : ℝ) →
      r - 1 ≤ (G.neighborFinset a ∩ G.neighborFinset b).card := by
  intro P Y hfail
  by_cases ha : a ∈ X
  · exact common_neighbors_ge_of_root_contraction_mass_failure hab X ha hb r hm
      hmissing hfail
  · exact common_neighbors_ge_of_exterior_contraction_mass_failure hab X ha hb r hm
      hfail
/-- An edge with at least r−1 common neighbors gives its endpoint degree at least r. -/
theorem degree_ge_of_common_neighbor_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (v u : V) (hvu : G.Adj v u) (r : ℕ) (hr : 0 < r)
    (hc : r - 1 ≤ (G.neighborFinset v ∩ G.neighborFinset u).card) :
    r ≤ G.degree v := by
  have hC : (G.neighborFinset v ∩ G.neighborFinset u).card =
      Fintype.card (G.commonNeighbors v u) := by
    classical
    rw [← Set.toFinset_card]
    congr 1
    ext x
    simp [SimpleGraph.commonNeighbors, SimpleGraph.mem_neighborFinset]
  have hlt := hvu.card_commonNeighbors_lt_degree
  rw [←hC] at hlt
  omega

/-- If each outside vertex has a neighbor and every exterior edge has many common neighbors, then all outside degrees are large. -/
theorem outside_degree_ge_of_common_neighbors
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (r : ℕ) (hr : 0 < r)
    (hneighbor : ∀ v ∉ X, ∃ u, G.Adj v u)
    (hcommon : ∀ v u, v ∉ X → G.Adj v u →
      r - 1 ≤ (G.neighborFinset v ∩ G.neighborFinset u).card) :
    ∀ v ∉ X, r ≤ G.degree v := by
  intro v hv
  obtain ⟨u,hvu⟩ := hneighbor v hv
  exact degree_ge_of_common_neighbor_edge G v u hvu r hr (hcommon v u hv hvu)
/-- Adding edges only among roots leaves incidence counts unchanged on sets disjoint from the roots. -/
theorem incidence_eq_of_root_extension
    {G H : SimpleGraph V} (X : Finset V) (S : Set V)
    (hGH : G ≤ H)
    (hnew : ∀ u v, H.Adj u v → ¬G.Adj u v → u ∈ X ∧ v ∈ X)
    (hSX : Disjoint S (X : Set V)) :
    edgeIncidenceSetCount H S = edgeIncidenceSetCount G S := by
  apply incidence_eq_of_agree_on_incident_edges S hGH
  intro e heH hinc
  induction e using Sym2.ind with | h u v =>
    have huv : H.Adj u v := (H.mem_edgeSet).mp heH
    by_cases hG : G.Adj u v
    · exact (G.mem_edgeSet).mpr hG
    · obtain ⟨huX,hvX⟩ := hnew u v huv hG
      obtain ⟨w,hwS,hwe⟩ := hinc
      have hwuv : w = u ∨ w = v := by simpa using hwe
      rcases hwuv with hwu | hwv
      · exact False.elim ((Set.disjoint_left.mp hSX) hwS (hwu ▸ huX))
      · exact False.elim ((Set.disjoint_left.mp hSX) hwS (hwv ▸ hvX))

/-- Arbitrary edge additions wholly inside the root set preserve massedness. -/
theorem massed_of_root_extension
    {G H : SimpleGraph V} (X : Finset V) (α : ℝ)
    (hGH : G ≤ H)
    (hnew : ∀ u v, H.Adj u v → ¬G.Adj u v → u ∈ X ∧ v ∈ X)
    (hm : MassedPair G (X : Set V) α) :
    MassedPair H (X : Set V) α := by
  refine ⟨?_, ?_⟩
  · have hdis : Disjoint (X : Set V)ᶜ (X : Set V) := by
      apply Set.disjoint_left.mpr
      intro x hx hX
      exact hx hX
    rw [incidence_eq_of_root_extension X (X : Set V)ᶜ hGH hnew hdis]
    exact hm.global
  · intro S hroot hsmall
    let T : VertexSeparation G := {
      left := S.left
      right := S.right
      cover := S.cover
      no_cross := by
        intro x y hxL hxNotR hyR hyNotL hG
        exact (S.no_cross hxL hxNotR hyR hyNotL) (hGH hG)
    }
    have hdis : Disjoint S.strictRight (X : Set V) := by
      apply Set.disjoint_left.mpr
      intro x hx hX
      exact hx.2 (hroot hX)
    have hcount := incidence_eq_of_root_extension X S.strictRight hGH hnew hdis
    have hshore := hm.shore T hroot hsmall
    rw [hcount]
    exact hshore

/-- Edges added among roots outside the prescribed pairs cannot repair a fixed bad pairing. -/
theorem fixed_pair_nonlinked_of_root_extension
    {G H : SimpleGraph V} (X : Finset V) {ι : Type*}
    (P : IndexedPairs ι V)
    (hnew : ∀ u v, H.Adj u v → ¬G.Adj u v →
      u ∈ X ∧ v ∈ X ∧ ∀ i, s(u,v) ≠ s(P.start i,P.finish i))
    (hbad : ¬∃ L : IndexedLinkage G P, InteriorsAvoid L X) :
    ¬∃ L : IndexedLinkage H P, InteriorsAvoid L X := by
  rintro ⟨L,hL⟩
  have hedge (i : ι) : ∀ e, e ∈ (L.path i : H.Walk (P.start i) (P.finish i)).edges →
      e ∈ G.edgeSet := by
    intro e he
    induction e using Sym2.ind with | h u v =>
      let p : H.Walk (P.start i) (P.finish i) := L.path i
      have heH : s(u,v) ∈ H.edgeSet := p.edges_subset_edgeSet he
      have huv : H.Adj u v := (H.mem_edgeSet).mp heH
      by_cases hG : G.Adj u v
      · exact (G.mem_edgeSet).mpr hG
      · obtain ⟨huX,hvX,hother⟩ := hnew u v huv hG
        exact False.elim ((hL.other_root_edge_not_used L X i u v huX hvX huv.ne
          (hother i)) he)
  let q (i : ι) : G.Path (P.start i) (P.finish i) :=
    ⟨(L.path i : H.Walk (P.start i) (P.finish i)).transfer G (hedge i),
      (L.path i).property.transfer (hedge i)⟩
  have hvertex (i : ι) : pathVertexSet (q i) = pathVertexSet (L.path i) := by
    ext x
    simp [q, pathVertexSet, SimpleGraph.Walk.support_transfer]
  let L' : IndexedLinkage G P := {
    path := q
    disjoint := by
      intro i j hij
      simpa only [hvertex] using L.disjoint hij
  }
  apply hbad
  refine ⟨L', ?_⟩
  intro i x hx hroot
  apply hL i x
  · simpa only [L', hvertex] using hx
  · exact hroot

/-- Complete all root edges except those prescribed by a fixed pairing. -/
def rootPairSaturation (G : SimpleGraph V) (X : Finset V)
    {ι : Type*} (P : IndexedPairs ι V) : SimpleGraph V where
  Adj u v := G.Adj u v ∨
    (u ≠ v ∧ u ∈ X ∧ v ∈ X ∧ ∀ i, s(u,v) ≠ s(P.start i,P.finish i))
  symm := by
    constructor
    intro u v h
    rcases h with hG | ⟨huv,huX,hvX,hother⟩
    · exact Or.inl hG.symm
    · right
      refine ⟨huv.symm,hvX,huX,?_⟩
      intro i he
      exact hother i (Sym2.eq_swap ▸ he)
  loopless := by
    constructor
    intro u h
    rcases h with hG | hNew
    · exact G.irrefl hG
    · exact hNew.1 rfl

/-- Root-pair saturation preserves both massedness and failure of the fixed pairing. -/
theorem rootPairSaturation_massed_bad
    {G : SimpleGraph V} (X : Finset V) {ι : Type*} (P : IndexedPairs ι V)
    (α : ℝ) (hm : MassedPair G (X : Set V) α)
    (hbad : ¬∃ L : IndexedLinkage G P, InteriorsAvoid L X) :
    MassedPair (rootPairSaturation G X P) (X : Set V) α ∧
      ¬∃ L : IndexedLinkage (rootPairSaturation G X P) P,
        InteriorsAvoid L X := by
  let H := rootPairSaturation G X P
  have hGH : G ≤ H := by
    intro u v h
    exact Or.inl h
  have hnew : ∀ u v, H.Adj u v → ¬G.Adj u v →
      u ∈ X ∧ v ∈ X ∧ ∀ i, s(u,v) ≠ s(P.start i,P.finish i) := by
    intro u v hH hnot
    rcases hH with hG | hAdded
    · exact False.elim (hnot hG)
    · exact ⟨hAdded.2.1,hAdded.2.2.1,hAdded.2.2.2⟩
  exact ⟨massed_of_root_extension X α hGH (fun u v hH hnot =>
    let h := hnew u v hH hnot
    ⟨h.1,h.2.1⟩) hm,
    fixed_pair_nonlinked_of_root_extension X P hnew hbad⟩

/-- Every root of the saturated graph has at most one nonneighbor in the root set. -/
theorem rootPairSaturation_missing
    (G : SimpleGraph V) (X : Finset V) {ι : Type*} (P : IndexedPairs ι V)
    (hP : P.DisjointTerminals)
    [DecidableRel (rootPairSaturation G X P).Adj]
    (u : V) (hu : u ∈ X) :
    (X.erase u \ (rootPairSaturation G X P).neighborFinset u).card ≤ 1 := by
  classical
  let H := rootPairSaturation G X P
  apply root_at_most_one_nonedge_of_pairable X P hP ?_ u hu
  intro x hx y hy hxy hnxy
  by_contra hnone
  have hother : ∀ i, s(x,y) ≠ s(P.start i,P.finish i) := by
    intro i he
    exact hnone ⟨i,he⟩
  have hAdj : H.Adj x y := Or.inr ⟨hxy,hx,hy,hother⟩
  exact hnxy hAdj

theorem incidence_induce_eq_of_support_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) [Fintype S] (hSupport : G.support ⊆ S) (U : Finset S) :
    edgeIncidenceCount (G.induce S) U =
      edgeIncidenceCount G (U.image Subtype.val) := by
  classical
  let f : Sym2 S ↪ Sym2 V := (Function.Embedding.subtype (· ∈ S)).sym2Map
  have hmap : (G.induce S).edgeFinset.map f = G.edgeFinset := by
    ext e
    constructor
    · intro he
      obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp he
      induction d using Sym2.ind with | h u v =>
        have huv : G.Adj (u : V) (v : V) :=
          ((G.induce S).mem_edgeFinset).mp hd
        exact G.mem_edgeFinset.mpr huv
    · intro he
      induction e using Sym2.ind with | h a b =>
        have hab : G.Adj a b := G.mem_edgeFinset.mp he
        let u : S := ⟨a, hSupport hab.mem_support_left⟩
        let v : S := ⟨b, hSupport hab.mem_support_right⟩
        apply Finset.mem_map.mpr
        refine ⟨s(u,v), ?_, rfl⟩
        exact (G.induce S).mem_edgeFinset.mpr hab
  have hfilter :
      ((G.induce S).edgeFinset.filter (fun e => ∃ u ∈ U, u ∈ e)).map f =
        G.edgeFinset.filter (fun e => ∃ v ∈ U.image Subtype.val, v ∈ e) := by
    ext e
    constructor
    · intro he
      obtain ⟨d, hd, hde⟩ := Finset.mem_map.mp he
      obtain ⟨hdG, u, huU, hud⟩ := Finset.mem_filter.mp hd
      have heG : e ∈ G.edgeFinset := by
        rw [←hmap]
        exact Finset.mem_map.mpr ⟨d, hdG, hde⟩
      refine Finset.mem_filter.mpr ⟨heG, ?_⟩
      refine ⟨(u : V), Finset.mem_image.mpr ⟨u,huU,rfl⟩, ?_⟩
      rw [←hde]
      exact Sym2.mem_map.mpr ⟨u,hud,rfl⟩
    · intro he
      obtain ⟨heG, v, hvU, hve⟩ := Finset.mem_filter.mp he
      obtain ⟨u,huU,huv⟩ := Finset.mem_image.mp hvU
      have heMap : e ∈ (G.induce S).edgeFinset.map f := by rw [hmap]; exact heG
      obtain ⟨d,hdG,hde⟩ := Finset.mem_map.mp heMap
      have hfu : (u : V) ∈ f d := by simpa [huv, hde] using hve
      obtain ⟨w,hwd,hwu⟩ := Sym2.mem_map.mp hfu
      have hwu' : w = u := Subtype.val_injective hwu
      subst w
      exact Finset.mem_map.mpr ⟨d,
        Finset.mem_filter.mpr ⟨hdG,⟨u,huU,hwd⟩⟩,hde⟩
  have hincH : edgeIncidenceCount (G.induce S) U =
      ((G.induce S).edgeFinset.filter (fun e => ∃ u ∈ U, u ∈ e)).card := by
    unfold edgeIncidenceCount
    congr 1
    ext e
    simp [SimpleGraph.mem_edgeFinset]
  have hincG : edgeIncidenceCount G (U.image Subtype.val) =
      (G.edgeFinset.filter (fun e => ∃ v ∈ U.image Subtype.val, v ∈ e)).card := by
    unfold edgeIncidenceCount
    congr 1
    ext e
    simp [SimpleGraph.mem_edgeFinset]
  rw [hincH, hincG]
  calc
    _ = (((G.induce S).edgeFinset.filter (fun e => ∃ u ∈ U, u ∈ e)).map f).card := by
      rw [Finset.card_map]
    _ = _ := congrArg Finset.card hfilter

/-- Incidence counts in an induced graph agree with ambient counts when all edges survive. -/
theorem incidenceSetCount_induce_eq_of_support_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) [Fintype S] (hSupport : G.support ⊆ S) (U : Set S) :
    edgeIncidenceSetCount (G.induce S) U =
      edgeIncidenceSetCount G (Subtype.val '' U) := by
  classical
  let T : Finset S := U.toFinset
  have hU : (T : Set S) = U := by ext u; simp [T]
  have hImage : ((T.image Subtype.val : Finset V) : Set V) =
      Subtype.val '' U := by
    ext v
    simp [T]
  rw [← hImage, ← hU,
    incidenceSetCount_eq_finsetCount,
    incidenceSetCount_eq_finsetCount]
  exact incidence_induce_eq_of_support_subset G S hSupport T

/-- A separation of an induced graph lifts when all edges are supported inside it. -/
def liftInducedSeparation (G : SimpleGraph V) (S : Set V)
    (hSupport : G.support ⊆ S)
    (A : VertexSeparation (G.induce S)) : VertexSeparation G where
  left := Sᶜ ∪ Subtype.val '' A.left
  right := Subtype.val '' A.right
  cover := by
    apply Set.eq_univ_iff_forall.mpr
    intro v
    by_cases hv : v ∈ S
    · have hcover : (⟨v,hv⟩ : S) ∈ A.left ∪ A.right := by
        rw [A.cover]
        trivial
      rcases hcover with hleft | hright
      · exact Or.inl (Or.inr ⟨⟨v,hv⟩,hleft,rfl⟩)
      · exact Or.inr ⟨⟨v,hv⟩,hright,rfl⟩
    · exact Or.inl (Or.inl hv)
  no_cross := by
    intro x y hxL hxNotR hyR hyNotL hxy
    have hxS : x ∈ S := hSupport hxy.mem_support_left
    have hyS : y ∈ S := hSupport hxy.mem_support_right
    have hxA : (⟨x,hxS⟩ : S) ∈ A.left := by
      rcases hxL with hxNotS | ⟨u,hu,hux⟩
      · exact False.elim (hxNotS hxS)
      · have hEq : u = ⟨x,hxS⟩ := Subtype.val_injective hux
        simpa [hEq] using hu
    have hxNotA : (⟨x,hxS⟩ : S) ∉ A.right := by
      intro h
      exact hxNotR ⟨⟨x,hxS⟩,h,rfl⟩
    obtain ⟨u,hu,huy⟩ := hyR
    have hEq : u = ⟨y,hyS⟩ := Subtype.val_injective huy
    have hyA : (⟨y,hyS⟩ : S) ∈ A.right := by simpa [hEq] using hu
    have hyNotA : (⟨y,hyS⟩ : S) ∉ A.left := by
      intro h
      exact hyNotL (Or.inr ⟨⟨y,hyS⟩,h,rfl⟩)
    exact A.no_cross hxA hxNotA hyA hyNotA hxy

theorem liftInducedSeparation_separator (G : SimpleGraph V) (S : Set V)
    (hSupport : G.support ⊆ S) (A : VertexSeparation (G.induce S)) :
    (liftInducedSeparation G S hSupport A).separator =
      Subtype.val '' A.separator := by
  ext v
  constructor
  · intro hv
    obtain ⟨hvL,hvR⟩ := hv
    obtain ⟨u,huR,huv⟩ := hvR
    have huL : u ∈ A.left := by
      rcases hvL with hvNotS | ⟨w,hwL,hwv⟩
      · exact False.elim (hvNotS (huv ▸ u.property))
      · have hwu : w = u := Subtype.val_injective (hwv.trans huv.symm)
        simpa [hwu] using hwL
    exact ⟨u,⟨huL,huR⟩,huv⟩
  · rintro ⟨u,⟨huL,huR⟩,huv⟩
    exact ⟨Or.inr ⟨u,huL,huv⟩,⟨u,huR,huv⟩⟩

theorem liftInducedSeparation_strictRight (G : SimpleGraph V) (S : Set V)
    (hSupport : G.support ⊆ S) (A : VertexSeparation (G.induce S)) :
    (liftInducedSeparation G S hSupport A).strictRight =
      Subtype.val '' A.strictRight := by
  ext v
  constructor
  · intro hv
    obtain ⟨⟨u,huR,huv⟩,hvNotL⟩ := hv
    have huNotL : u ∉ A.left := by
      intro h
      exact hvNotL (Or.inr ⟨u,h,huv⟩)
    exact ⟨u,⟨huR,huNotL⟩,huv⟩
  · rintro ⟨u,⟨huR,huNotL⟩,huv⟩
    refine ⟨⟨u,huR,huv⟩, ?_⟩
    rintro (hvNotS | ⟨w,hwL,hwv⟩)
    · exact hvNotS (huv ▸ u.property)
    · have hwu : w = u := Subtype.val_injective (hwv.trans huv.symm)
      exact huNotL (hwu ▸ hwL)

/-- Removing vertices outside the support does not change edge incidence on a set. -/
theorem incidence_inter_support_subset
    (G : SimpleGraph V) (S : Set V) (hSupport : G.support ⊆ S)
    (U : Set V) :
    edgeIncidenceSetCount G (U ∩ S) = edgeIncidenceSetCount G U := by
  have hEq : edgeIncidenceSet G (U ∩ S) = edgeIncidenceSet G U := by
    ext e
    constructor
    · rintro ⟨v,⟨hvU,_⟩,hve⟩
      exact ⟨v,hvU,hve⟩
    · rintro ⟨v,hvU,hve⟩
      have hvS : v ∈ S := by
        rcases e with ⟨d, hd⟩
        induction d using Sym2.ind with | h a b =>
          have hab : G.Adj a b := G.mem_edgeSet.mp hd
          have hvab : v = a ∨ v = b := by simpa using hve
          rcases hvab with rfl | rfl
          · exact hSupport hab.mem_support_left
          · exact hSupport hab.mem_support_right
      exact ⟨v,⟨hvU,hvS⟩,hve⟩
  unfold edgeIncidenceSetCount
  exact congrArg (fun T : Set G.edgeSet => Nat.card T) hEq

/-- Deleting unsupported vertices preserves the massed pair invariant. -/
theorem massed_induce_support_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S R : Set V) [Fintype S]
    (hSupport : G.support ⊆ S) (hRS : R ⊆ S)
    (α : ℝ) (hα : 0 ≤ α) (hm : MassedPair G R α) :
    MassedPair (G.induce S) {u : S | (u : V) ∈ R} α := by
  classical
  let Y : Set S := {u | (u : V) ∈ R}
  have hRoots : Subtype.val '' Y = R := by
    ext v
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact hu
    · intro hv
      exact ⟨⟨v,hRS hv⟩,hv,rfl⟩
  have hRootCard : Nat.card Y = Nat.card R := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, ← hRoots,
      Set.ncard_image_of_injective _ Subtype.val_injective]
  have hOutsideCard : Nat.card {u : S // u ∉ Y} ≤
      Nat.card {v : V // v ∉ R} := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    apply Fintype.card_le_of_injective
      (fun u : {u : S // u ∉ Y} => (⟨u.1.1, u.2⟩ : {v : V // v ∉ R}))
    intro u v huv
    have hval : (u.1 : V) = (v.1 : V) :=
      congrArg (fun q : {w : V // w ∉ R} => (q : V)) huv
    exact Subtype.ext (Subtype.ext hval)
  refine ⟨?_, ?_⟩
  · have hOutside : Subtype.val '' (Yᶜ : Set S) = Rᶜ ∩ S := by
      ext v
      constructor
      · rintro ⟨u,hu,rfl⟩
        exact ⟨hu,u.property⟩
      · rintro ⟨hvR,hvS⟩
        exact ⟨⟨v,hvS⟩,hvR,rfl⟩
    have hinc := incidenceSetCount_induce_eq_of_support_subset G S hSupport Yᶜ
    rw [hOutside, incidence_inter_support_subset G S hSupport Rᶜ] at hinc
    change α * (Nat.card {u : S // u ∉ Y} : ℝ) <
      (edgeIncidenceSetCount (G.induce S) Yᶜ : ℝ)
    rw [hinc]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by exact_mod_cast hOutsideCard) hα)
      hm.global
  · intro A hroot hsmall
    let T : VertexSeparation G := liftInducedSeparation G S hSupport A
    have hrootG : R ⊆ T.left := by
      intro v hvR
      have hvS : v ∈ S := hRS hvR
      exact Or.inr ⟨⟨v,hvS⟩,hroot hvR,rfl⟩
    have hSepCard : Nat.card T.separator = Nat.card A.separator := by
      rw [Nat.card_coe_set_eq,
        liftInducedSeparation_separator G S hSupport A,
        Set.ncard_image_of_injective _ Subtype.val_injective,
        Nat.card_coe_set_eq]
    have hsmallG : Nat.card T.separator < Nat.card R := by
      rw [hSepCard, ← hRootCard]
      exact hsmall
    have hshore := hm.shore T hrootG hsmallG
    rw [liftInducedSeparation_strictRight G S hSupport A] at hshore
    rw [Nat.card_coe_set_eq, Set.ncard_image_of_injective _ Subtype.val_injective,
      ← Nat.card_coe_set_eq] at hshore
    have hinc := incidenceSetCount_induce_eq_of_support_subset G S hSupport
      A.strictRight
    rw [hinc]
    exact hshore


/-- Removing an isolated nonroot vertex preserves massedness. -/
theorem massed_delete_isolated
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (α : ℝ) (hα : 0 ≤ α)
    (hm : MassedPair G (X : Set V) α)
    (z : V) (hz : z ∉ X) (hiso : ∀ u, ¬ G.Adj z u) :
    MassedPair (G.induce {v : V | v ≠ z})
      {u : {v : V | v ≠ z} | (u : V) ∈ X} α := by
  apply massed_induce_support_subset G {v : V | v ≠ z} (X : Set V)
    ?_ ?_ α hα hm
  · intro v hv hEq
    have hvAdj := G.mem_support.mp hv
    obtain ⟨u,hu⟩ := hvAdj
    subst v
    exact hiso u hu
  · intro v hv hEq
    exact hz (hEq ▸ hv)


/-- A nonlinked massed pair has no isolated outside vertex if all one-vertex
massed deletions are linked. -/
theorem outside_has_neighbor_of_linked_vertex_deletions
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (α : ℝ) (hα : 0 ≤ α)
    (hm : MassedPair G (X : Set V) α)
    (hbad : ¬ RootedLinked G X)
    (hminimal : ∀ z : V, z ∉ X →
      MassedPair (G.induce {v : V | v ≠ z})
        {u : {v : V | v ≠ z} | (u : V) ∈ X} α →
      RootedLinked (G.induce {v : V | v ≠ z})
        (Finset.univ.filter (fun u : {v : V | v ≠ z} => (u : V) ∈ X))) :
    ∀ z ∉ X, ∃ u, G.Adj z u := by
  classical
  intro z hz
  by_contra hnone
  push Not at hnone
  let S : Set V := {v | v ≠ z}
  let Y : Finset S := Finset.univ.filter (fun u : S => (u : V) ∈ X)
  have hmass : MassedPair (G.induce S) (Y : Set S) α := by
    have h := massed_delete_isolated G X α hα hm z hz hnone
    simpa [S,Y] using h
  have hlinked : RootedLinked (G.induce S) Y :=
    hminimal z hz (by simpa [S,Y] using hmass)
  have hXS : (X : Set V) ⊆ S := by
    intro v hv hEq
    exact hz (hEq ▸ hv)
  have hY : ∀ u : S, u ∈ Y ↔ (u : V) ∈ X := by
    intro u
    simp [Y]
  exact hbad (RootedLinked.of_induce G S X Y hXS hY hlinked)


/-- A root set with fewer than two vertices has no nontrivial pairing. -/
theorem rootedLinked_of_card_le_one (G : SimpleGraph V) (X : Finset V)
    (hX : X.card ≤ 1) : RootedLinked G X := by
  intro n P _ hne hPX
  have hn : n = 0 := by
    by_contra hn
    have hpos : 0 < n := by omega
    let i : Fin n := ⟨0, hpos⟩
    have ha : P.start i ∈ X := hPX i (by simp [IndexedPairs.terminals])
    have hb : P.finish i ∈ X := hPX i (by simp [IndexedPairs.terminals])
    have hsub : ({P.start i, P.finish i} : Finset V) ⊆ X := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact ha
      · have heq : v = P.finish i := by simpa using hv
        simpa [heq] using hb
    have htwo : ({P.start i, P.finish i} : Finset V).card = 2 := by
      simp [hne i]
    have hle := Finset.card_le_card hsub
    omega
  subst n
  let L : IndexedLinkage G P := {
    path := fun i => Fin.elim0 i
    disjoint := by intro i; exact Fin.elim0 i
  }
  exact ⟨L, by intro i; exact Fin.elim0 i⟩

/-- Any failure of rooted linkedness uses at least two roots. -/
theorem root_card_ge_two_of_not_rootedLinked (G : SimpleGraph V) (X : Finset V)
    (hbad : ¬ RootedLinked G X) : 2 ≤ X.card := by
  by_contra h
  have hX : X.card ≤ 1 := by omega
  exact hbad (rootedLinked_of_card_le_one G X hX)


/-- Failure of rooted linkedness is witnessed by one finite prescribed pairing. -/
theorem exists_bad_pairing_of_not_rootedLinked
    (G : SimpleGraph V) (X : Finset V)
    (hbad : ¬ RootedLinked G X) :
    ∃ n : ℕ, ∃ P : IndexedPairs (Fin n) V, P.DisjointTerminals ∧
      (∀ i, P.start i ≠ P.finish i) ∧
      (∀ i, P.terminals i ⊆ (X : Set V)) ∧
      ¬ ∃ L : IndexedLinkage G P, InteriorsAvoid L X := by
  unfold RootedLinked at hbad
  push Not at hbad
  obtain ⟨n, P, hP, hne, hX, hno⟩ := hbad
  exact ⟨n, P, hP, hne, hX, by rintro ⟨L, hL⟩; exact hno L hL⟩

/-- A neighbor of a strict far-side vertex remains in the right side. -/
theorem VertexSeparation.adj_right_of_strictRight
    {G : SimpleGraph V} (S : VertexSeparation G)
    {u v : V} (hu : u ∈ S.strictRight) (hAdj : G.Adj u v) :
    v ∈ S.right := by
  by_contra hvR
  have hvL : v ∈ S.left := by
    have hv := S.cover
    have hv' : v ∈ S.left ∪ S.right := by rw [hv]; trivial
    rcases hv' with h | h
    · exact h
    · exact False.elim (hvR h)
  exact S.no_cross hvL hvR hu.1 hu.2 hAdj.symm

/-- Edge incidence on a strict far-side set is unchanged by restricting to
the right side of a separation. -/
theorem incidenceCount_induce_right
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : VertexSeparation G) [Fintype S.right]
    (U : Finset S.right)
    (hU : ∀ u ∈ U, (u : V) ∉ S.left) :
    edgeIncidenceCount (G.induce S.right) U =
      edgeIncidenceCount G (U.image Subtype.val) := by
  classical
  let f : Sym2 S.right ↪ Sym2 V :=
    (Function.Embedding.subtype (· ∈ S.right)).sym2Map
  have hfilter :
      ((G.induce S.right).edgeFinset.filter (fun e => ∃ u ∈ U, u ∈ e)).map f =
        G.edgeFinset.filter (fun e => ∃ v ∈ U.image Subtype.val, v ∈ e) := by
    ext e
    constructor
    · intro he
      obtain ⟨d, hd, hde⟩ := Finset.mem_map.mp he
      obtain ⟨hdG, u, huU, hud⟩ := Finset.mem_filter.mp hd
      have heG : e ∈ G.edgeFinset := by
        rw [←hde]
        induction d using Sym2.ind with | h a b =>
          have hab : G.Adj (a : V) (b : V) :=
            ((G.induce S.right).mem_edgeFinset).mp hdG
          exact G.mem_edgeFinset.mpr hab
      refine Finset.mem_filter.mpr ⟨heG, ?_⟩
      refine ⟨(u : V), Finset.mem_image.mpr ⟨u,huU,rfl⟩, ?_⟩
      rw [←hde]
      exact Sym2.mem_map.mpr ⟨u,hud,rfl⟩
    · intro he
      obtain ⟨heG, v, hvU, hve⟩ := Finset.mem_filter.mp he
      obtain ⟨u,huU,huv⟩ := Finset.mem_image.mp hvU
      induction e using Sym2.ind with | h a b =>
        have hab : G.Adj a b := G.mem_edgeFinset.mp heG
        have huab : (u : V) = a ∨ (u : V) = b := by
          simpa [huv] using hve
        have haR : a ∈ S.right := by
          rcases huab with ha | hb
          · exact ha ▸ u.property
          · have hstrict : (u : V) ∈ S.strictRight := ⟨u.property,hU u huU⟩
            exact VertexSeparation.adj_right_of_strictRight S hstrict (hb ▸ hab.symm)
        have hbR : b ∈ S.right := by
          rcases huab with ha | hb
          · have hstrict : (u : V) ∈ S.strictRight := ⟨u.property,hU u huU⟩
            exact VertexSeparation.adj_right_of_strictRight S hstrict (ha ▸ hab)
          · exact hb ▸ u.property
        let a' : S.right := ⟨a,haR⟩
        let b' : S.right := ⟨b,hbR⟩
        have huD : u ∈ s(a',b') := by
          rcases huab with ha | hb
          · have hEq : u = a' := Subtype.ext ha
            simpa [hEq]
          · have hEq : u = b' := Subtype.ext hb
            simpa [hEq]
        have hdG : s(a',b') ∈ (G.induce S.right).edgeFinset :=
          (G.induce S.right).mem_edgeFinset.mpr hab
        exact Finset.mem_map.mpr ⟨s(a',b'),
          Finset.mem_filter.mpr ⟨hdG,⟨u,huU,huD⟩⟩,rfl⟩
  have hincH : edgeIncidenceCount (G.induce S.right) U =
      ((G.induce S.right).edgeFinset.filter (fun e => ∃ u ∈ U, u ∈ e)).card := by
    unfold edgeIncidenceCount
    congr 1
    ext e
    simp [SimpleGraph.mem_edgeFinset]
  have hincG : edgeIncidenceCount G (U.image Subtype.val) =
      (G.edgeFinset.filter (fun e => ∃ v ∈ U.image Subtype.val, v ∈ e)).card := by
    unfold edgeIncidenceCount
    congr 1
    ext e
    simp [SimpleGraph.mem_edgeFinset]
  rw [hincH,hincG]
  calc
    _ = (((G.induce S.right).edgeFinset.filter (fun e => ∃ u ∈ U, u ∈ e)).map f).card := by
      rw [Finset.card_map]
    _ = _ := congrArg Finset.card hfilter

/-- Set-level incidence equality on a separation's strict far shore. -/
theorem incidenceSetCount_induce_right
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : VertexSeparation G) [Fintype S.right]
    (U : Set S.right)
    (hU : ∀ u ∈ U, (u : V) ∉ S.left) :
    edgeIncidenceSetCount (G.induce S.right) U =
      edgeIncidenceSetCount G (Subtype.val '' U) := by
  classical
  let T : Finset S.right := U.toFinset
  have hUset : (T : Set S.right) = U := by ext u; simp [T]
  have hImage : ((T.image Subtype.val : Finset V) : Set V) =
      Subtype.val '' U := by
    ext v
    simp [T]
  rw [← hImage, ← hUset,
    incidenceSetCount_eq_finsetCount,
    incidenceSetCount_eq_finsetCount]
  apply incidenceCount_induce_right G S T
  intro u hu
  exact hU u (by simpa [T] using hu)


/-- A dense far shore becomes the global mass condition after restricting
to the far-side induced graph and rooting its separator. -/
theorem dense_far_shore_induced_global
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : VertexSeparation G) [Fintype S.right] (α : ℝ)
    (hdense : α * (Nat.card S.strictRight : ℝ) <
      (edgeIncidenceSetCount G S.strictRight : ℝ)) :
    let T : Set S.right := {u | (u : V) ∈ S.left}
    α * (Nat.card {u : S.right // u ∉ T} : ℝ) <
      (edgeIncidenceSetCount (G.induce S.right) Tᶜ : ℝ) := by
  intro T
  have hImage : Subtype.val '' Tᶜ = S.strictRight := by
    ext v
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u.property,hu⟩
    · rintro ⟨hvR,hvNotL⟩
      exact ⟨⟨v,hvR⟩,hvNotL,rfl⟩
  have hcard : Nat.card {u : S.right // u ∉ T} = Nat.card S.strictRight := by
    change Nat.card (Tᶜ : Set S.right) = Nat.card S.strictRight
    simp only [Nat.card_coe_set_eq]
    rw [← hImage, Set.ncard_image_of_injective _ Subtype.val_injective]
  have hinc := incidenceSetCount_induce_right G S Tᶜ (by
    intro u hu
    exact hu)
  rw [hImage] at hinc
  rw [hcard,hinc]
  exact hdense


/-- Glue a separation of the right induced graph back to the ambient graph
when the old adhesion lies on its near side. -/
def glueRightInduced {G : SimpleGraph V}
    (S : VertexSeparation G)
    (T : VertexSeparation (G.induce S.right))
    (hBoundary : ∀ u : S.right, (u : V) ∈ S.left → u ∈ T.left) :
    VertexSeparation G where
  left := S.left ∪ Subtype.val '' T.left
  right := Subtype.val '' T.right
  cover := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    have hxcover : x ∈ S.left ∪ S.right := by rw [S.cover]; trivial
    rcases hxcover with hxL | hxR
    · exact Or.inl (Or.inl hxL)
    · have ht : (⟨x,hxR⟩ : S.right) ∈ T.left ∪ T.right := by
        rw [T.cover]
        trivial
      rcases ht with htL | htR
      · exact Or.inl (Or.inr ⟨⟨x,hxR⟩,htL,rfl⟩)
      · exact Or.inr ⟨⟨x,hxR⟩,htR,rfl⟩
  no_cross := by
    intro x y hxL hxNR hyR hyNL hxy
    obtain ⟨yw,hyT,hyEq⟩ := hyR
    have hyS : y ∈ S.right := hyEq ▸ yw.property
    have hyNotSL : y ∉ S.left := by
      intro h
      exact hyNL (Or.inl h)
    have hyNotTL : (⟨y,hyS⟩ : S.right) ∉ T.left := by
      intro h
      exact hyNL (Or.inr ⟨⟨y,hyS⟩,h,rfl⟩)
    have hyTR : (⟨y,hyS⟩ : S.right) ∈ T.right := by
      have h : yw = ⟨y,hyS⟩ := Subtype.val_injective hyEq
      simpa [h] using hyT
    have crossT (hxS : x ∈ S.right)
        (hxT : (⟨x,hxS⟩ : S.right) ∈ T.left) : False := by
      have hxNotTR : (⟨x,hxS⟩ : S.right) ∉ T.right := by
        intro h
        exact hxNR ⟨⟨x,hxS⟩,h,rfl⟩
      exact T.no_cross hxT hxNotTR hyTR hyNotTL hxy
    rcases hxL with hxSL | ⟨xw,hxT,hxEq⟩
    · by_cases hxS : x ∈ S.right
      · exact crossT hxS (hBoundary ⟨x,hxS⟩ hxSL)
      · exact S.no_cross hxSL hxS hyS hyNotSL hxy
    · have hxS : x ∈ S.right := hxEq ▸ xw.property
      have h : xw = ⟨x,hxS⟩ := Subtype.val_injective hxEq
      exact crossT hxS (by simpa [h] using hxT)

/-- The glued boundary is the image of the right-side boundary. -/
theorem glueRightInduced_separator {G : SimpleGraph V}
    (S : VertexSeparation G) (T : VertexSeparation (G.induce S.right))
    (hBoundary : ∀ u : S.right, (u : V) ∈ S.left → u ∈ T.left) :
    (glueRightInduced S T hBoundary).separator =
      Subtype.val '' T.separator := by
  ext x
  constructor
  · rintro ⟨hxL,⟨u,huR,huEq⟩⟩
    have huL : u ∈ T.left := by
      rcases hxL with hxSL | ⟨w,hwL,hwEq⟩
      · exact hBoundary u (huEq ▸ hxSL)
      · have hwu : w = u := Subtype.val_injective (hwEq.trans huEq.symm)
        exact hwu ▸ hwL
    exact ⟨u,⟨huL,huR⟩,huEq⟩
  · rintro ⟨u,⟨huL,huR⟩,huEq⟩
    exact ⟨Or.inr ⟨u,huL,huEq⟩,⟨u,huR,huEq⟩⟩

/-- Gluing preserves adhesion order. -/
theorem glueRightInduced_separator_card {G : SimpleGraph V}
    (S : VertexSeparation G) (T : VertexSeparation (G.induce S.right))
    (hBoundary : ∀ u : S.right, (u : V) ∈ S.left → u ∈ T.left) :
    Nat.card (glueRightInduced S T hBoundary).separator =
      Nat.card T.separator := by
  rw [Nat.card_coe_set_eq,
    glueRightInduced_separator S T hBoundary,
    Set.ncard_image_of_injective _ Subtype.val_injective,
    Nat.card_coe_set_eq]

/-- The strict far shore of the glued separation is exactly the image of
the induced strict far shore. -/
theorem glueRightInduced_strictRight {G : SimpleGraph V}
    (S : VertexSeparation G) (T : VertexSeparation (G.induce S.right))
    (hBoundary : ∀ u : S.right, (u : V) ∈ S.left → u ∈ T.left) :
    (glueRightInduced S T hBoundary).strictRight =
      Subtype.val '' T.strictRight := by
  ext x
  constructor
  · rintro ⟨⟨u,huR,huEq⟩,hxNotL⟩
    have huNotL : u ∉ T.left := by
      intro h
      exact hxNotL (Or.inr ⟨u,h,huEq⟩)
    exact ⟨u,⟨huR,huNotL⟩,huEq⟩
  · rintro ⟨u,⟨huR,huNotL⟩,huEq⟩
    refine ⟨⟨u,huR,huEq⟩, ?_⟩
    rintro (hxSL | ⟨w,hwL,hwEq⟩)
    · exact huNotL (hBoundary u (huEq ▸ hxSL))
    · have hwu : w = u := Subtype.val_injective (hwEq.trans huEq.symm)
      exact huNotL (hwu ▸ hwL)

/-- Lower adhesion makes the glued right side a proper subset of the old one. -/
theorem glueRightInduced_right_proper {G : SimpleGraph V}
    (S : VertexSeparation G) (T : VertexSeparation (G.induce S.right))
    (hBoundary : ∀ u : S.right, (u : V) ∈ S.left → u ∈ T.left)
    (hsmall : Nat.card T.separator < Nat.card S.separator) :
    (glueRightInduced S T hBoundary).right ⊆ S.right ∧
      ∃ x ∈ S.right, x ∉ (glueRightInduced S T hBoundary).right := by
  let B : Set S.right := {u | (u : V) ∈ S.left}
  have hImg : Subtype.val '' B = S.separator := by
    ext v
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨hu,u.property⟩
    · rintro ⟨hvL,hvR⟩
      exact ⟨⟨v,hvR⟩,hvL,rfl⟩
  have hBcard : B.ncard = S.separator.ncard := by
    rw [← hImg, Set.ncard_image_of_injective _ Subtype.val_injective]
  have hnot : ¬ B ⊆ T.separator := by
    intro hsubset
    have hc := Set.ncard_le_ncard hsubset
    rw [hBcard] at hc
    simpa only [Nat.card_coe_set_eq] using (not_lt_of_ge hc hsmall)
  obtain ⟨u,huB,huNotSep⟩ := Set.not_subset.mp hnot
  have huNotRight : u ∉ T.right := by
    intro huR
    exact huNotSep ⟨hBoundary u huB,huR⟩
  constructor
  · rintro x ⟨w,hw,rfl⟩
    exact w.property
  · refine ⟨(u : V), u.property, ?_⟩
    rintro ⟨w,hw,hwu⟩
    have hEq : w = u := Subtype.val_injective hwu
    exact huNotRight (hEq ▸ hw)

/-- A violating shore minimal by right-side inclusion induces a smaller
massed pair rooted at its adhesion. -/
theorem massed_far_shore_of_minimal_violation
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Set V) (α : ℝ)
    (S : VertexSeparation G) [Fintype S.right]
    (hrootS : R ⊆ S.left)
    (hsepS : Nat.card S.separator < Nat.card R)
    (hdense : α * (Nat.card S.strictRight : ℝ) <
      (edgeIncidenceSetCount G S.strictRight : ℝ))
    (hmin : ∀ Q : VertexSeparation G,
      R ⊆ Q.left → Nat.card Q.separator < Nat.card R →
      Q.right ⊆ S.right → (∃ x ∈ S.right, x ∉ Q.right) →
      (edgeIncidenceSetCount G Q.strictRight : ℝ) ≤
        α * (Nat.card Q.strictRight : ℝ)) :
    MassedPair (G.induce S.right)
      {u : S.right | (u : V) ∈ S.left} α := by
  classical
  let Y : Set S.right := {u | (u : V) ∈ S.left}
  have hImg : Subtype.val '' Y = S.separator := by
    ext v
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨hu,u.property⟩
    · rintro ⟨hvL,hvR⟩
      exact ⟨⟨v,hvR⟩,hvL,rfl⟩
  have hYcard : Nat.card Y = Nat.card S.separator := by
    simp only [Nat.card_coe_set_eq]
    rw [← hImg, Set.ncard_image_of_injective _ Subtype.val_injective]
  refine ⟨?_, ?_⟩
  · exact dense_far_shore_induced_global G S α hdense
  · intro T hrootY hsmall
    have hBoundary : ∀ u : S.right, (u : V) ∈ S.left → u ∈ T.left := by
      intro u hu
      exact hrootY hu
    let Q : VertexSeparation G := glueRightInduced S T hBoundary
    have hrootQ : R ⊆ Q.left := by
      intro v hv
      exact Or.inl (hrootS hv)
    have hsepT : Nat.card T.separator < Nat.card S.separator := by
      rw [← hYcard]
      exact hsmall
    have hsepQ : Nat.card Q.separator < Nat.card R := by
      rw [glueRightInduced_separator_card S T hBoundary]
      exact lt_trans hsepT hsepS
    obtain ⟨hsubset,hproper⟩ :=
      glueRightInduced_right_proper S T hBoundary hsepT
    have hbound := hmin Q hrootQ hsepQ hsubset hproper
    rw [glueRightInduced_strictRight S T hBoundary] at hbound
    have hcard : Nat.card (Subtype.val '' T.strictRight) =
        Nat.card T.strictRight := by
      simp only [Nat.card_coe_set_eq]
      rw [Set.ncard_image_of_injective _ Subtype.val_injective]
    rw [hcard] at hbound
    have hinc := incidenceSetCount_induce_right G S T.strictRight (by
      intro u hu
      intro huS
      exact hu.2 (hBoundary u huS))
    rw [hinc]
    exact hbound

/-- Among dense violating shores, choose one with inclusion-minimal right side. -/
theorem exists_minimal_violating_shore
    (G : SimpleGraph V) (R : Set V) (α : ℝ)
    (hex : ∃ S : VertexSeparation G,
      R ⊆ S.left ∧ Nat.card S.separator < Nat.card R ∧
      α * (Nat.card S.strictRight : ℝ) <
        (edgeIncidenceSetCount G S.strictRight : ℝ)) :
    ∃ S : VertexSeparation G,
      R ⊆ S.left ∧ Nat.card S.separator < Nat.card R ∧
      α * (Nat.card S.strictRight : ℝ) <
        (edgeIncidenceSetCount G S.strictRight : ℝ) ∧
      ∀ Q : VertexSeparation G,
        R ⊆ Q.left → Nat.card Q.separator < Nat.card R →
        Q.right ⊆ S.right → (∃ x ∈ S.right, x ∉ Q.right) →
        (edgeIncidenceSetCount G Q.strictRight : ℝ) ≤
          α * (Nat.card Q.strictRight : ℝ) := by
  classical
  let P : ℕ → Prop := fun n => ∃ S : VertexSeparation G,
    R ⊆ S.left ∧ Nat.card S.separator < Nat.card R ∧
      α * (Nat.card S.strictRight : ℝ) <
        (edgeIncidenceSetCount G S.strictRight : ℝ) ∧
      Nat.card S.right = n
  have hP : ∃ n, P n := by
    obtain ⟨S,hroot,hsep,hdense⟩ := hex
    exact ⟨Nat.card S.right,S,hroot,hsep,hdense,rfl⟩
  obtain ⟨S,hroot,hsep,hdense,hcard⟩ := Nat.find_spec hP
  refine ⟨S,hroot,hsep,hdense,?_⟩
  intro Q hrootQ hsepQ hsub hproper
  by_contra hnot
  have hdenseQ : α * (Nat.card Q.strictRight : ℝ) <
      (edgeIncidenceSetCount G Q.strictRight : ℝ) := lt_of_not_ge hnot
  have hQ : P (Nat.card Q.right) :=
    ⟨Q,hrootQ,hsepQ,hdenseQ,rfl⟩
  have hss : Q.right ⊂ S.right := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨hsub, ?_⟩
    intro heq
    obtain ⟨x,hxS,hxNotQ⟩ := hproper
    exact hxNotQ (heq.symm ▸ hxS)
  have hlt : Nat.card Q.right < Nat.card S.right := by
    simpa only [Nat.card_coe_set_eq] using Set.ncard_lt_ncard hss
  have hmin : Nat.find hP ≤ Nat.card Q.right := Nat.find_min' hP hQ
  omega


/-- A dense shore with adhesion at most the original root order inherits massedness. -/
theorem massed_induced_far_shore_of_adhesion_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Set V) (α : ℝ)
    (hm : MassedPair G R α)
    (S : VertexSeparation G) [Fintype S.right]
    (hrootS : R ⊆ S.left)
    (hle : Nat.card S.separator ≤ Nat.card R)
    (hdense : α * (Nat.card S.strictRight : ℝ) <
      (edgeIncidenceSetCount G S.strictRight : ℝ)) :
    MassedPair (G.induce S.right)
      {u : S.right | (u : V) ∈ S.left} α := by
  classical
  let Y : Set S.right := {u | (u : V) ∈ S.left}
  have hImg : Subtype.val '' Y = S.separator := by
    ext v
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨hu,u.property⟩
    · rintro ⟨hvL,hvR⟩
      exact ⟨⟨v,hvR⟩,hvL,rfl⟩
  have hYcard : Nat.card Y = Nat.card S.separator := by
    simp only [Nat.card_coe_set_eq]
    rw [← hImg, Set.ncard_image_of_injective _ Subtype.val_injective]
  refine ⟨?_, ?_⟩
  · exact dense_far_shore_induced_global G S α hdense
  · intro T hrootY hsmall
    have hBoundary : ∀ u : S.right, (u : V) ∈ S.left → u ∈ T.left := by
      intro u hu
      exact hrootY hu
    let Q : VertexSeparation G := glueRightInduced S T hBoundary
    have hrootQ : R ⊆ Q.left := by
      intro v hv
      exact Or.inl (hrootS hv)
    have hsepQ : Nat.card Q.separator < Nat.card R := by
      rw [glueRightInduced_separator_card S T hBoundary]
      have hsepT : Nat.card T.separator < Nat.card S.separator := by
        rw [← hYcard]
        exact hsmall
      omega
    have hbound := hm.shore Q hrootQ hsepQ
    rw [glueRightInduced_strictRight S T hBoundary] at hbound
    have hcard : Nat.card (Subtype.val '' T.strictRight) =
        Nat.card T.strictRight := by
      simp only [Nat.card_coe_set_eq]
      rw [Set.ncard_image_of_injective _ Subtype.val_injective]
    rw [hcard] at hbound
    have hinc := incidenceSetCount_induce_right G S T.strictRight (by
      intro u hu
      intro huS
      exact hu.2 (hBoundary u huS))
    rw [hinc]
    exact hbound


noncomputable def separationBoundaryFinset
    {G : SimpleGraph V} (S : VertexSeparation G) : Finset S.right := by
  classical
  letI : Fintype S.right := Fintype.ofFinite S.right
  exact Finset.univ.filter (fun u : S.right => (u : V) ∈ S.left)

@[simp] theorem mem_separationBoundaryFinset
    {G : SimpleGraph V} (S : VertexSeparation G) (u : S.right) :
    u ∈ separationBoundaryFinset S ↔ (u : V) ∈ S.left := by
  simp [separationBoundaryFinset]


/-- There is no proper linked far shore of adhesion at most the root order. -/
def NoRigidSeparation (G : SimpleGraph V) (R : Set V) : Prop :=
  ∀ S : VertexSeparation G,
    R ⊆ S.left →
    S.strictRight.Nonempty →
    Nat.card S.separator ≤ Nat.card R →
    ¬ RootedLinked (G.induce S.right) (separationBoundaryFinset S)

/-- Any separation of order below the root set omits a root from its right side. -/
theorem right_card_lt_of_root_sep {G : SimpleGraph V}
    (R : Set V) (S : VertexSeparation G)
    (hroot : R ⊆ S.left)
    (hsep : Nat.card S.separator < Nat.card R) :
    Nat.card S.right < Fintype.card V := by
  classical
  have hnot : ¬ R ⊆ S.separator := by
    intro h
    have hc := Set.ncard_le_ncard h
    change R.ncard ≤ S.separator.ncard at hc
    simpa only [Nat.card_coe_set_eq] using (not_lt_of_ge hc hsep)
  obtain ⟨x,hxR,hxNotSep⟩ := Set.not_subset.mp hnot
  have hxNotRight : x ∉ S.right := by
    intro hx
    exact hxNotSep ⟨hroot hxR,hx⟩
  have hss : S.right ⊂ (Set.univ : Set V) := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨Set.subset_univ _, ?_⟩
    intro heq
    exact hxNotRight (heq.symm ▸ Set.mem_univ x)
  have hc := Set.ncard_lt_ncard hss
  change S.right.ncard < Fintype.card V
  simpa only [Set.ncard_univ, Nat.card_eq_fintype_card] using hc


/-- A smaller massed-pair principle makes the minimal dense violating shore linked. -/
theorem exists_linked_minimal_violating_shore
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Set V) (α : ℝ)
    (hsmall : ∀ S : VertexSeparation G,
      Nat.card S.right < Fintype.card V →
      Nat.card S.separator < Nat.card R →
      MassedPair (G.induce S.right)
        {u : S.right | (u : V) ∈ S.left} α →
      RootedLinked (G.induce S.right) (separationBoundaryFinset S))
    (hex : ∃ S : VertexSeparation G,
      R ⊆ S.left ∧ Nat.card S.separator < Nat.card R ∧
      α * (Nat.card S.strictRight : ℝ) <
        (edgeIncidenceSetCount G S.strictRight : ℝ)) :
    ∃ S : VertexSeparation G,
      R ⊆ S.left ∧ Nat.card S.separator < Nat.card R ∧
      α * (Nat.card S.strictRight : ℝ) <
        (edgeIncidenceSetCount G S.strictRight : ℝ) ∧
      RootedLinked (G.induce S.right) (separationBoundaryFinset S) := by
  classical
  obtain ⟨S,hroot,hsep,hdense,hmin⟩ :=
    exists_minimal_violating_shore G R α hex
  letI : Fintype S.right := Fintype.ofFinite S.right
  have hmS : MassedPair (G.induce S.right)
      {u : S.right | (u : V) ∈ S.left} α :=
    massed_far_shore_of_minimal_violation G R α S
      hroot hsep hdense hmin
  exact ⟨S,hroot,hsep,hdense,
    hsmall S (right_card_lt_of_root_sep R S hroot hsep) hsep hmS⟩


/-- A clique lies entirely on one closed side of every vertex separation. -/
theorem clique_on_one_separation_side
    {G : SimpleGraph V} (C : Set V)
    (hclique : C.Pairwise G.Adj)
    (S : VertexSeparation G) :
    C ⊆ S.left ∨ C ⊆ S.right := by
  by_cases hleft : C ⊆ S.left
  · exact Or.inl hleft
  · right
    obtain ⟨x,hxC,hxNotL⟩ := Set.not_subset.mp hleft
    have hxR : x ∈ S.right := by
      have hc : x ∈ S.left ∪ S.right := by rw [S.cover]; trivial
      exact hc.resolve_left hxNotL
    intro y hyC
    by_contra hyNotR
    have hyL : y ∈ S.left := by
      have hc : y ∈ S.left ∪ S.right := by rw [S.cover]; trivial
      exact hc.resolve_right hyNotR
    have hxy : x ≠ y := by
      intro heq
      exact hyNotR (heq ▸ hxR)
    exact S.no_cross hyL hyNotR hxR hxNotL
      (hclique hxC hyC hxy).symm


end Linkedness
end HadwigerLean
