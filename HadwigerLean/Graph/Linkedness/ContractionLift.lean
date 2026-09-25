import HadwigerLean.Graph.Linkedness.Massed

/-!
# Lifting rooted linkages through a single edge contraction

The preimage of a connected quotient vertex set is connected, since the
contraction blocks form a minor model. A quotient linkage therefore lifts
pathwise while preserving disjointness and root-interior avoidance.
-/

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A connected set in a touching quotient lifts to a connected union of
its partition blocks. -/
theorem connected_partition_preimage {I : Type*} {G : SimpleGraph V}
    (P : ConnectedPartition G I) (C : Set I)
    (hC : (P.touchingQuotient.induce C).Connected) :
    (G.induce (partitionIndex P ⁻¹' C)).Connected := by
  let M : MinorModel (SimpleGraph.completeGraph (Fin 1))
      P.touchingQuotient := {
    branch := fun _ => C
    connected := fun _ => hC
    disjoint := by
      intro i j hij
      exact (hij (Subsingleton.elim i j)).elim
    adjacent := by
      intro i j hij
      exact (hij (Subsingleton.elim i j)).elim
  }
  have h := (M.comp P.toMinorModel).connected 0
  change (G.induce {x | ∃ q ∈ C, x ∈ P.block q}).Connected at h
  have heq : partitionIndex P ⁻¹' C = {x | ∃ q ∈ C, x ∈ P.block q} := by
    ext x
    constructor
    · intro hx
      exact ⟨partitionIndex P x, hx, partitionIndex_mem P x⟩
    · rintro ⟨q, hq, hx⟩
      change partitionIndex P x ∈ C
      rw [partitionIndex_eq_of_mem P x q hx]
      exact hq
  rw [heq]
  exact h

/-- Lift a path between specified original endpoints through a connected
quotient set, keeping every lifted vertex over that set. -/
theorem exists_path_in_partition_preimage
    {I : Type*} {G : SimpleGraph V}
    (P : ConnectedPartition G I) (C : Set I)
    (hC : (P.touchingQuotient.induce C).Connected)
    {u v : V} (hu : partitionIndex P u ∈ C)
    (hv : partitionIndex P v ∈ C) :
    ∃ p : G.Path u v, pathVertexSet p ⊆ partitionIndex P ⁻¹' C := by
  let U : Set V := partitionIndex P ⁻¹' C
  have hU : (G.induce U).Connected :=
    connected_partition_preimage P C hC
  let u' : U := ⟨u, hu⟩
  let v' : U := ⟨v, hv⟩
  let p : (G.induce U).Path u' v' := (hU.preconnected u' v').some.toPath
  let q : G.Path u v := p.mapEmbedding (SimpleGraph.Embedding.induce U)
  refine ⟨q, ?_⟩
  intro x hx
  have hxmap : x ∈ (p : (G.induce U).Walk u' v').support.map Subtype.val := by
    change x ∈ ((p : (G.induce U).Walk u' v').map
      (SimpleGraph.Embedding.induce U).toHom).support at hx
    rw [SimpleGraph.Walk.support_map] at hx
    simpa using hx
  obtain ⟨z, _, hz⟩ := List.mem_map.mp hxmap
  exact hz ▸ z.property

/-- Rooted linkedness lifts through contraction of an edge whose second
endpoint is not a prescribed root. Quotient paths are lifted inside the
preimages of their support sets. -/
theorem rootedLinked_of_edgeContraction
    {G : SimpleGraph V} {a b : V} (hab : G.Adj a b)
    (X : Finset V) (hb : b ∉ X)
    (h : RootedLinked (edgeContraction G hab)
      (X.image (partitionIndex (edgeContractionPartition G hab)))) :
    RootedLinked G X := by
  classical
  let C := edgeContractionPartition G hab
  let f : V → EdgeContractionVertex a b := partitionIndex C
  have hfinj : Set.InjOn f (X : Set V) := by
    exact edgeContraction_index_injOn_roots hab X hb
  intro n P hP hne hterm
  let PQ : IndexedPairs (Fin n) (EdgeContractionVertex a b) := {
    start := f ∘ P.start
    finish := f ∘ P.finish
  }
  have hterm_lift (i : Fin n) {q : EdgeContractionVertex a b}
      (hq : q ∈ PQ.terminals i) :
      ∃ x ∈ P.terminals i, f x = q := by
    change q ∈ ({f (P.start i), f (P.finish i)} :
      Set (EdgeContractionVertex a b)) at hq
    rcases hq with hq | hq
    · exact ⟨P.start i, by simp [IndexedPairs.terminals], hq.symm⟩
    · exact ⟨P.finish i, by simp [IndexedPairs.terminals], hq.symm⟩
  have hPQdisj : PQ.DisjointTerminals := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro q hqi hqj
    obtain ⟨x, hxi, hfx⟩ := hterm_lift i hqi
    obtain ⟨y, hyj, hfy⟩ := hterm_lift j hqj
    have hxy : x = y := hfinj (hterm i hxi) (hterm j hyj)
      (hfx.trans hfy.symm)
    exact (Set.disjoint_left.mp (hP hij)) hxi (hxy ▸ hyj)
  have hPQne : ∀ i, PQ.start i ≠ PQ.finish i := by
    intro i hi
    have hs : P.start i ∈ X := hterm i (by simp [IndexedPairs.terminals])
    have ht : P.finish i ∈ X := hterm i (by simp [IndexedPairs.terminals])
    exact hne i (hfinj hs ht hi)
  have hPQterm : ∀ i, PQ.terminals i ⊆
      (X.image f : Set (EdgeContractionVertex a b)) := by
    intro i q hq
    obtain ⟨x, hx, rfl⟩ := hterm_lift i hq
    exact Finset.mem_image.mpr ⟨x, hterm i hx, rfl⟩
  obtain ⟨LQ, havoidQ⟩ := h n PQ hPQdisj hPQne hPQterm
  have hpath : ∀ i : Fin n,
      ∃ p : G.Path (P.start i) (P.finish i),
        pathVertexSet p ⊆ f ⁻¹' pathVertexSet (LQ.path i) := by
    intro i
    have hc : (C.touchingQuotient.induce
        (pathVertexSet (LQ.path i))).Connected := by
      exact (LQ.path i : (edgeContraction G hab).Walk
        (PQ.start i) (PQ.finish i)).connected_induce_support
    apply exists_path_in_partition_preimage C
      (pathVertexSet (LQ.path i)) hc
    · exact pathVertexSet.start_mem (LQ.path i)
    · exact pathVertexSet.finish_mem (LQ.path i)
  let p (i : Fin n) : G.Path (P.start i) (P.finish i) :=
    Classical.choose (hpath i)
  have hp (i : Fin n) :
      pathVertexSet (p i) ⊆ f ⁻¹' pathVertexSet (LQ.path i) :=
    Classical.choose_spec (hpath i)
  let L : IndexedLinkage G P := {
    path := p
    disjoint := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro x hxi hxj
      exact (Set.disjoint_left.mp (LQ.disjoint hij))
        (hp i hxi) (hp j hxj)
  }
  refine ⟨L, ?_⟩
  intro i x hx hxX
  have hfx : f x ∈ pathVertexSet (LQ.path i) := hp i hx
  have hfxX : f x ∈ X.image f := Finset.mem_image.mpr ⟨x, hxX, rfl⟩
  have hqterm : f x ∈ PQ.terminals i :=
    havoidQ i (f x) hfx hfxX
  obtain ⟨y, hy, hfy⟩ := hterm_lift i hqterm
  have hxy : x = y := hfinj hxX (hterm i hy) hfy.symm
  exact hxy ▸ hy
/-- Lift a connected quotient set into any larger induced shore. -/
theorem exists_path_in_partition_preimage_induce
    {I : Type*} {G : SimpleGraph V}
    (P : ConnectedPartition G I) (U C : Set I) (hCU : C ⊆ U)
    (hC : (P.touchingQuotient.induce C).Connected)
    {u v : V} (hu : partitionIndex P u ∈ C)
    (hv : partitionIndex P v ∈ C) :
    ∃ p : (G.induce (partitionIndex P ⁻¹' U)).Path
      ⟨u, hCU hu⟩ ⟨v, hCU hv⟩,
      ∀ x ∈ pathVertexSet p, partitionIndex P (x : V) ∈ C := by
  obtain ⟨p,hp⟩ := exists_path_in_partition_preimage P C hC hu hv
  have hU : ∀ x ∈ (p : G.Walk u v).support, x ∈ partitionIndex P ⁻¹' U := by
    intro x hx
    exact hCU (hp hx)
  let q : (G.induce (partitionIndex P ⁻¹' U)).Path
      ⟨u, hU u (p : G.Walk u v).start_mem_support⟩
      ⟨v, hU v (p : G.Walk u v).end_mem_support⟩ :=
    ⟨(p : G.Walk u v).induce (partitionIndex P ⁻¹' U) hU, by
      have hmap : (((p : G.Walk u v).induce (partitionIndex P ⁻¹' U) hU).map
          (SimpleGraph.Embedding.induce _).toHom).IsPath := by
        rw [SimpleGraph.Walk.map_induce]
        exact p.property
      exact SimpleGraph.Walk.IsPath.of_map hmap⟩
  have hqs : ∀ x, x ∈ pathVertexSet q →
      partitionIndex P (x : V) ∈ C := by
    intro x hx
    have hxmap : (x : V) ∈
        (q.val.map
          (SimpleGraph.Embedding.induce _).toHom).support := by
      rw [SimpleGraph.Walk.support_map]
      exact List.mem_map.mpr ⟨x,hx,rfl⟩
    have hxold : (x : V) ∈ (p : G.Walk u v).support := by
      change (x : V) ∈ (((p : G.Walk u v).induce
        (partitionIndex P ⁻¹' U) hU).map
          (SimpleGraph.Embedding.induce _).toHom).support at hxmap
      rw [SimpleGraph.Walk.map_induce] at hxmap
      exact hxmap
    exact hp hxold
  exact ⟨q, hqs⟩


/-- Rooted linkedness inside a quotient shore lifts into its full preimage. -/
theorem rootedLinked_of_partition_induce
    {I : Type*} {G : SimpleGraph V}
    (C : ConnectedPartition G I) (U : Set I)
    (X : Finset (partitionIndex C ⁻¹' U))
    (Z : Finset U)
    (hinj : Set.InjOn
      (fun x : partitionIndex C ⁻¹' U =>
        (⟨partitionIndex C (x : V), x.property⟩ : U))
      (X : Set (partitionIndex C ⁻¹' U)))
    (hroots : ∀ x ∈ X,
      (⟨partitionIndex C (x : V), x.property⟩ : U) ∈ Z)
    (hlinked : RootedLinked (C.touchingQuotient.induce U) Z) :
    RootedLinked (G.induce (partitionIndex C ⁻¹' U)) X := by
  classical
  let f : (partitionIndex C ⁻¹' U) → U :=
    fun x => ⟨partitionIndex C (x : V), x.property⟩
  intro n P hP hne hterm
  let PQ : IndexedPairs (Fin n) U := {
    start := f ∘ P.start
    finish := f ∘ P.finish
  }
  have hterm_lift (i : Fin n) {q : U}
      (hq : q ∈ PQ.terminals i) :
      ∃ x ∈ P.terminals i, f x = q := by
    change q ∈ ({f (P.start i), f (P.finish i)} : Set U) at hq
    rcases hq with hq | hq
    · exact ⟨P.start i, by simp [IndexedPairs.terminals], hq.symm⟩
    · exact ⟨P.finish i, by simp [IndexedPairs.terminals], hq.symm⟩
  have hPQdisj : PQ.DisjointTerminals := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro q hqi hqj
    obtain ⟨x,hxi,hfx⟩ := hterm_lift i hqi
    obtain ⟨y,hyj,hfy⟩ := hterm_lift j hqj
    have hxy : x = y := hinj (hterm i hxi) (hterm j hyj)
      (hfx.trans hfy.symm)
    exact (Set.disjoint_left.mp (hP hij)) hxi (hxy ▸ hyj)
  have hPQne : ∀ i, PQ.start i ≠ PQ.finish i := by
    intro i hi
    have hs : P.start i ∈ X := hterm i (by simp [IndexedPairs.terminals])
    have ht : P.finish i ∈ X := hterm i (by simp [IndexedPairs.terminals])
    exact hne i (hinj hs ht hi)
  have hPQterm : ∀ i, PQ.terminals i ⊆ (Z : Set U) := by
    intro i q hq
    obtain ⟨x,hx,rfl⟩ := hterm_lift i hq
    exact hroots x (hterm i hx)
  obtain ⟨LQ, havoidQ⟩ := hlinked n PQ hPQdisj hPQne hPQterm
  let q (i : Fin n) : C.touchingQuotient.Path
      (partitionIndex C (P.start i).val)
      (partitionIndex C (P.finish i).val) :=
    (LQ.path i).mapEmbedding (SimpleGraph.Embedding.induce U)
  let D (i : Fin n) : Set I := pathVertexSet (q i)
  have hDU (i : Fin n) : D i ⊆ U := by
    intro z hz
    have hzmap : z ∈
        (LQ.path i : (C.touchingQuotient.induce U).Walk
          (PQ.start i) (PQ.finish i)).support.map Subtype.val := by
      change z ∈ ((LQ.path i : (C.touchingQuotient.induce U).Walk
        (PQ.start i) (PQ.finish i)).map
          (SimpleGraph.Embedding.induce U).toHom).support at hz
      rw [SimpleGraph.Walk.support_map] at hz
      exact hz
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hzmap
    exact w.property
  have hmem (i : Fin n) (x : partitionIndex C ⁻¹' U)
      (hx : partitionIndex C (x : V) ∈ D i) :
      f x ∈ pathVertexSet (LQ.path i) := by
    have hxmap : partitionIndex C (x : V) ∈
        (LQ.path i : (C.touchingQuotient.induce U).Walk
          (PQ.start i) (PQ.finish i)).support.map Subtype.val := by
      change partitionIndex C (x : V) ∈
        ((LQ.path i : (C.touchingQuotient.induce U).Walk
          (PQ.start i) (PQ.finish i)).map
          (SimpleGraph.Embedding.induce U).toHom).support at hx
      rw [SimpleGraph.Walk.support_map] at hx
      exact hx
    obtain ⟨w,hw,hval⟩ := List.mem_map.mp hxmap
    have hwf : w = f x := Subtype.val_injective hval
    exact hwf ▸ hw
  have hpath : ∀ i : Fin n,
      ∃ p : (G.induce (partitionIndex C ⁻¹' U)).Path
        (P.start i) (P.finish i),
        ∀ x ∈ pathVertexSet p, partitionIndex C (x : V) ∈ D i := by
    intro i
    have hc : (C.touchingQuotient.induce (D i)).Connected := by
      change (C.touchingQuotient.induce
        {z | z ∈ (q i).val.support}).Connected
      exact (q i).val.connected_induce_support
    have hs : partitionIndex C (P.start i).val ∈ D i :=
      pathVertexSet.start_mem (q i)
    have ht : partitionIndex C (P.finish i).val ∈ D i :=
      pathVertexSet.finish_mem (q i)
    exact exists_path_in_partition_preimage_induce C U (D i)
      (hDU i) hc hs ht
  let p (i : Fin n) : (G.induce (partitionIndex C ⁻¹' U)).Path
      (P.start i) (P.finish i) := Classical.choose (hpath i)
  have hp (i : Fin n) :
      ∀ x ∈ pathVertexSet (p i), partitionIndex C (x : V) ∈ D i :=
    Classical.choose_spec (hpath i)
  let L : IndexedLinkage (G.induce (partitionIndex C ⁻¹' U)) P := {
    path := p
    disjoint := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro x hxi hxj
      exact (Set.disjoint_left.mp (LQ.disjoint hij))
        (hmem i x (hp i x hxi)) (hmem j x (hp j x hxj))
  }
  refine ⟨L, ?_⟩
  intro i x hx hxX
  have hfx : f x ∈ pathVertexSet (LQ.path i) :=
    hmem i x (hp i x hx)
  have hfxX : f x ∈ Z := hroots x hxX
  have hqterm : f x ∈ PQ.terminals i :=
    havoidQ i (f x) hfx hfxX
  obtain ⟨y,hy,hfy⟩ := hterm_lift i hqterm
  have hxy : x = y := hinj hxX (hterm i hy) hfy.symm
  exact hxy ▸ hy


/-- A linked quotient shore whose contracted vertex is strict-far lifts to a linked original shore. -/
theorem rootedLinked_contraction_strictFar_induce
    {G : SimpleGraph V} {a b : V} (hab : G.Adj a b)
    (S : VertexSeparation (edgeContraction G hab))
    (hnone : none ∈ S.strictRight)
    (hlinked : RootedLinked ((edgeContraction G hab).induce S.right)
      (separationBoundaryFinset S)) :
    let C := edgeContractionPartition G hab
    let T := partitionPullbackSeparation C S
    RootedLinked (G.induce T.right) (separationBoundaryFinset T) := by
  classical
  intro C T
  have hnoneSep : none ∉ S.separator := by
    intro h
    exact hnone.2 h.1
  have hinj : Set.InjOn
      (fun x : T.right =>
        (⟨partitionIndex C (x : V), x.property⟩ : S.right))
      (separationBoundaryFinset T : Set T.right) := by
    intro x hx y hy hxy
    apply Subtype.ext
    apply edgeContraction_index_inj_away hab
    · intro hidx
      have hxL : partitionIndex C (x : V) ∈ S.left :=
        (mem_separationBoundaryFinset T x).mp hx
      exact hnoneSep (hidx ▸ ⟨hxL,x.property⟩)
    · exact congrArg Subtype.val hxy
  have hroots : ∀ x ∈ separationBoundaryFinset T,
      (⟨partitionIndex C (x : V), x.property⟩ : S.right) ∈
        separationBoundaryFinset S := by
    intro x hx
    apply (mem_separationBoundaryFinset S _).mpr
    exact (mem_separationBoundaryFinset T x).mp hx
  exact rootedLinked_of_partition_induce C S.right
    (separationBoundaryFinset T) (separationBoundaryFinset S)
    hinj hroots hlinked


/-- A linked strict-far quotient shore contradicts the absence of rigid original shores. -/
theorem no_linked_contraction_strictFar
    {G : SimpleGraph V} {a b : V} (hab : G.Adj a b)
    (R : Set V) (hno : NoRigidSeparation G R)
    (S : VertexSeparation (edgeContraction G hab))
    (hroot : R ⊆ (partitionPullbackSeparation
      (edgeContractionPartition G hab) S).left)
    (hsep : Nat.card S.separator ≤ Nat.card R)
    (hnone : none ∈ S.strictRight)
    (hlinked : RootedLinked ((edgeContraction G hab).induce S.right)
      (separationBoundaryFinset S)) : False := by
  let C := edgeContractionPartition G hab
  let T := partitionPullbackSeparation C S
  have hnoneSep : none ∉ S.separator := by
    intro h
    exact hnone.2 h.1
  have hcard : Nat.card T.separator = Nat.card S.separator :=
    edgeContraction_pullback_separator_card_away hab S hnoneSep
  have hTfar : T.strictRight.Nonempty := by
    refine ⟨a, ?_⟩
    constructor
    · change partitionIndex C a ∈ S.right
      rw [edgeContraction_index_left hab]
      exact hnone.1
    · change partitionIndex C a ∉ S.left
      rw [edgeContraction_index_left hab]
      exact hnone.2
  have hTlinked : RootedLinked (G.induce T.right)
      (separationBoundaryFinset T) :=
    rootedLinked_contraction_strictFar_induce hab S hnone hlinked
  exact hno T hroot hTfar (hcard.trans_le hsep) hTlinked


/-- A dense contraction shore with the contracted vertex in its separator expands to a massed original shore. -/
theorem massed_contraction_separator_shore
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} (hab : G.Adj a b)
    (X : Finset V) (α : ℝ)
    (hm : MassedPair G (X : Set V) α)
    (S : VertexSeparation (edgeContraction G hab))
    (hroot : (partitionIndex (edgeContractionPartition G hab) '' (X : Set V)) ⊆ S.left)
    (hsep : Nat.card S.separator <
      Nat.card (partitionIndex (edgeContractionPartition G hab) '' (X : Set V)))
    (hnone : none ∈ S.separator)
    (hdense : α * (Nat.card S.strictRight : ℝ) <
      (edgeIncidenceSetCount (edgeContraction G hab) S.strictRight : ℝ)) :
    let C := edgeContractionPartition G hab
    let T := partitionPullbackSeparation C S
    MassedPair (G.induce T.right)
      {u : T.right | (u : V) ∈ T.left} α := by
  classical
  intro C T
  have hrootT : (X : Set V) ⊆ T.left := by
    intro x hx
    exact hroot ⟨x,hx,rfl⟩
  have hsizeImage : Nat.card (partitionIndex C '' (X : Set V)) ≤
      Nat.card (X : Set V) := by
    change (partitionIndex C '' (X : Set V)).ncard ≤ (X : Set V).ncard
    exact Set.ncard_image_le (Set.toFinite (X : Set V))
  have hle : Nat.card T.separator ≤ Nat.card (X : Set V) := by
    change Nat.card S.separator <
      Nat.card (partitionIndex C '' (X : Set V)) at hsep
    have hcard : Nat.card T.separator = Nat.card S.separator + 1 :=
      edgeContraction_preimage_card_of_mem_contract hab S.separator hnone
    omega
  have hfarT : T.strictRight = partitionIndex C ⁻¹' S.strictRight := by
    ext x
    rfl
  have hnoneFar : none ∉ S.strictRight := by
    intro h
    exact h.2 hnone.1
  have hcardFar : Nat.card T.strictRight = Nat.card S.strictRight := by
    rw [hfarT]
    exact edgeContraction_preimage_card_away hab S.strictRight hnoneFar
  have hinc : (edgeIncidenceSetCount (edgeContraction G hab) S.strictRight : ℝ) ≤
      (edgeIncidenceSetCount G T.strictRight : ℝ) := by
    have hc := quotient_incidence_le_original C S.strictRight
    rw [hfarT]
    exact_mod_cast hc
  have hdenseT : α * (Nat.card T.strictRight : ℝ) <
      (edgeIncidenceSetCount G T.strictRight : ℝ) := by
    rw [hcardFar]
    exact lt_of_lt_of_le hdense hinc
  letI : Fintype T.right := Fintype.ofFinite T.right
  exact massed_induced_far_shore_of_adhesion_le G (X : Set V) α
    hm T hrootT hle hdenseT


/-- A sub-root-order quotient separator leaves an original root outside its pulled-back right side. -/
theorem contraction_pullback_right_card_lt_of_root_sep
    {G : SimpleGraph V} {a b : V} (hab : G.Adj a b)
    (X : Finset V)
    (S : VertexSeparation (edgeContraction G hab))
    (hroot : (partitionIndex (edgeContractionPartition G hab) '' (X : Set V)) ⊆ S.left)
    (hsep : Nat.card S.separator <
      Nat.card (partitionIndex (edgeContractionPartition G hab) '' (X : Set V))) :
    Nat.card (partitionPullbackSeparation (edgeContractionPartition G hab) S).right <
      Fintype.card V := by
  classical
  let C := edgeContractionPartition G hab
  let T := partitionPullbackSeparation C S
  let Y : Set (EdgeContractionVertex a b) := partitionIndex C '' (X : Set V)
  have hnot : ¬ Y ⊆ S.separator := by
    intro h
    have hc := Set.ncard_le_ncard h
    change Nat.card Y ≤ Nat.card S.separator at hc
    change Nat.card S.separator < Nat.card Y at hsep
    omega
  obtain ⟨q,hqY,hqNotSep⟩ := Set.not_subset.mp hnot
  have hqY' := hqY
  obtain ⟨x,hxX,hxeq⟩ := hqY
  have hxNotRight : x ∉ T.right := by
    intro hx
    have hqR : q ∈ S.right := hxeq ▸ hx
    have hqL : q ∈ S.left := hroot hqY'
    exact hqNotSep ⟨hqL,hqR⟩
  have hss : T.right ⊂ (Set.univ : Set V) := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨Set.subset_univ _, ?_⟩
    intro heq
    exact hxNotRight (heq.symm ▸ Set.mem_univ x)
  have hc := Set.ncard_lt_ncard hss
  change T.right.ncard < Fintype.card V
  simpa only [Set.ncard_univ, Nat.card_eq_fintype_card] using hc


/-- A dense violating contraction shore with contracted vertex on its boundary is forbidden by minimality and absence of rigid shores. -/
theorem no_violating_contraction_separator
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} (hab : G.Adj a b)
    (X : Finset V) (α : ℝ)
    (hm : MassedPair G (X : Set V) α)
    (hno : NoRigidSeparation G (X : Set V))
    (hsmall : ∀ T : VertexSeparation G,
      Nat.card T.right < Fintype.card V →
      Nat.card T.separator ≤ X.card →
      MassedPair (G.induce T.right)
        {u : T.right | (u : V) ∈ T.left} α →
      RootedLinked (G.induce T.right) (separationBoundaryFinset T))
    (S : VertexSeparation (edgeContraction G hab))
    (hroot : (partitionIndex (edgeContractionPartition G hab) '' (X : Set V)) ⊆ S.left)
    (hsep : Nat.card S.separator <
      Nat.card (partitionIndex (edgeContractionPartition G hab) '' (X : Set V)))
    (hnone : none ∈ S.separator)
    (hdense : α * (Nat.card S.strictRight : ℝ) <
      (edgeIncidenceSetCount (edgeContraction G hab) S.strictRight : ℝ)) : False := by
  classical
  let C := edgeContractionPartition G hab
  let T := partitionPullbackSeparation C S
  have hmT : MassedPair (G.induce T.right)
      {u : T.right | (u : V) ∈ T.left} α :=
    massed_contraction_separator_shore hab X α hm S hroot hsep hnone hdense
  have horder : Nat.card T.right < Fintype.card V :=
    contraction_pullback_right_card_lt_of_root_sep hab X S hroot hsep


  have hrootT : (X : Set V) ⊆ T.left := by
    intro x hx
    exact hroot ⟨x,hx,rfl⟩
  have hsizeImage : Nat.card (partitionIndex C '' (X : Set V)) ≤
      Nat.card (X : Set V) := by
    change (partitionIndex C '' (X : Set V)).ncard ≤ (X : Set V).ncard
    exact Set.ncard_image_le (Set.toFinite (X : Set V))
  have hsepT : Nat.card T.separator ≤ Nat.card (X : Set V) := by
    change Nat.card S.separator <
      Nat.card (partitionIndex C '' (X : Set V)) at hsep
    have hcard : Nat.card T.separator = Nat.card S.separator + 1 :=
      edgeContraction_preimage_card_of_mem_contract hab S.separator hnone
    omega
  have hlinked : RootedLinked (G.induce T.right)
      (separationBoundaryFinset T) := hsmall T horder (by simpa using hsepT) hmT
  have hSfar : S.strictRight.Nonempty := by
    by_contra hn
    have he : S.strictRight = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    rw [he] at hdense
    simp [edgeIncidenceSetCount, edgeIncidenceSet] at hdense
  obtain ⟨q,hq⟩ := hSfar
  have hTfar : T.strictRight.Nonempty := by
    cases hqv : q with
    | none =>
        exact False.elim (hq.2 (hqv ▸ hnone.1))
    | some z =>
        have hzidx : partitionIndex C z.1 = some z := by
          have hz := z.property
          simpa [C] using edgeContraction_index_some hab z.1 hz.1 hz.2
        refine ⟨z.1, ?_⟩
        change partitionIndex C z.1 ∈ S.strictRight
        rw [hzidx]
        exact hqv ▸ hq
  exact hno T hrootT hTfar hsepT hlinked


/-- Under the extremal induction and no-rigid-separation hypotheses, every edge contraction preserves the massed shore bound. -/
theorem contraction_shore_of_noRigid_and_minimality
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} (hab : G.Adj a b)
    (X : Finset V) (α : ℝ)
    (hm : MassedPair G (X : Set V) α)
    (hno : NoRigidSeparation G (X : Set V))
    (hsmallQ : ∀ S : VertexSeparation (edgeContraction G hab),
      Nat.card S.right < Fintype.card (EdgeContractionVertex a b) →
      Nat.card S.separator <
        Nat.card (partitionIndex (edgeContractionPartition G hab) '' (X : Set V)) →
      MassedPair ((edgeContraction G hab).induce S.right)
        {u : S.right | (u : EdgeContractionVertex a b) ∈ S.left} α →
      RootedLinked ((edgeContraction G hab).induce S.right)
        (separationBoundaryFinset S))
    (hsmallG : ∀ T : VertexSeparation G,
      Nat.card T.right < Fintype.card V →
      Nat.card T.separator ≤ X.card →
      MassedPair (G.induce T.right)
        {u : T.right | (u : V) ∈ T.left} α →
      RootedLinked (G.induce T.right) (separationBoundaryFinset T)) :
    ∀ S : VertexSeparation (edgeContraction G hab),
      (partitionIndex (edgeContractionPartition G hab) '' (X : Set V)) ⊆ S.left →
      Nat.card S.separator <
        Nat.card (partitionIndex (edgeContractionPartition G hab) '' (X : Set V)) →
      (edgeIncidenceSetCount (edgeContraction G hab) S.strictRight : ℝ) ≤
        α * (Nat.card S.strictRight : ℝ) := by
  classical
  let C := edgeContractionPartition G hab
  let H := edgeContraction G hab
  let Y : Set (EdgeContractionVertex a b) := partitionIndex C '' (X : Set V)
  intro S hroot hsep
  by_contra hnot
  have hdense : α * (Nat.card S.strictRight : ℝ) <
      (edgeIncidenceSetCount H S.strictRight : ℝ) := lt_of_not_ge hnot
  have hex : ∃ Q : VertexSeparation H,
      Y ⊆ Q.left ∧ Nat.card Q.separator < Nat.card Y ∧
      α * (Nat.card Q.strictRight : ℝ) <
        (edgeIncidenceSetCount H Q.strictRight : ℝ) :=
    ⟨S,hroot,hsep,hdense⟩
  obtain ⟨Q,hrootQ,hsepQ,hdenseQ,hlinkQ⟩ :=
    exists_linked_minimal_violating_shore H Y α hsmallQ hex
  by_cases hright : none ∈ Q.right
  · by_cases hleft : none ∈ Q.left
    · have hsepNone : none ∈ Q.separator := ⟨hleft,hright⟩
      exact no_violating_contraction_separator hab X α hm hno
        hsmallG Q hrootQ hsepQ hsepNone hdenseQ
    · have hfarNone : none ∈ Q.strictRight := ⟨hright,hleft⟩
      have hrootT : (X : Set V) ⊆
          (partitionPullbackSeparation C Q).left := by
        intro x hx
        exact hrootQ ⟨x,hx,rfl⟩
      have hcardImage : Nat.card Y ≤ Nat.card (X : Set V) := by
        change Y.ncard ≤ (X : Set V).ncard
        exact Set.ncard_image_le (Set.toFinite (X : Set V))
      have hsepOriginal : Nat.card Q.separator ≤ Nat.card (X : Set V) := by
        omega
      exact no_linked_contraction_strictFar hab (X : Set V) hno
        Q hrootT hsepOriginal hfarNone hlinkQ
  · have hbound := edgeContraction_shore_away hab X α hm Q hrootQ hsepQ hright
    exact (not_lt_of_ge hbound) hdenseQ


/-- D.2 common-neighbor estimate from contraction-shore stability and graph-order minimality. -/
theorem common_neighbors_ge_of_noRigid_minimality
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} (hab : G.Adj a b)
    (X : Finset V) (hb : b ∉ X) (r : ℕ)
    (hm : MassedPair G (X : Set V) (r : ℝ))
    (hbad : ¬ RootedLinked G X)
    (hmissing : ∀ x ∈ X, (X.erase x \ G.neighborFinset x).card ≤ 1)
    (hno : NoRigidSeparation G (X : Set V))
    (hsmallQ : ∀ S : VertexSeparation (edgeContraction G hab),
      Nat.card S.right < Fintype.card (EdgeContractionVertex a b) →
      Nat.card S.separator <
        Nat.card (partitionIndex (edgeContractionPartition G hab) '' (X : Set V)) →
      MassedPair ((edgeContraction G hab).induce S.right)
        {u : S.right | (u : EdgeContractionVertex a b) ∈ S.left} (r : ℝ) →
      RootedLinked ((edgeContraction G hab).induce S.right)
        (separationBoundaryFinset S))
    (hsmallG : ∀ T : VertexSeparation G,
      Nat.card T.right < Fintype.card V →
      Nat.card T.separator ≤ X.card →
      MassedPair (G.induce T.right)
        {u : T.right | (u : V) ∈ T.left} (r : ℝ) →
      RootedLinked (G.induce T.right) (separationBoundaryFinset T))
    (hminH : MassedPair (edgeContraction G hab)
      (partitionIndex (edgeContractionPartition G hab) '' (X : Set V))
      (r : ℝ) →
      RootedLinked (edgeContraction G hab)
        (X.image (partitionIndex (edgeContractionPartition G hab)))) :
    r - 1 ≤ (G.neighborFinset a ∩ G.neighborFinset b).card := by
  classical
  let C := edgeContractionPartition G hab
  let H := edgeContraction G hab
  let Y : Set (EdgeContractionVertex a b) := partitionIndex C '' (X : Set V)
  have hshore := contraction_shore_of_noRigid_and_minimality hab X (r : ℝ)
    hm hno hsmallQ hsmallG
  have hbadH : ¬ RootedLinked H (X.image (partitionIndex C)) := by
    intro h
    exact hbad (rootedLinked_of_edgeContraction hab X hb h)
  have hfail : (edgeIncidenceSetCount H Yᶜ : ℝ) ≤
      (r : ℝ) * (Yᶜ.ncard : ℝ) := by
    by_contra hnot
    have hstrict : (r : ℝ) * (Yᶜ.ncard : ℝ) <
        (edgeIncidenceSetCount H Yᶜ : ℝ) := lt_of_not_ge hnot
    have hmH : MassedPair H Y (r : ℝ) := by
      refine ⟨?_, ?_⟩
      · have hcard : Nat.card {v : EdgeContractionVertex a b // v ∉ Y} =
            (Yᶜ).ncard := by
          change Nat.card (Yᶜ : Set (EdgeContractionVertex a b)) = (Yᶜ).ncard
          exact Nat.card_coe_set_eq (Yᶜ)
        rw [hcard]
        exact hstrict
      · exact hshore
    exact hbadH (hminH hmH)
  exact common_neighbors_ge_of_contraction_mass_failure hab X hb r hm
    hmissing hfail


end Linkedness
end HadwigerLean
