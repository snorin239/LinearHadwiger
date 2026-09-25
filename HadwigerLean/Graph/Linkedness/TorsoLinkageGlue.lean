import HadwigerLean.Graph.Linkedness.TorsoPathSplice

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Replacing each torso excursion by a path in the rigid far side preserves disjoint paths. -/
theorem torso_linkage_splice_given_crossing
    (G : SimpleGraph V) (S : VertexSeparation G)
    {ι : Type*} {P : IndexedPairs ι S.left}
    (L : IndexedLinkage (torsoGraph G S) P)
    (B : IndexedLinkage (G.induce S.right) (torsoCrossingPairs G S L))
    (hB : InteriorsAvoid B (separationBoundaryFinset S)) :
    ∃ M : IndexedLinkage G
      ⟨(fun i => ((P.start i : S.left) : V)),
       (fun i => ((P.finish i : S.left) : V))⟩,
      ∀ i x, x ∈ pathVertexSet (M.path i) →
        x ∈ Subtype.val '' pathVertexSet (L.path i) ∨
        ∃ hi : TorsoPathHit G S (L.path i),
          x ∈ Subtype.val '' pathVertexSet (B.path ⟨i,hi⟩) := by
  classical
  let Q : IndexedPairs ι V :=
    ⟨(fun i => ((P.start i : S.left) : V)),
     (fun i => ((P.finish i : S.left) : V))⟩
  let E (i : ι) (hi : TorsoPathHit G S (L.path i)) :=
    torsoPathEndsChosen G S (L.path i) hi
  let N : ι → Set V := fun i =>
    if hi : TorsoPathHit G S (L.path i) then
      (Subtype.val '' pathVertexSet (E i hi).prefixPath) ∪
      (Subtype.val '' pathVertexSet (E i hi).suffixPath)
    else
      Subtype.val '' pathVertexSet (torsoNoHitPath G S (L.path i) hi)
  let F : ι → Set V := fun i =>
    if hi : TorsoPathHit G S (L.path i) then
      Subtype.val '' pathVertexSet (B.path ⟨i,hi⟩) else ∅
  let R : ι → Set V := fun i => N i ∪ F i
  have hNold (i : ι) (x : V) (hx : x ∈ N i) :
      ∃ u : S.left, u ∈ pathVertexSet (L.path i) ∧ (u : V) = x := by
    by_cases hi : TorsoPathHit G S (L.path i)
    · simp only [N, dif_pos hi] at hx
      rcases hx with hx | hx
      · obtain ⟨u,hu,hux⟩ := hx
        exact ⟨u,(E i hi).prefix_subset hu,hux⟩
      · obtain ⟨u,hu,hux⟩ := hx
        exact ⟨u,(E i hi).suffix_subset hu,hux⟩
    · simp only [N, dif_neg hi] at hx
      obtain ⟨u,hu,hux⟩ := hx
      exact ⟨u, (torsoNoHitPath_support G S (L.path i) hi) ▸ hu, hux⟩
  have hNnear (i : ι) : N i ⊆ S.left := by
    intro x hx
    obtain ⟨u,_,rfl⟩ := hNold i x hx
    exact u.property
  have hFfar (i : ι) : F i ⊆ S.right := by
    intro x hx
    by_cases hi : TorsoPathHit G S (L.path i)
    · simp only [F, dif_pos hi] at hx
      obtain ⟨u,_,rfl⟩ := hx
      exact u.property
    · simp only [F, dif_neg hi] at hx
      exact False.elim (by simpa using hx)
  have hFcross (i : ι) (x : V) (hx : x ∈ F i) (hxNear : x ∈ S.left) :
      ∃ u : S.left, u ∈ pathVertexSet (L.path i) ∧ (u : V) = x := by
    by_cases hi : TorsoPathHit G S (L.path i)
    · simp only [F, dif_pos hi] at hx
      exact crossing_path_near_overlap G S L B hB ⟨i,hi⟩ x hx hxNear
    · simp only [F, dif_neg hi] at hx
      exact False.elim (by simpa using hx)
  have hOldDis (i j : ι) (hij : i ≠ j) (x : V)
      (hi : ∃ u : S.left, u ∈ pathVertexSet (L.path i) ∧ (u : V) = x)
      (hj : ∃ u : S.left, u ∈ pathVertexSet (L.path j) ∧ (u : V) = x) : False := by
    obtain ⟨u,hu,hux⟩ := hi
    obtain ⟨v,hv,hvx⟩ := hj
    have huv : u = v := Subtype.val_injective (hux.trans hvx.symm)
    exact (Set.disjoint_left.mp (L.disjoint hij)) hu (huv ▸ hv)
  have hFDis (i j : ι) (hij : i ≠ j) (x : V)
      (hxi : x ∈ F i) (hxj : x ∈ F j) : False := by
    by_cases hi : TorsoPathHit G S (L.path i)
    · by_cases hj : TorsoPathHit G S (L.path j)
      · simp only [F, dif_pos hi] at hxi
        simp only [F, dif_pos hj] at hxj
        obtain ⟨u,hu,hux⟩ := hxi
        obtain ⟨v,hv,hvx⟩ := hxj
        have huv : u = v := Subtype.val_injective (hux.trans hvx.symm)
        exact (Set.disjoint_left.mp (B.disjoint
          (fun heq => hij (congrArg Subtype.val heq)))) hu (huv ▸ hv)
      · simp only [F, dif_neg hj] at hxj
        exact (by simpa using hxj)
    · simp only [F, dif_neg hi] at hxi
      exact (by simpa using hxi)
  have hRdis : Pairwise (fun i j => Disjoint (R i) (R j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    rcases hxi with hNi | hFi
    · rcases hxj with hNj | hFj
      · exact hOldDis i j hij x (hNold i x hNi) (hNold j x hNj)
      · exact hOldDis i j hij x (hNold i x hNi)
          (hFcross j x hFj (hNnear i hNi))
    · rcases hxj with hNj | hFj
      · exact hOldDis i j hij x (hFcross i x hFi (hNnear j hNj))
          (hNold j x hNj)
      · exact hFDis i j hij x hFi hFj
  have hRconn (i : ι) : (G.induce (R i)).Connected := by
    by_cases hi : TorsoPathHit G S (L.path i)
    · let A : Set V := Subtype.val '' pathVertexSet (E i hi).prefixPath
      let C : Set V := Subtype.val '' pathVertexSet (E i hi).suffixPath
      let D : Set V := Subtype.val '' pathVertexSet (B.path ⟨i,hi⟩)
      have hA : (G.induce A).Connected :=
        connected_induce_path_image G S.left (E i hi).prefixPath
      have hC : (G.induce C).Connected :=
        connected_induce_path_image G S.left (E i hi).suffixPath
      have hD : (G.induce D).Connected :=
        connected_induce_path_image G S.right (B.path ⟨i,hi⟩)
      have hfirstA : (((E i hi).first : S.left) : V) ∈ A :=
        ⟨(E i hi).first,pathVertexSet.finish_mem (E i hi).prefixPath,rfl⟩
      have hfirstD : (((E i hi).first : S.left) : V) ∈ D :=
        ⟨(torsoCrossingPairs G S L).start ⟨i,hi⟩,
          pathVertexSet.start_mem (B.path ⟨i,hi⟩),rfl⟩
      have hlastC : (((E i hi).last : S.left) : V) ∈ C :=
        ⟨(E i hi).last,pathVertexSet.start_mem (E i hi).suffixPath,rfl⟩
      have hlastD : (((E i hi).last : S.left) : V) ∈ D :=
        ⟨(torsoCrossingPairs G S L).finish ⟨i,hi⟩,
          pathVertexSet.finish_mem (B.path ⟨i,hi⟩),rfl⟩
      have hAD : (G.induce (A ∪ D)).Connected :=
        connected_induce_union_of_common hA hD hfirstA hfirstD
      have hADC : (G.induce ((A ∪ D) ∪ C)).Connected :=
        connected_induce_union_of_common hAD hC (Or.inr hlastD) hlastC
      have hshape : R i = (A ∪ D) ∪ C := by
        ext x
        simp only [R,N,F,A,C,D, dif_pos hi, Set.mem_union]
        tauto
      rw [hshape]
      exact hADC
    · have hno := connected_induce_path_image G S.left
        (torsoNoHitPath G S (L.path i) hi)
      have hNshape : N i =
          Subtype.val '' pathVertexSet (torsoNoHitPath G S (L.path i) hi) := by
        simp [N, hi]
      have hFshape : F i = ∅ := by
        simp [F, hi]
      have hRshape : R i =
          Subtype.val '' pathVertexSet (torsoNoHitPath G S (L.path i) hi) := by
        change N i ∪ F i = _
        rw [hNshape, hFshape, Set.union_empty]
      rw [hRshape]
      exact hno
  have hstart (i : ι) : Q.start i ∈ R i := by
    by_cases hi : TorsoPathHit G S (L.path i)
    · simp only [R,N,F,dif_pos hi]
      exact Or.inl (Or.inl
        ⟨P.start i,pathVertexSet.start_mem (E i hi).prefixPath,rfl⟩)
    · simp only [R,N,F,dif_neg hi]
      exact Or.inl ⟨P.start i,
        pathVertexSet.start_mem (torsoNoHitPath G S (L.path i) hi),rfl⟩
  have hfinish (i : ι) : Q.finish i ∈ R i := by
    by_cases hi : TorsoPathHit G S (L.path i)
    · simp only [R,N,F,dif_pos hi]
      exact Or.inl (Or.inr
        ⟨P.finish i,pathVertexSet.finish_mem (E i hi).suffixPath,rfl⟩)
    · simp only [R,N,F,dif_neg hi]
      exact Or.inl ⟨P.finish i,
        pathVertexSet.finish_mem (torsoNoHitPath G S (L.path i) hi),rfl⟩
  obtain ⟨M,hM⟩ :=
    exists_linkage_of_disjoint_connected_regions Q R hRconn hstart hfinish hRdis
  refine ⟨M, ?_⟩
  intro i x hx
  rcases hM i hx with hN | hF
  · obtain ⟨u,hu,hux⟩ := hNold i x hN
    exact Or.inl ⟨u,hu,hux⟩
  · by_cases hi : TorsoPathHit G S (L.path i)
    · exact Or.inr ⟨hi, by simpa only [F,dif_pos hi] using hF⟩
    · simp [F,hi] at hF

/-- Splicing also preserves avoidance of all near-side roots. -/
theorem torso_linkage_splice_rooted
    (G : SimpleGraph V) (S : VertexSeparation G)
    {ι : Type*} {P : IndexedPairs ι S.left}
    (L : IndexedLinkage (torsoGraph G S) P)
    (Y : Finset S.left) (X : Finset V)
    (hY : ∀ u : S.left, u ∈ Y ↔ (u : V) ∈ X)
    (hX : (X : Set V) ⊆ S.left)
    (hL : InteriorsAvoid L Y)
    (B : IndexedLinkage (G.induce S.right) (torsoCrossingPairs G S L))
    (hB : InteriorsAvoid B (separationBoundaryFinset S)) :
    ∃ M : IndexedLinkage G
      ⟨(fun i => ((P.start i : S.left) : V)),
       (fun i => ((P.finish i : S.left) : V))⟩,
      InteriorsAvoid M X := by
  obtain ⟨M,hM⟩ := torso_linkage_splice_given_crossing G S L B hB
  refine ⟨M, ?_⟩
  intro i x hx hxX
  have hOld : ∃ u : S.left,
      u ∈ pathVertexSet (L.path i) ∧ (u : V) = x := by
    rcases hM i x hx with hNear | ⟨hi,hFar⟩
    · exact hNear
    · exact crossing_path_near_overlap G S L B hB
        ⟨i,hi⟩ x hFar (hX hxX)
  obtain ⟨u,hu,hux⟩ := hOld
  have huY : u ∈ Y := (hY u).mpr (hux ▸ hxX)
  have huTerm := hL i u hu huY
  change u = P.start i ∨ u = P.finish i at huTerm
  change x = (P.start i : V) ∨ x = (P.finish i : V)
  rcases huTerm with heq | heq
  · exact Or.inl (hux.symm.trans (congrArg Subtype.val heq))
  · exact Or.inr (hux.symm.trans (congrArg Subtype.val heq))
/-- Rooted linkedness of the completed near side and of the original far side
implies rooted linkedness in the whole graph. -/
theorem rootedLinked_of_torso_and_far
    (G : SimpleGraph V) (S : VertexSeparation G)
    (X : Finset V) (Y : Finset S.left)
    (hX : (X : Set V) ⊆ S.left)
    (hY : ∀ u : S.left, u ∈ Y ↔ (u : V) ∈ X)
    (hK : RootedLinked (torsoGraph G S) Y)
    (hfar : RootedLinked (G.induce S.right)
      (separationBoundaryFinset S)) :
    RootedLinked G X := by
  classical
  letI : Fintype S.left := Fintype.ofFinite S.left
  letI : DecidableEq S.left := Classical.decEq _
  intro n P hP hne hPX
  let Q : IndexedPairs (Fin n) S.left := {
    start := fun i => ⟨P.start i,
      hX (hPX i (by simp [IndexedPairs.terminals]))⟩
    finish := fun i => ⟨P.finish i,
      hX (hPX i (by simp [IndexedPairs.terminals]))⟩
  }
  have hterm_iff (i : Fin n) (u : S.left) :
      u ∈ Q.terminals i ↔ (u : V) ∈ P.terminals i := by
    simp only [IndexedPairs.terminals, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (hu | hu)
      · exact Or.inl (congrArg Subtype.val hu)
      · exact Or.inr (congrArg Subtype.val hu)
    · rintro (hu | hu)
      · exact Or.inl (Subtype.ext hu)
      · exact Or.inr (Subtype.ext hu)
  have hQ : Q.DisjointTerminals := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro u hui huj
    exact (Set.disjoint_left.mp (hP hij))
      ((hterm_iff i u).mp hui) ((hterm_iff j u).mp huj)
  have hneQ : ∀ i, Q.start i ≠ Q.finish i := by
    intro i heq
    exact hne i (congrArg Subtype.val heq)
  have hQY : ∀ i, Q.terminals i ⊆ (Y : Set S.left) := by
    intro i u hu
    exact (hY u).mpr (hPX i ((hterm_iff i u).mp hu))
  obtain ⟨L,hL⟩ := hK n Q hQ hneQ hQY
  obtain ⟨B,hB⟩ := exists_torso_crossing_linkage G S L hfar
  obtain ⟨M,hM⟩ := torso_linkage_splice_rooted G S L Y X hY hX hL B hB
  exact ⟨M,hM⟩
end Linkedness
end HadwigerLean
