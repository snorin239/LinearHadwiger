import HadwigerLean.Graph.Linkedness.RootedMonotonicity
import HadwigerLean.Graph.Linkedness.CoreFarFan
import HadwigerLean.Graph.Linkedness.RootedLinkedIso
import HadwigerLean.Graph.RootedCliqueMinor.LeftCutGluing
import Mathlib.Tactic

namespace HadwigerLean
namespace Linkedness

/-- A trimmed fan inside a region transfers linkedness at its arrival set
from an induced core to its starts in the whole region. -/
theorem rootedLinked_region_of_fan_to_arrivals
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (R : Set V) (J : Finset V)
    (hJR : ∀ x ∈ J, x ∈ R)
    {q : ℕ} (P : IndexedPairs (Fin q) V)
    (F : IndexedLinkage G P)
    (hfinish : ∀ i, P.finish i ∈ J)
    (hpathR : ∀ i x, x ∈ pathVertexSet (F.path i) → x ∈ R)
    (hfirst : ∀ i x, x ∈ pathVertexSet (F.path i) →
      x ∈ J → x = P.finish i)
    (hcore : RootedLinked (G.induce (J : Set V))
      (fanArrivalFinset P J hfinish)) :
    RootedLinked (G.induce R)
      (Finset.univ.image (fun i : Fin q =>
        (⟨P.start i, hpathR i _ (pathVertexSet.start_mem (F.path i))⟩ : R))) := by
  classical
  let T : Finset R := @Finset.subtype V R (Classical.decPred R) J
  let P' : IndexedPairs (Fin q) R :=
    ⟨(fun i => ⟨P.start i, hpathR i _ (pathVertexSet.start_mem (F.path i))⟩),
     (fun i => ⟨P.finish i, hpathR i _ (pathVertexSet.finish_mem (F.path i))⟩)⟩
  let F' : IndexedLinkage (G.induce R) P' :=
    IndexedLinkage.induce F R hpathR
  have hTset : (J : Set V) = Subtype.val '' (T : Set R) := by
    ext v
    constructor
    · intro hv
      refine ⟨⟨v, hJR v hv⟩, ?_, rfl⟩
      exact (Finset.mem_subtype).2 hv
    · rintro ⟨x, hx, rfl⟩
      exact (Finset.mem_subtype).1 hx
  let e : ((G.induce R).induce (T : Set R)) ≃g
      G.induce (J : Set V) := {
    toEquiv := (Equiv.Set.image (fun x : R => (x : V))
      (T : Set R) Subtype.val_injective).trans
        (Equiv.setCongr hTset.symm)
    map_rel_iff' := by intro x y; rfl
  }
  have hfinishT (i : Fin q) : P'.finish i ∈ T :=
    (Finset.mem_subtype).2 (hfinish i)
  let Y : Finset (T : Set R) := fanArrivalFinset P' T hfinishT
  let X : Finset (J : Set V) := fanArrivalFinset P J hfinish
  have he (i : Fin q) :
      e (⟨P'.finish i, hfinishT i⟩ : (T : Set R)) =
        (⟨P.finish i, hfinish i⟩ : (J : Set V)) := by
    apply Subtype.ext
    rfl
  have hXY (u : (J : Set V)) : u ∈ X ↔ e.symm u ∈ Y := by
    constructor
    · intro hu
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hu
      have hi' : e (⟨P'.finish i, hfinishT i⟩ : (T : Set R)) = u := by
        rw [he i]
        exact hi
      have hw := congrArg e.symm hi'
      exact Finset.mem_image.mpr
        ⟨i, Finset.mem_univ _, by simpa only [e.symm_apply_apply] using hw⟩
    · intro hu
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hu
      have hi' := congrArg e hi
      rw [e.apply_symm_apply, he i] at hi'
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi'⟩
  have hcoreT : RootedLinked ((G.induce R).induce (T : Set R)) Y :=
    rootedLinked_of_iso e.symm X Y hXY hcore
  have hfirstT (i : Fin q) (x : R)
      (hx : x ∈ pathVertexSet (F'.path i)) (hxT : x ∈ T) :
      x = P'.finish i := by
    have hxG : (x : V) ∈ pathVertexSet (F.path i) :=
      (IndexedLinkage.mem_induce_pathVertexSet_iff F R hpathR i x).mp hx
    have hxJ : (x : V) ∈ J := (Finset.mem_subtype).1 hxT
    exact Subtype.ext (hfirst i (x : V) hxG hxJ)
  exact rootedLinked_of_trimmed_fan_to_arrivals P' F' T
    hfinishT hfirstT hcoreT


/-- A saturated fan from the new adhesion to the old linked adhesion
makes the far shore of the glued separation rooted-linked. -/
theorem rootedLinked_glueLeft_of_saturated_fan
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : VertexSeparation G) [Fintype S.left]
    (T : VertexSeparation (G.induce S.left))
    (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right)
    {q : ℕ} (C : IndexedPairs (Fin q) S.left)
    (F : IndexedLinkage (G.induce S.left) C)
    (hstarts : Finset.univ.image C.start = T.separatorFinset)
    (hfinish : ∀ i, (C.finish i : V) ∈ S.separator)
    (hpathT : ∀ i x, x ∈ pathVertexSet (F.path i) → x ∈ T.right)
    (hfirst : ∀ i x, x ∈ pathVertexSet (F.path i) →
      (x : V) ∈ S.right → x = C.finish i)
    (hfar : RootedLinked (G.induce S.right)
      (separationBoundaryFinset S)) :
    RootedLinked (G.induce (S.glueLeft T hBoundary).right)
      (separationBoundaryFinset (S.glueLeft T hBoundary)) := by
  classical
  let Q := S.glueLeft T hBoundary
  let R : Set V := Q.right
  let P : IndexedPairs (Fin q) V :=
    ⟨(fun i => (C.start i : V)), (fun i => (C.finish i : V))⟩
  let L : IndexedLinkage G P := F.mapInduce
  have hL (i : Fin q) (x : V) :
      x ∈ pathVertexSet (L.path i) ↔
        ∃ u : S.left, u ∈ pathVertexSet (F.path i) ∧ (u : V) = x := by
    change x ∈ ((F.path i : (G.induce S.left).Walk (C.start i) (C.finish i)).map
      (SimpleGraph.Embedding.induce S.left).toHom).support ↔
      ∃ u : S.left, u ∈ (F.path i : (G.induce S.left).Walk
        (C.start i) (C.finish i)).support ∧ (u : V) = x
    rw [SimpleGraph.Walk.support_map]
    simp only [List.mem_map]
    rfl
  have hpathR (i : Fin q) (x : V)
      (hx : x ∈ pathVertexSet (L.path i)) : x ∈ R := by
    obtain ⟨u,hu,rfl⟩ := (hL i x).mp hx
    exact Or.inr ⟨u.property, hpathT i u hu⟩
  let J : Finset V := S.right.toFinset
  have hJR (x : V) (hx : x ∈ J) : x ∈ R := by
    exact Or.inl (by simpa [J] using hx)
  have hfinishJ (i : Fin q) : P.finish i ∈ J := by
    simpa only [P, J, Set.mem_toFinset] using (hfinish i).2
  have hfirstJ (i : Fin q) (x : V)
      (hx : x ∈ pathVertexSet (L.path i)) (hxJ : x ∈ J) :
      x = P.finish i := by
    obtain ⟨u,hu,hux⟩ := (hL i x).mp hx
    have huR : (u : V) ∈ S.right := by simpa [J, ← hux] using hxJ
    exact hux.symm.trans (congrArg Subtype.val (hfirst i u hu huR))
  have hJeq : (J : Set V) = S.right := by
    ext x
    simp [J]
  let e : G.induce S.right ≃g G.induce (J : Set V) := {
    toEquiv := Equiv.setCongr hJeq.symm
    map_rel_iff' := by intro x y; rfl
  }
  let Z : Finset (J : Set V) :=
    (separationBoundaryFinset S).image e
  have hiso : RootedLinked (G.induce (J : Set V)) Z :=
    rootedLinked_of_iso e (separationBoundaryFinset S) Z
      (by intro v; simp [Z]) hfar
  have hsubset : fanArrivalFinset P J hfinishJ ⊆ Z := by
    intro u hu
    change u ∈ Finset.univ.image (fun i : Fin q =>
      (⟨P.finish i, hfinishJ i⟩ : (J : Set V))) at hu
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hu
    let v : S.right := ⟨C.finish i, (hfinish i).2⟩
    have hvZ : v ∈ separationBoundaryFinset S :=
      (mem_separationBoundaryFinset S v).mpr (hfinish i).1
    have hev : e v = u := by
      apply Subtype.ext
      exact congrArg Subtype.val hi
    exact Finset.mem_image.mpr ⟨v, hvZ, hev⟩
  have hcore : RootedLinked (G.induce (J : Set V))
      (fanArrivalFinset P J hfinishJ) := hiso.of_subset hsubset
  have hfan := rootedLinked_region_of_fan_to_arrivals G R J hJR
    P L hfinishJ hpathR hfirstJ hcore
  have hstartQ (i : Fin q) : P.start i ∈ R :=
    hpathR i _ (pathVertexSet.start_mem (L.path i))
  let X : Finset R := Finset.univ.image
    (fun i : Fin q => (⟨P.start i, hstartQ i⟩ : R))
  have hsubsetQ : X ⊆ separationBoundaryFinset Q := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    have hCi : C.start i ∈ T.separatorFinset := by
      rw [← hstarts]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hTL : C.start i ∈ T.left := (T.mem_separatorFinset _).mp hCi |>.1
    have hxL : ((⟨P.start i, hstartQ i⟩ : R) : V) ∈ Q.left := by
      change (C.start i : V) ∈ (S.glueLeft T hBoundary).left
      exact ⟨(C.start i).property, hTL⟩
    exact (mem_separationBoundaryFinset Q
      (⟨P.start i, hstartQ i⟩ : R)).mpr hxL
  have hstartCard : X.card = q := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro i j hij
      have hP : P.start i = P.start j :=
        congrArg (fun z : R => (z : V)) hij
      have hval : (C.start i : V) = (C.start j : V) := hP
      exact F.start_injective (Subtype.val_injective hval)
  have hTcard : T.separatorFinset.card = q := by
    rw [← hstarts, Finset.card_image_of_injective]
    · simp
    · exact F.start_injective
  have hQcard : (separationBoundaryFinset Q).card = q := by
    have hcard := S.glueLeft_separatorFinset_card T hBoundary
    have hboundaryCard : (separationBoundaryFinset Q).card =
        Q.separatorFinset.card := by
      exact Finset.card_bij (fun z hz => (z : V)) (by
        intro z hz
        exact (Q.mem_separatorFinset z).mpr
          ⟨(mem_separationBoundaryFinset Q z).mp hz, z.property⟩)
        (by intro a ha b hb hab; exact Subtype.val_injective hab)
        (by
          intro y hy
          have hyQ : y ∈ Q.right := (Q.mem_separatorFinset y).mp hy |>.2
          refine ⟨⟨y,hyQ⟩, ?_, rfl⟩
          exact (mem_separationBoundaryFinset Q ⟨y,hyQ⟩).mpr
            ((Q.mem_separatorFinset y).mp hy).1)
    change Q.separatorFinset.card = T.separatorFinset.card at hcard
    omega
  have hXeq : X = separationBoundaryFinset Q :=
    Finset.eq_of_subset_of_card_le hsubsetQ (by omega)
  simpa only [X, R, Q, hXeq] using hfan

end Linkedness
end HadwigerLean
