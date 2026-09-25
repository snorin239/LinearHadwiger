import HadwigerLean.Graph.RootedDensity.UniversalRigidRegionFan
import HadwigerLean.Graph.Linkedness.RigidGluedFan
import Mathlib.Tactic

/-! An H-universal rigid far shore remains universal after a saturated
boundary-to-adhesion fan moves its adhesion outward. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- The saturated-fan transfer for an arbitrary finite target `H`. -/
theorem universalAt_glueLeft_of_saturated_fan
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W]
    {G : SimpleGraph V} (S : VertexSeparation G) [Fintype S.left]
    (T : VertexSeparation (G.induce S.left))
    (hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right)
    (H : SimpleGraph W)
    (huni : UniversalAtRightShore H S)
    (hsize : (Linkedness.separationBoundaryFinset S).card ≤ Fintype.card W)
    {q : ℕ} (C : IndexedPairs (Fin q) S.left)
    (F : IndexedLinkage (G.induce S.left) C)
    (hstarts : Finset.univ.image C.start = T.separatorFinset)
    (hfinish : ∀ i, (C.finish i : V) ∈ S.separator)
    (hpathT : ∀ i x, x ∈ pathVertexSet (F.path i) → x ∈ T.right)
    (hfirst : ∀ i x, x ∈ pathVertexSet (F.path i) →
      (x : V) ∈ S.right → x = C.finish i) :
    UniversalAtRightShore H (S.glueLeft T hBoundary) := by
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
  have hSR : S.right ⊆ R := fun _ hx => Or.inl hx
  have hfinishS (i : Fin q) : P.finish i ∈ S.separator := hfinish i
  have hfirstS (i : Fin q) (x : V)
      (hx : x ∈ pathVertexSet (L.path i)) (hxS : x ∈ S.right) :
      x = P.finish i := by
    obtain ⟨u,hu,hux⟩ := (hL i x).mp hx
    have huS : (u : V) ∈ S.right := hux ▸ hxS
    exact hux.symm.trans (congrArg Subtype.val (hfirst i u hu huS))
  let startR : Fin q → R := fun i =>
    ⟨P.start i,hpathR i _ (pathVertexSet.start_mem (L.path i))⟩
  have hstartSubset : Finset.univ.image startR ⊆
      Linkedness.separationBoundaryFinset Q := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    have hCi : C.start i ∈ T.separatorFinset := by
      rw [← hstarts]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hTL : C.start i ∈ T.left := (T.mem_separatorFinset _).mp hCi |>.1
    have hxL : ((startR i : R) : V) ∈ Q.left := by
      change (C.start i : V) ∈ (S.glueLeft T hBoundary).left
      exact ⟨(C.start i).property, hTL⟩
    exact (Linkedness.mem_separationBoundaryFinset Q (startR i)).mpr hxL
  have hstartCard : (Finset.univ.image startR).card = q := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro i j hij
      have hval : (C.start i : V) = (C.start j : V) :=
        congrArg (fun z : R => (z : V)) hij
      exact F.start_injective (Subtype.val_injective hval)
  have hTcard : T.separatorFinset.card = q := by
    rw [← hstarts, Finset.card_image_of_injective]
    · simp
    · exact F.start_injective
  have hQcard : (Linkedness.separationBoundaryFinset Q).card = q := by
    calc
      (Linkedness.separationBoundaryFinset Q).card = Nat.card Q.separator :=
        Linkedness.separationBoundaryFinset_card_eq Q
      _ = Q.separatorFinset.card := by simp [VertexSeparation.separatorFinset]
      _ = T.separatorFinset.card := S.glueLeft_separatorFinset_card T hBoundary
      _ = q := hTcard
  have hstartEq : Finset.univ.image startR =
      Linkedness.separationBoundaryFinset Q :=
    Finset.eq_of_subset_of_card_le hstartSubset (by omega)
  change UniversalAt (G.induce R) H
    (Linkedness.separationBoundaryFinset Q)
  intro Y root hinj hrange
  have hindexExists (y : ↥(Y : Set W)) : ∃ i : Fin q, startR i = root y := by
    have hy : root y ∈ Linkedness.separationBoundaryFinset Q := by
      have hr : root y ∈ Set.range root := ⟨y,rfl⟩
      simpa only [hrange, Finset.mem_coe] using hr
    rw [← hstartEq] at hy
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hy
    exact ⟨i,hi⟩
  let idx : ↥(Y : Set W) → Fin q := fun y => Classical.choose (hindexExists y)
  have hidx (y : ↥(Y : Set W)) : startR (idx y) = root y :=
    Classical.choose_spec (hindexExists y)
  have hidxInj : Function.Injective idx := by
    intro y z hyz
    apply hinj
    calc
      root y = startR (idx y) := (hidx y).symm
      _ = startR (idx z) := by rw [hyz]
      _ = root z := hidx z
  let e : ↥(Y : Set W) ↪ Fin q := ⟨idx,hidxInj⟩
  let P' : IndexedPairs ↥(Y : Set W) V := P.reindex e
  let L' : IndexedLinkage G P' := L.reindex e
  have hfinish' (y : ↥(Y : Set W)) : P'.finish y ∈ S.separator :=
    hfinishS (e y)
  have hpathR' (y : ↥(Y : Set W)) (x : V)
      (hx : x ∈ pathVertexSet (L'.path y)) : x ∈ R :=
    hpathR (e y) x hx
  have hfirst' (y : ↥(Y : Set W)) (x : V)
      (hx : x ∈ pathVertexSet (L'.path y)) (hxS : x ∈ S.right) :
      x = P'.finish y := hfirstS (e y) x hx hxS
  have hmodel := rootedMinor_of_universal_right_and_clean_fan_in_region
    G S R hSR H huni hsize Y P' L' hfinish' hpathR' hfirst'
  have hrootEq : (fun y : ↥(Y : Set W) =>
      (⟨P'.start y,
        hpathR' y _ (pathVertexSet.start_mem (L'.path y))⟩ : R)) = root := by
    funext y
    exact hidx y
  rwa [hrootEq] at hmodel

end HadwigerLean.RootedDensity
