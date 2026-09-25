import HadwigerLean.Graph.RootedDensity.FanCore
import HadwigerLean.Graph.Linkedness.FirstHit

/-! The full-fan branch of Appendix F.c for arbitrary finite targets. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- A clean disjoint fan from every prescribed root to a universal
induced core transfers universality to the original root set. -/
theorem universalAt_of_universal_core_and_clean_fan
    {W : Type u} [Fintype W] {V : Type v} [Fintype V] [DecidableEq V]
    (H : SimpleGraph W) (G : SimpleGraph V) (J : Finset V)
    (hcore : Universal (G.induce (J : Set V)) H)
    (hW : 0 < Fintype.card W)
    (X : Finset V) (P : IndexedPairs ↥(X : Set V) V)
    (L : IndexedLinkage G P)
    (hstart : ∀ i, P.start i = (i : V))
    (hfinish : ∀ i, P.finish i ∈ J)
    (hfirst : ∀ i x, x ∈ pathVertexSet (L.path i) →
      x ∈ J → x = P.finish i) :
    UniversalAt G H X := by
  classical
  intro Y root hroot hrange
  let idx : ↥(Y : Set W) ↪ ↥(X : Set V) := {
    toFun := fun i => ⟨root i, by
      rw [← hrange]
      exact ⟨i, rfl⟩⟩
    inj' := by
      intro i j hij
      apply hroot
      exact congrArg Subtype.val hij
  }
  let Q : IndexedPairs ↥(Y : Set W) V := P.reindex idx
  let F : IndexedLinkage G Q := L.reindex idx
  have hfinishQ : ∀ i, Q.finish i ∈ J := fun i => hfinish (idx i)
  have hfirstQ : ∀ i x, x ∈ pathVertexSet (F.path i) →
      x ∈ J → x = Q.finish i := fun i x hx hxJ =>
    hfirst (idx i) x hx hxJ
  have hmodel := rootedMinor_of_universal_induced_and_clean_fan
    H G J hcore hW Y Q F hfinishQ hfirstQ
  have hstartQ : Q.start = root := by
    funext i
    exact hstart (idx i)
  rw [hstartQ] at hmodel
  exact hmodel

/-- Any full disjoint fan can be trimmed at its first core hit, so its
paths need not initially avoid the core. -/
theorem universalAt_of_universal_core_and_full_fan
    {W : Type u} [Fintype W] {V : Type v} [Fintype V] [DecidableEq V]
    (H : SimpleGraph W) (G : SimpleGraph V) (J : Finset V)
    (hcore : Universal (G.induce (J : Set V)) H)
    (hW : 0 < Fintype.card W)
    (X : Finset V) (P : IndexedPairs ↥(X : Set V) V)
    (L : IndexedLinkage G P)
    (hstart : ∀ i, P.start i = (i : V))
    (hfinish : ∀ i, P.finish i ∈ J) :
    UniversalAt G H X := by
  classical
  obtain ⟨P', L', hstart', hfinish', hfirst', _⟩ :=
    Linkedness.IndexedLinkage.trim_to_first_hit L J hfinish
  exact universalAt_of_universal_core_and_clean_fan H G J hcore hW
    X P' L' (fun i => (hstart' i).trans (hstart i))
    hfinish' hfirst'


/-- A full fan indexed by any finite type transfers universality to its
set of start vertices. -/
theorem universalAt_of_universal_core_and_full_fan_image
    {W : Type u} [Fintype W] {V : Type v} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (H : SimpleGraph W) (G : SimpleGraph V) (J : Finset V)
    (hcore : Universal (G.induce (J : Set V)) H)
    (hW : 0 < Fintype.card W)
    (P : IndexedPairs ι V) (L : IndexedLinkage G P)
    (hfinish : ∀ i, P.finish i ∈ J) :
    UniversalAt G H (Finset.univ.image P.start) := by
  classical
  let X : Finset V := Finset.univ.image P.start
  let f : ι ↪ ↥(X : Set V) := {
    toFun := fun i => ⟨P.start i, Finset.mem_image.mpr
      ⟨i, Finset.mem_univ _, rfl⟩⟩
    inj' := by
      intro i j hij
      exact L.start_injective (congrArg Subtype.val hij)
  }
  have hfSurj : Function.Surjective f := by
    intro x
    obtain ⟨i, _, hix⟩ := Finset.mem_image.mp x.property
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact hix
  let e₀ : ι ≃ ↥(X : Set V) :=
    Equiv.ofBijective f ⟨f.injective, hfSurj⟩
  let e : ↥(X : Set V) ≃ ι := e₀.symm
  let Q : IndexedPairs ↥(X : Set V) V := P.reindex e
  let F : IndexedLinkage G Q := L.reindex e.toEmbedding
  have hstart : ∀ x, Q.start x = (x : V) := by
    intro x
    exact congrArg Subtype.val (e₀.apply_symm_apply x)
  have hfinishQ : ∀ x, Q.finish x ∈ J := fun x => hfinish (e x)
  exact universalAt_of_universal_core_and_full_fan H G J hcore hW
    X Q F hstart hfinishQ
end HadwigerLean.RootedDensity


