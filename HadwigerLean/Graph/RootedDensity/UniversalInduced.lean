import HadwigerLean.Graph.RootedDensity.Universal

/-! Transport partial rooted universality from an induced subgraph. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- A rooted target model in an induced graph remains a rooted model in
the ambient graph when the prescribed roots all lie in the induced set. -/
theorem UniversalAt.of_induce
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (S : Set V) (X : Finset V) (Y : Finset S)
    (hXS : (X : Set V) ⊆ S)
    (hY : ∀ y : S, y ∈ Y ↔ (y : V) ∈ X)
    (h : letI : Fintype S := Fintype.ofFinite S;
      UniversalAt (G.induce S) H Y) :
    UniversalAt G H X := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  intro T root hroot hrange
  let r : ↥(T : Set W) → S := fun i => ⟨root i, hXS (by
    rw [← hrange]
    exact ⟨i, rfl⟩)⟩
  have hrinj : Function.Injective r := by
    intro i j hij
    exact hroot (congrArg Subtype.val hij)
  have hrrange : Set.range r = (Y : Set S) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      apply (hY _).2
      have hi : root i ∈ (X : Set V) := by
        rw [← hrange]
        exact ⟨i, rfl⟩
      exact hi
    · intro hy
      have hyX : (y : V) ∈ X := (hY y).1 hy
      have hyRange : (y : V) ∈ Set.range root := by
        rw [hrange]
        exact hyX
      obtain ⟨i, hi⟩ := hyRange
      refine ⟨i, ?_⟩
      apply Subtype.ext
      exact hi
  obtain ⟨M⟩ := h T r hrinj hrrange
  let E : (G.induce S) ↪g G := SimpleGraph.Embedding.induce S
  have hM : RootedMinorModel (H.induce (T : Set W)) G root := by
    convert (M.map E.toHom E.injective) using 1
    funext i
    rfl
  exact ⟨hM⟩

end HadwigerLean.RootedDensity

