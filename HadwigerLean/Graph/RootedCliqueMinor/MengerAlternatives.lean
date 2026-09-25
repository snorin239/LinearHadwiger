import HadwigerLean.Graph.RootedCliqueMinor

/-!
# Root-to-target Menger alternative

This form does not assume global vertex connectivity. It returns either a
full linkage with every root and target used once, or a smaller set Menger
separator. The latter is converted to a graph separation later.
-/

namespace HadwigerLean

/-- Reindex a full linkage so the path indexed by `i` starts at `root i`,
and note that its finishes exhaust the target set. -/
theorem reindex_root_target_linkage
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r : ℕ}
    (root : Fin r → V) (hroot : Function.Injective root)
    (X : Finset V) (hX : X.card = r)
    {P : IndexedPairs (Fin r) V} (L : IndexedLinkage G P)
    (hAB : SetMenger.IsABLinkage L (Finset.univ.image root) X) :
    ∃ (P' : IndexedPairs (Fin r) V) (L' : IndexedLinkage G P'),
      (∀ i, P'.start i = root i) ∧
      (∀ i, P'.finish i ∈ X) ∧
      (∀ x ∈ X, ∃ i, P'.finish i = x) := by
  classical
  let R : Finset V := Finset.univ.image root
  have hRcard : R.card = r := by
    simp [R, Finset.card_image_of_injective _ hroot]
  have hstartInj := L.start_injective
  have hstartSubset : Finset.univ.image P.start ⊆ R := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hAB.1 i
  have hstartCard : (Finset.univ.image P.start).card = r := by
    simp [Finset.card_image_of_injective _ hstartInj]
  have hstartRange : Finset.univ.image P.start = R :=
    Finset.eq_of_subset_of_card_le hstartSubset (by omega)
  have hsurj : ∀ i : Fin r, ∃ j : Fin r, P.start j = root i := by
    intro i
    have hi : root i ∈ R := Finset.mem_image.mpr
      ⟨i, Finset.mem_univ _, rfl⟩
    rw [← hstartRange] at hi
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
    exact ⟨j, hj⟩
  let idx : Fin r → Fin r := fun i => Classical.choose (hsurj i)
  have hidx : ∀ i : Fin r, P.start (idx i) = root i := fun i =>
    Classical.choose_spec (hsurj i)
  have hidxInj : Function.Injective idx := by
    intro i j hij
    apply hroot
    calc
      root i = P.start (idx i) := (hidx i).symm
      _ = P.start (idx j) := by rw [hij]
      _ = root j := hidx j
  let e : Fin r ↪ Fin r := ⟨idx, hidxInj⟩
  let P' := P.reindex e
  let L' : IndexedLinkage G P' := L.reindex e
  have hfinishSubset : Finset.univ.image P'.finish ⊆ X := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hAB.2 (e i)
  have hfinishCard : (Finset.univ.image P'.finish).card = r := by
    simp [Finset.card_image_of_injective _ L'.finish_injective]
  have hfinishRange : Finset.univ.image P'.finish = X :=
    Finset.eq_of_subset_of_card_le hfinishSubset (by omega)
  refine ⟨P', L', hidx, (fun i => hAB.2 (e i)), ?_⟩
  intro x hx
  rw [← hfinishRange] at hx
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
  exact ⟨i, hi⟩

/-- Menger either links every prescribed root to a distinct member of an
equicardinal target set, or supplies a separator of order below r. -/
theorem root_target_linkage_or_separator
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {r : ℕ}
    (root : Fin r → V) (hroot : Function.Injective root)
    (X : Finset V) (hX : X.card = r) :
    (∃ (P : IndexedPairs (Fin r) V) (L : IndexedLinkage G P),
      (∀ i, P.start i = root i) ∧
      (∀ i, P.finish i ∈ X) ∧
      (∀ x ∈ X, ∃ i, P.finish i = x)) ∨
    ∃ Q : Finset V,
      Q.card < r ∧
      SetMenger.IsABSeparator G (Finset.univ.image root) X Q := by
  classical
  let R : Finset V := Finset.univ.image root
  obtain ⟨Q, n, P, L, hQ, hAB, hcard, _⟩ :=
    SetMenger.finite_set_menger G R X
  by_cases hn : r ≤ n
  · left
    let e : Fin r ↪ Fin n := Fin.castLEEmb hn
    let P' := P.reindex e
    let L' : IndexedLinkage G P' := L.reindex e
    have hAB' : SetMenger.IsABLinkage L' R X :=
      ⟨fun i => hAB.1 (e i), fun i => hAB.2 (e i)⟩
    exact reindex_root_target_linkage root hroot X hX L' hAB'
  · right
    exact ⟨Q, by omega, hQ⟩

end HadwigerLean
