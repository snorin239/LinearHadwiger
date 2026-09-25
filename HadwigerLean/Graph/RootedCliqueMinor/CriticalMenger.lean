import HadwigerLean.Graph.RootedCliqueMinor.MengerAlternatives
import HadwigerLean.Graph.RootedCliqueMinor.InducedLinkage
import HadwigerLean.Graph.RootedCliqueMinor.LeftCutGluing
import HadwigerLean.Graph.RootedCliqueMinor.TorsoRecursion

/-!
# The critical order-r separation step

Apply Menger inside the near shore. A small separator gives the original
separator outcome; a full linkage lets the right-torso dichotomy recurse.
-/

namespace HadwigerLean

theorem RootCliqueCriticalSeparation.recurse
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r : ℕ}
    {root : Fin r → V}
    {M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots G (Set.range root))}
    {a b : V} (C : RootCliqueCriticalSeparation G root M a b)
    [Fintype C.sep.left] [DecidableEq C.sep.left]
    [Fintype C.sep.right]
    (hroot : Function.Injective root)
    (hD : RootCliqueSeparatorDichotomy (G.induce C.sep.right) r) :
    Nonempty (RootAttachedCliqueModel G root) ∨
      Nonempty (RootCliqueSeparatorOutcome G root M) := by
  classical
  let S := C.sep
  let rootL : Fin r → S.left := fun i => ⟨root i, C.roots_left i⟩
  have hrootL : Function.Injective rootL := by
    intro i j hij
    apply hroot
    exact congrArg (fun x : S.left => (x : V)) hij
  let A : Finset S.left := Finset.univ.image rootL
  let B : Finset S.left :=
    Finset.univ.filter (fun x : S.left => (x : V) ∈ S.right)
  have hBimage : B.image Subtype.val = S.separatorFinset := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact (S.mem_separatorFinset y).mpr
        ⟨y.property, (Finset.mem_filter.mp hy).2⟩
    · intro hx
      have hxL : x ∈ S.left := (S.mem_separatorFinset x).mp hx |>.1
      let y : S.left := ⟨x, hxL⟩
      apply Finset.mem_image.mpr
      refine ⟨y, ?_, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (S.mem_separatorFinset x).mp hx |>.2⟩
  have hBcard : B.card = r := by
    have hcard : (B.image Subtype.val).card = B.card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    rw [hBimage] at hcard
    have hX : S.separatorFinset.card = r := C.order_eq
    omega
  rcases root_target_linkage_or_separator (G.induce S.left)
      rootL hrootL B hBcard with hL | hQ
  · obtain ⟨P, L, hstart, hfinish, hsurj⟩ := hL
    let L' := L.mapInduce
    have hstart' : ∀ i, (⟨fun i => ((P.start i : S.left) : V),
        fun i => ((P.finish i : S.left) : V)⟩ : IndexedPairs (Fin r) V).start i =
          root i := by
      intro i
      exact congrArg Subtype.val (hstart i)
    have hfinish' : ∀ i, (P.finish i : V) ∈ S.separatorFinset := by
      intro i
      rw [← hBimage]
      exact Finset.mem_image.mpr ⟨P.finish i, hfinish i, rfl⟩
    have hsurj' : ∀ x ∈ S.separatorFinset,
        ∃ i, (P.finish i : V) = x := by
      intro x hx
      have hxB : x ∈ B.image Subtype.val := hBimage ▸ hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hxB
      obtain ⟨i, hi⟩ := hsurj y hy
      exact ⟨i, congrArg Subtype.val hi |>.trans hyx⟩
    exact C.recurse_with_linkage L' hstart' hfinish' hsurj' hD
  · obtain ⟨Q, hQcard, hAB⟩ := hQ
    right
    apply C.outcome_of_left_ABSeparator A B Q hQcard hAB
    · intro i
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    · intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩

end HadwigerLean
