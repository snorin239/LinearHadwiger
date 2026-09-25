import HadwigerLean.Bootstrap.Definitions
import HadwigerLean.Graph.ChromaticSlice
import Mathlib.Tactic

/-!
# Chromatic separation for three outer-induction children
-/

namespace HadwigerLean
namespace Woven

/-- A nested induced graph is isomorphic to the graph induced on the
image of its vertex set in the ambient graph. -/
theorem chromatic_nested_image
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (R : Set V) (S : Set R)
    [Fintype R] [Fintype S] [Fintype (Subtype.val '' S)] :
    chromatic ((G.induce R).induce S) =
      chromatic (G.induce (Subtype.val '' S)) := by
  let e : (G.induce R).induce S ≃g
      G.induce (Subtype.val '' S) := {
    toEquiv := Equiv.Set.image (fun r : R => (r : V)) S Subtype.val_injective
    map_rel_iff' := by
      intro a b
      rfl
  }
  change ENat.toNat (((G.induce R).induce S).chromaticNumber) =
    ENat.toNat ((G.induce (Subtype.val '' S)).chromaticNumber)
  exact congrArg ENat.toNat (SimpleGraph.chromaticNumber_congr e)


/-- The set image of a subtype subset, represented as a finite set. -/
private noncomputable def ambientFinset {V : Type*} [Fintype V]
    (R : Set V) (S : Set R) : Finset V := by
  classical
  letI : Fintype (Subtype.val '' S) := Fintype.ofFinite _
  exact (Subtype.val '' S).toFinset

private theorem ambientFinset_coe {V : Type*} [Fintype V]
    (R : Set V) (S : Set R) :
    (ambientFinset R S : Set V) = Subtype.val '' S := by
  classical
  ext x
  simp [ambientFinset]

private theorem ambientFinset_subset {V : Type*} [Fintype V]
    (R : Set V) (S : Set R) :
    (ambientFinset R S : Set V) ⊆ R := by
  rw [ambientFinset_coe]
  rintro x ⟨y, -, rfl⟩
  exact y.property

private theorem ambientFinset_disjoint {V : Type*} [Fintype V]
    (R : Set V) {S T : Set R} (hST : Disjoint S T) :
    Disjoint (ambientFinset R S) (ambientFinset R T) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxS hxT
  have hs : x ∈ Subtype.val '' S := by
    change x ∈ (ambientFinset R S : Set V) at hxS
    rwa [ambientFinset_coe] at hxS
  have ht : x ∈ Subtype.val '' T := by
    change x ∈ (ambientFinset R T : Set V) at hxT
    rwa [ambientFinset_coe] at hxT
  obtain ⟨s, hs, hse⟩ := hs
  obtain ⟨t, ht, hte⟩ := ht
  have heq : s = t := Subtype.ext (hse.trans hte.symm)
  exact (Set.disjoint_left.mp hST) hs (heq ▸ ht)

private theorem ambientFinset_chromatic {V : Type*} [Fintype V]
    (G : SimpleGraph V) (R : Set V) (S : Set R)
    [Fintype R] [Fintype S] :
    chromatic ((G.induce R).induce S) =
      chromatic (G.induce (ambientFinset R S : Set V)) := by
  classical
  letI : Fintype (Subtype.val '' S) := Fintype.ofFinite _
  rw [ambientFinset_coe]
  exact chromatic_nested_image G R S


/-- Two applications of chromatic separability yield three disjoint
induced children, each losing at most two separation budgets. -/
theorem three_chromatic_pieces_of_separation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Y : Finset V) (s : ℕ)
    (hsep : ∀ X : Finset V, X ⊆ Y →
      2 * s < chromatic (G.induce (X : Set V)) →
      Bootstrap.ChromaticSeparable (G.induce (X : Set V)) s)
    (hχ : 3 * s < chromatic (G.induce (Y : Set V))) :
    ∃ J : Fin 3 → Finset V,
      (∀ i, J i ⊆ Y) ∧
      (Pairwise fun i j => Disjoint (J i) (J j)) ∧
      (∀ i, chromatic (G.induce (Y : Set V)) ≤
        chromatic (G.induce (J i : Set V)) + 2 * s) := by
  classical
  have hχ2 : 2 * s < chromatic (G.induce (Y : Set V)) := by omega
  obtain ⟨A, B, hAB, hA, hB⟩ := hsep Y (by rfl) hχ2
  let A' : Finset V := ambientFinset (Y : Set V) A
  let B' : Finset V := ambientFinset (Y : Set V) B
  have hA'Y : A' ⊆ Y := by
    intro x hx
    exact ambientFinset_subset (Y : Set V) A hx
  have hB'Y : B' ⊆ Y := by
    intro x hx
    exact ambientFinset_subset (Y : Set V) B hx
  have hAB' : Disjoint A' B' := ambientFinset_disjoint (Y : Set V) hAB
  have hAχ : chromatic (G.induce (Y : Set V)) ≤
      chromatic (G.induce (A' : Set V)) + s := by
    simpa only [ambientFinset_chromatic G (Y : Set V) A] using hA
  have hBχ : chromatic (G.induce (Y : Set V)) ≤
      chromatic (G.induce (B' : Set V)) + s := by
    simpa only [ambientFinset_chromatic G (Y : Set V) B] using hB
  have hAχ2 : 2 * s < chromatic (G.induce (A' : Set V)) := by omega
  obtain ⟨C, D, hCD, hC, hD⟩ := hsep A' hA'Y hAχ2
  let C' : Finset V := ambientFinset (A' : Set V) C
  let D' : Finset V := ambientFinset (A' : Set V) D
  have hC'A' : C' ⊆ A' := by
    intro x hx
    exact ambientFinset_subset (A' : Set V) C hx
  have hD'A' : D' ⊆ A' := by
    intro x hx
    exact ambientFinset_subset (A' : Set V) D hx
  have hC'Y : C' ⊆ Y := hC'A'.trans hA'Y
  have hD'Y : D' ⊆ Y := hD'A'.trans hA'Y
  have hCD' : Disjoint C' D' := ambientFinset_disjoint (A' : Set V) hCD
  have hCB' : Disjoint C' B' := by
    apply Finset.disjoint_left.mpr
    intro x hxC hxB
    exact (Finset.disjoint_left.mp hAB') (hC'A' hxC) hxB
  have hDB' : Disjoint D' B' := by
    apply Finset.disjoint_left.mpr
    intro x hxD hxB
    exact (Finset.disjoint_left.mp hAB') (hD'A' hxD) hxB
  have hCχ : chromatic (G.induce (A' : Set V)) ≤
      chromatic (G.induce (C' : Set V)) + s := by
    simpa only [ambientFinset_chromatic G (A' : Set V) C] using hC
  have hDχ : chromatic (G.induce (A' : Set V)) ≤
      chromatic (G.induce (D' : Set V)) + s := by
    simpa only [ambientFinset_chromatic G (A' : Set V) D] using hD
  have hYC : chromatic (G.induce (Y : Set V)) ≤
      chromatic (G.induce (C' : Set V)) + 2 * s := by omega
  have hYD : chromatic (G.induce (Y : Set V)) ≤
      chromatic (G.induce (D' : Set V)) + 2 * s := by omega
  have hYB : chromatic (G.induce (Y : Set V)) ≤
      chromatic (G.induce (B' : Set V)) + 2 * s := by omega
  let J : Fin 3 → Finset V := ![C', D', B']
  refine ⟨J, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa [J] using hC'Y
    · simpa [J] using hD'Y
    · simpa [J] using hB'Y
  · intro i j hij
    have hDC' : Disjoint D' C' := hCD'.symm
    have hBC' : Disjoint B' C' := hCB'.symm
    have hBD' : Disjoint B' D' := hDB'.symm
    fin_cases i <;> fin_cases j <;> simp_all [J]
  · intro i
    fin_cases i
    · simpa [J] using hYC
    · simpa [J] using hYD
    · simpa [J] using hYB

end Woven
end HadwigerLean