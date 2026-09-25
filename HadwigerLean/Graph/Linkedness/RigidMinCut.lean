import HadwigerLean.Graph.Linkedness.RigidFullFan
import HadwigerLean.Graph.Linkedness.RigidTorso
import HadwigerLean.Graph.Linkedness.CoreFarFan
import HadwigerLean.Graph.SetMengerTheorem
import HadwigerLean.Graph.RootedCliqueMinor.LeftCutGluing
import Mathlib.Tactic

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The old adhesion, viewed inside the near shore, has the same order. -/
theorem torsoBoundaryFinset_card_eq
    (G : SimpleGraph V) (S : VertexSeparation G) :
    (torsoBoundaryFinset G S).card = S.separatorFinset.card := by
  classical
  let J := torsoBoundaryFinset G S
  have himage : J.image Subtype.val = S.separatorFinset := by
    ext x
    constructor
    · intro hx
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      exact (S.mem_separatorFinset u).mpr
        ⟨u.property, (mem_torsoBoundaryFinset G S u).mp hu⟩
    · intro hx
      have hsep := (S.mem_separatorFinset x).mp hx
      exact Finset.mem_image.mpr ⟨⟨x,hsep.1⟩,
        (mem_torsoBoundaryFinset G S _).mpr hsep.2, rfl⟩
  rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]

/-- A full near-shore fan into a linked rigid far shore links all roots. -/
theorem rootedLinked_of_rigid_full_near_fan
    (G : SimpleGraph V) (S : VertexSeparation G) [Fintype S.left]
    (X : Finset V) (hX : (X : Set V) ⊆ S.left)
    {n : ℕ} (P : IndexedPairs (Fin n) S.left)
    (L : IndexedLinkage (G.induce S.left) P)
    (hstarts : Finset.univ.image P.start = torsoRootFinset S X)
    (hfinish : ∀ i, P.finish i ∈ torsoBoundaryFinset G S)
    (hfar : RootedLinked (G.induce S.right)
      (separationBoundaryFinset S)) :
    RootedLinked G X := by
  classical
  let P' : IndexedPairs (Fin n) V :=
    ⟨fun i => (P.start i : V), fun i => (P.finish i : V)⟩
  let L' : IndexedLinkage G P' := L.mapInduce
  have hrooted : RootedLinked G (Finset.univ.image P'.start) :=
    rootedLinked_of_full_fan_to_rigid_far S P' L'
      (fun i => (P.start i).property)
      (fun i => (mem_torsoBoundaryFinset G S _).mp (hfinish i)) hfar
  have hYimage : (torsoRootFinset S X).image Subtype.val = X := by
    ext x
    constructor
    · intro hx
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      exact (mem_torsoRootFinset S X u).mp hu
    · intro hx
      exact Finset.mem_image.mpr ⟨⟨x,hX hx⟩,
        (mem_torsoRootFinset S X _).mpr hx,rfl⟩
  have hrootset : Finset.univ.image P'.start = X := by
    calc
      Finset.univ.image P'.start =
          (Finset.univ.image P.start).image Subtype.val := by
            rw [Finset.image_image]
            rfl
      _ = X := by rw [hstarts, hYimage]
  exact hrootset ▸ hrooted
/-- Menger either gives a full root-to-adhesion fan inside the near shore,
or a smaller cut saturated by disjoint boundary-to-adhesion paths on the
cut's far side. -/
theorem rigid_full_fan_or_saturated_cut
    (G : SimpleGraph V) (S : VertexSeparation G) [Fintype S.left]
    (X : Finset V) (hX : (X : Set V) ⊆ S.left)
    (horder : S.separatorFinset.card = X.card) :
    (∃ (n : ℕ) (P : IndexedPairs (Fin n) S.left)
        (L : IndexedLinkage (G.induce S.left) P),
      n = X.card ∧
      Finset.univ.image P.start = torsoRootFinset S X ∧
      (∀ i, P.finish i ∈ torsoBoundaryFinset G S)) ∨
    ∃ (n : ℕ) (T : VertexSeparation (G.induce S.left))
      (C : IndexedPairs (Fin n) S.left)
      (F : IndexedLinkage (G.induce S.left) C),
      T.separatorFinset.card = n ∧ n < X.card ∧
      (torsoRootFinset S X : Set S.left) ⊆ T.left ∧
      (∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right) ∧
      Finset.univ.image C.start = T.separatorFinset ∧
      (∀ i, (C.finish i : V) ∈ S.separator) ∧
      (∀ i x, x ∈ pathVertexSet (F.path i) → x ∈ T.right) ∧
      (∀ i x, x ∈ pathVertexSet (F.path i) →
        (x : V) ∈ S.right → x = C.finish i) := by
  classical
  let Y := torsoRootFinset S X
  let J := torsoBoundaryFinset G S
  have hYcard : Y.card = X.card := torsoRootFinset_card S X hX
  have hJcard : J.card = X.card := by
    rw [torsoBoundaryFinset_card_eq, horder]
  obtain ⟨Q,n,P,L,hQ,hAB,hQcard,_⟩ :=
    SetMenger.finite_set_menger (G.induce S.left) Y J
  have hnle : n ≤ X.card := by
    have hstart : Finset.univ.image P.start ⊆ Y := by
      intro x hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact hAB.1 i
    have hc : (Finset.univ.image P.start).card = n := by
      simp [Finset.card_image_of_injective _ L.start_injective]
    have hle := Finset.card_le_card hstart
    omega
  by_cases hn : n = X.card
  · left
    have hstart : Finset.univ.image P.start = Y := by
      have hsub : Finset.univ.image P.start ⊆ Y := by
        intro x hx
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
        exact hAB.1 i
      apply Finset.eq_of_subset_of_card_le hsub
      have hc : (Finset.univ.image P.start).card = n := by
        simp [Finset.card_image_of_injective _ L.start_injective]
      omega
    exact ⟨n,P,L,hn,hstart,hAB.2⟩
  · right
    have hnlt : n < X.card := by omega
    let T := SetMenger.reachableSeparation (G.induce S.left) Y Q
    have hJright : ∀ x ∈ J, x ∈ T.right := by
      intro x hx
      exact SetMenger.reachableSeparation_right_of_ABSeparator
        (G.induce S.left) Y Q J hQ x hx
    have hBoundary : ∀ u : S.left, (u : V) ∈ S.right → u ∈ T.right := by
      intro u hu
      exact hJright u ((mem_torsoBoundaryFinset G S u).mpr hu)
    have hTcard : T.separatorFinset.card = n := by
      simpa [T, SetMenger.reachableSeparation_separatorFinset] using hQcard
    have hhit : ∀ i, ∃ x ∈ T.separatorFinset,
        x ∈ pathVertexSet (L.path i) := by
      intro i
      obtain ⟨q,hqQ,hqPath⟩ :=
        hQ (P.start i) (hAB.1 i) (P.finish i) (hAB.2 i) (L.path i)
      exact ⟨q, by simpa [T, SetMenger.reachableSeparation_separatorFinset] using hqQ,
        hqPath⟩
    obtain ⟨C,F,hCstart,hCfinish,hFright,hFfirst⟩ :=
      boundary_core_fan_in_right T J hJright P L hAB.2 hhit hTcard
    have hrootT : (Y : Set S.left) ⊆ T.left := by
      intro x hx
      exact SetMenger.reachableSeparation_left_of_mem
        (G.induce S.left) Y Q x hx
    refine ⟨n,T,C,F,hTcard,hnlt,hrootT,hBoundary,hCstart,?_,hFright,?_⟩
    · intro i
      exact ⟨(C.finish i).property,
        (mem_torsoBoundaryFinset G S (C.finish i)).mp (hCfinish i)⟩
    · intro i x hx hxS
      exact hFfirst i x hx ((mem_torsoBoundaryFinset G S x).mpr hxS)

end Linkedness
end HadwigerLean
