import HadwigerLean.Graph.RootedDensity.UniversalRigidFanImage
import HadwigerLean.Graph.Linkedness.RigidMinCut
import Mathlib.Tactic

/-!
# Full near-side fan into a universal rigid far shore

This is the arbitrary-target analogue of the linkedness full-fan
branch in Appendix F.1. A disjoint fan inside the near shore, from
every prescribed root into the adhesion, attaches the universal
far-side rooted model and contradicts a massed counterexample.
-/

namespace HadwigerLean.RootedDensity

universe u v

theorem universalAt_of_rigid_full_near_fan
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) (S : VertexSeparation G)
    [Fintype S.left]
    (H : SimpleGraph W)
    (huni : UniversalAtRightShore H S)
    (hsize : (Linkedness.separationBoundaryFinset S).card ≤ Fintype.card W)
    (X : Finset V) (hX : (X : Set V) ⊆ S.left)
    {n : ℕ} (P : IndexedPairs (Fin n) S.left)
    (L : IndexedLinkage (G.induce S.left) P)
    (hstarts : Finset.univ.image P.start =
      Linkedness.torsoRootFinset S X)
    (hfinish : ∀ i, P.finish i ∈ Linkedness.torsoBoundaryFinset G S) :
    UniversalAt G H X := by
  classical
  let P' : IndexedPairs (Fin n) V :=
    ⟨fun i => (P.start i : V), fun i => (P.finish i : V)⟩
  let L' : IndexedLinkage G P' := L.mapInduce
  have huniX : UniversalAt G H (Finset.univ.image P'.start) :=
    universalAt_of_full_fan_to_universal_right_image
      G S H huni hsize P' L'
      (fun i => (P.start i).property)
      (fun i => (Linkedness.mem_torsoBoundaryFinset G S _).mp
        (hfinish i))
  have hYimage :
      (Linkedness.torsoRootFinset S X).image Subtype.val = X := by
    ext x
    constructor
    · intro hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact (Linkedness.mem_torsoRootFinset S X y).mp hy
    · intro hx
      exact Finset.mem_image.mpr
        ⟨⟨x,hX hx⟩,
          (Linkedness.mem_torsoRootFinset S X _).mpr hx,rfl⟩
  have hrootset : Finset.univ.image P'.start = X := by
    calc
      Finset.univ.image P'.start =
          (Finset.univ.image P.start).image Subtype.val := by
            rw [Finset.image_image]
            rfl
      _ = X := by rw [hstarts,hYimage]
  exact hrootset ▸ huniX

end HadwigerLean.RootedDensity
