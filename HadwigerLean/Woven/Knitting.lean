import HadwigerLean.Woven.KnittingPaths
import HadwigerLean.Woven.KnittingStarAssembly

/-!
# Knitting prescribed vertex groups

The `33p` connectivity consequence of linkedness: any partition of at most
`p` distinct prescribed vertices can be joined inside pairwise disjoint
connected sets, one for each group. The stars used in the proof omit their
representatives, so the case with no star edges is included.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A connected partition of `p` specified vertices follows from
`33p`-connectivity. The map `v` lists the specified vertices without
repetition; `group` assigns each to a nonempty part. -/
theorem exists_knitting_of_vertexConnected
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : ℕ) (v : Fin p ↪ V)
    (group : Fin p → Fin q) (hsurj : Function.Surjective group)
    (hconn : VertexConnected G (33 * p)) :
    ∃ C : Fin q → Set V,
      (∀ g, (G.induce (C g)).Connected) ∧
      (Pairwise fun g h => Disjoint (C g) (C h)) ∧
      (∀ i, v i ∈ C (group i)) := by
  classical
  let repIndex : Fin q → Fin p := Function.surjInv hsurj
  have hrepIndex (g : Fin q) : group (repIndex g) = g :=
    Function.rightInverse_surjInv hsurj g
  let X : Finset V := Finset.univ.image v
  have hX (i : Fin p) : v i ∈ X :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hXcard : X.card ≤ p := by
    simpa [X] using
      (Finset.card_image_le (s := (Finset.univ : Finset (Fin p))) (f := v))
  let I := {i : Fin p // i ≠ repIndex (group i)}
  have hI : Fintype.card I ≤ p := by
    simpa [I] using
      (Fintype.card_subtype_le (fun i : Fin p => i ≠ repIndex (group i)))
  let edgeStart : I → V := fun i => v i.1
  let edgeFinish : I → V := fun i => v (repIndex (group i.1))
  have hstartX (i : I) : edgeStart i ∈ X := hX i.1
  have hfinishX (i : I) : edgeFinish i ∈ X := hX _
  obtain ⟨proxy,L,_,hadjStart,hadjFinish,_,havoid⟩ :=
    exists_knitting_proxy_linkage G p X hXcard
      edgeStart edgeFinish hstartX hfinishX hI hconn
  let index : ↥(X : Set V) → Fin p := fun x =>
    Classical.choose (Finset.mem_image.mp x.property)
  have hindex (x : V) (hx : x ∈ X) : v (index ⟨x,hx⟩) = x :=
    (Classical.choose_spec (Finset.mem_image.mp hx)).2
  have hindex_of (i : Fin p) (hx : v i ∈ X) :
      index ⟨v i,hx⟩ = i :=
    v.injective (hindex (v i) hx)
  let label : ↥(X : Set V) → Fin q := fun x => group (index x)
  let groupI : I → Fin q := fun i => group i.1
  let rep : Fin q → V := fun g => v (repIndex g)
  have hrepX (g : Fin q) : rep g ∈ X := hX _
  have hstartLabel (i : I) :
      label ⟨edgeStart i, hstartX i⟩ = groupI i := by
    change group (index ⟨v i.1,hX i.1⟩) = group i.1
    rw [hindex_of]
  have hrepLabel (g : Fin q) :
      label ⟨rep g,hrepX g⟩ = g := by
    change group (index ⟨v (repIndex g),hX (repIndex g)⟩) = g
    rw [hindex_of, hrepIndex]
  have hend (i : I) : edgeFinish i = rep (groupI i) := rfl
  have hcover (x : V) (hx : x ∈ X) :
      x = rep (label ⟨x,hx⟩) ∨
      ∃ i : I, edgeStart i = x ∧ groupI i = label ⟨x,hx⟩ := by
    let j := index ⟨x,hx⟩
    have hj : v j = x := hindex x hx
    by_cases hrep : j = repIndex (group j)
    · left
      change x = v (repIndex (group j))
      rw [← hrep, hj]
    · right
      refine ⟨⟨j,hrep⟩, ?_, rfl⟩
      exact hj
  obtain ⟨C,hCconn,hCdis,hCcover⟩ :=
    knitting_of_star_linkage L edgeStart edgeFinish groupI rep label
      hstartX hrepX hstartLabel hrepLabel hend
      hadjStart hadjFinish havoid hcover
  refine ⟨C,hCconn,hCdis,?_⟩
  intro i
  have hi := hCcover (v i) (hX i)
  simpa only [label, hindex_of i (hX i)] using hi

end Woven
end HadwigerLean
