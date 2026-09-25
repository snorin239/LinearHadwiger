import HadwigerLean.Inseparability.FirstStage

/-!
# The first sequential stage as a stage invariant

The rooted model in `D` and clean paths from the chromatic region produce the
first nonempty model. The core consists of `D` and the distinct path starts.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x k m : ℕ}

/-- The special first-stage construction, before the chromatic reserve is
restored by a second highly chromatic region. -/
theorem exists_first_stage_state
    (D H : Finset V)
    (hDH : Disjoint D H)
    (hW : Woven (G.induce (D : Set V)) x 0)
    (P : IndexedPairs (Fin x) V) (L : IndexedLinkage G P)
    (hfinishD : ∀ i, P.finish i ∈ D)
    (hstartH : ∀ i, P.start i ∈ H)
    (hcleanD : ∀ i v, v ∈ pathVertexSet (L.path i) →
      v ∈ D → v = P.finish i)
    (hcleanH : ∀ i v, v ∈ pathVertexSet (L.path i) →
      v ∈ H → v = P.start i)
    (hHconn : VertexConnected (G.induce (H : Set V)) k)
    (hχH : chromatic G ≤ chromatic (G.induce (H : Set V)) + m) :
    Nonempty (StageState G x k m (D.card + x)) := by
  classical
  obtain ⟨M,hMbranch,hMtangent,hMcore⟩ :=
    first_stage_model_of_woven_piece D H hDH hW P L
      hfinishD hstartH hcleanD hcleanH
  let core : Finset V := D ∪ Finset.univ.image P.start
  have hcoreCard : core.card ≤ D.card + x := by
    have h1 := Finset.card_union_le D (Finset.univ.image P.start)
    have h2 := Finset.card_image_le
      (s := (Finset.univ : Finset (Fin x))) (f := P.start)
    simpa [core] using h1.trans (Nat.add_le_add_left h2 D.card)
  refine ⟨{
    root := P.start
    root_injective := L.start_injective
    model := M
    core := core
    region := H
    region_connected := hHconn
    chromatic_reserve := hχH
    core_card_le := hcoreCard
    tangent := ?_
    intersection_in_core := ?_
    core_witness := ?_
  }⟩
  · intro i
    refine ⟨P.start i, ?_, ?_⟩
    · have h : P.start i ∈ M.branch i ∩ (H : Set V) := by
        rw [hMtangent i]
        simp
      exact h
    · intro v hv
      have hv' : v ∈ M.branch i ∩ (H : Set V) := hv
      rw [hMtangent i] at hv'
      simpa using hv'
  · intro v hv
    obtain ⟨i,hvi⟩ := Set.mem_iUnion.mp hv.1
    have hviH : v ∈ M.branch i ∩ (H : Set V) := ⟨hvi,hv.2⟩
    rw [hMtangent i] at hviH
    have heq : v = P.start i := by simpa using hviH
    subst v
    exact Finset.mem_union.mpr (Or.inr
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  · intro i j hij
    obtain ⟨a,ha,b,hb,haD,hbD,hab⟩ := hMcore i j hij
    exact ⟨a,ha,b,hb,
      Finset.mem_union.mpr (Or.inl haD),
      Finset.mem_union.mpr (Or.inl hbD),hab⟩

end Inseparability
end HadwigerLean

