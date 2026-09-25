import HadwigerLean.Woven.KnittingStar

/-!
# Assemble linked star edges into disjoint connected parts
-/

namespace HadwigerLean
namespace Woven

variable {V ι : Type*} {G : SimpleGraph V}
  {q : ℕ} {X : Finset V}

/-- A disjoint proxy linkage for the star edges of a partition gives
pairwise disjoint connected vertex sets containing the specified vertices
of each part. -/
theorem knitting_of_star_linkage
    {P : IndexedPairs ι V} (L : IndexedLinkage G P)
    (edgeStart edgeFinish : ι → V)
    (group : ι → Fin q) (rep : Fin q → V)
    (label : ↥(X : Set V) → Fin q)
    (hstartX : ∀ i, edgeStart i ∈ X)
    (hrepX : ∀ g, rep g ∈ X)
    (hstartLabel : ∀ i,
      label ⟨edgeStart i, hstartX i⟩ = group i)
    (hrepLabel : ∀ g, label ⟨rep g, hrepX g⟩ = g)
    (hend : ∀ i, edgeFinish i = rep (group i))
    (hadjStart : ∀ i, G.Adj (edgeStart i) (P.start i))
    (hadjFinish : ∀ i, G.Adj (edgeFinish i) (P.finish i))
    (havoid : ∀ v, v ∈ L.vertices → v ∉ X)
    (hcover : ∀ (v : V) (hv : v ∈ X),
      v = rep (label ⟨v,hv⟩) ∨
      ∃ i, edgeStart i = v ∧ group i = label ⟨v,hv⟩) :
    ∃ C : Fin q → Set V,
      (∀ g, (G.induce (C g)).Connected) ∧
      (Pairwise fun g h => Disjoint (C g) (C h)) ∧
      (∀ (v : V) (hv : v ∈ X), v ∈ C (label ⟨v,hv⟩)) := by
  classical
  let patch (g : Fin q) :=
    knittingStarPatch rep edgeStart edgeFinish group L g
  let C (g : Fin q) : Set V :=
    knittingStarPiece rep edgeStart edgeFinish group L g
  have hpatchRep (g : Fin q)
      (slot : Option {i : ι // group i = g}) :
      rep g ∈ patch g slot := by
    cases slot with
    | none => simp [patch, knittingStarPatch]
    | some i =>
      have hi := hend i.1
      rw [i.property] at hi
      simp [patch, knittingStarPatch, knittingEdgePiece, hi]
  have hconnected (g : Fin q) : (G.induce (C g)).Connected := by
    let S : Set (Set V) := Set.range (patch g)
    have hS : S.Nonempty := ⟨patch g none, ⟨none,rfl⟩⟩
    have hpair : ∀ {s t}, s ∈ S → t ∈ S → (s ∩ t).Nonempty := by
      rintro s t ⟨u,rfl⟩ ⟨v,rfl⟩
      exact ⟨rep g, hpatchRep g u, hpatchRep g v⟩
    have hSconn : ∀ {s}, s ∈ S → (G.induce s).Connected := by
      rintro s ⟨slot,rfl⟩
      cases slot with
      | none => simp [patch, knittingStarPatch]
      | some i =>
        exact knittingEdgePiece_connected L edgeStart edgeFinish
          hadjStart hadjFinish i.1
    exact G.induce_sUnion_connected_of_pairwise_not_disjoint
      hS hpair hSconn
  have hclass (g : Fin q) (x : V) (hx : x ∈ C g) :
      (∃ hxX : x ∈ X, label ⟨x,hxX⟩ = g) ∨
      ∃ i : ι, group i = g ∧ x ∈ pathVertexSet (L.path i) := by
    obtain ⟨s,⟨slot,rfl⟩,hxs⟩ := Set.mem_sUnion.mp hx
    cases slot with
    | none =>
      have hxrep : x = rep g := by
        simpa [patch, knittingStarPatch] using hxs
      subst x
      exact Or.inl ⟨hrepX g, hrepLabel g⟩
    | some i =>
      change x ∈ knittingEdgePiece edgeStart edgeFinish L i.1 at hxs
      rcases hxs with hs | ht | hp
      · subst x
        exact Or.inl ⟨hstartX i.1, by simpa [i.property] using hstartLabel i.1⟩
      · have hxrep : x = rep g := by
          rw [ht, hend i.1, i.property]
        rw [hxrep]
        exact Or.inl ⟨hrepX g, hrepLabel g⟩
      · exact Or.inr ⟨i.1, i.property, hp⟩
  have hdis : Pairwise fun g h => Disjoint (C g) (C h) := by
    intro g h hgh
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hclass g x hx with ⟨hxX,hxg⟩ | ⟨i,hig,hxi⟩
    · rcases hclass h x hy with ⟨_,hxh⟩ | ⟨i,_,hxi⟩
      · exact hgh (hxg.symm.trans hxh)
      · exact havoid x (L.path_subset_vertices i hxi) hxX
    · rcases hclass h x hy with ⟨hxX,_⟩ | ⟨j,hjh,hxj⟩
      · exact havoid x (L.path_subset_vertices i hxi) hxX
      · by_cases hij : i = j
        · subst j
          exact hgh (hig.symm.trans hjh)
        · exact (Set.disjoint_left.mp (L.disjoint hij)) hxi hxj
  have hspecified (v : V) (hv : v ∈ X) :
      v ∈ C (label ⟨v,hv⟩) := by
    let g := label ⟨v,hv⟩
    rcases hcover v hv with hrep | ⟨i,hi,hig⟩
    · exact Set.mem_sUnion.mpr
        ⟨patch g none, ⟨none,rfl⟩, by
          change v = rep g
          exact hrep⟩
    · let slot : {i : ι // group i = g} := ⟨i,hig⟩
      exact Set.mem_sUnion.mpr
        ⟨patch g (some slot), ⟨some slot,rfl⟩,
          by
            change v ∈ knittingEdgePiece edgeStart edgeFinish L i
            exact Or.inl hi.symm⟩
  exact ⟨C,hconnected,hdis,hspecified⟩

end Woven
end HadwigerLean


