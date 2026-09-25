import HadwigerLean.Graph.RootedCliqueMinor

/-!
# Lifting attached clique models through a root-free contraction

The induction for the rooted clique minor theorem contracts an edge in a
branch avoiding every prescribed root.  Each root is therefore represented
by a singleton block, so attachments in the quotient lift unchanged.
-/

namespace HadwigerLean

/-- Either all root-avoiding branches are singletons, or an actual edge
inside one such branch can be contracted without identifying a root. -/
theorem singleton_avoiding_or_contractable
    {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (root : Fin r → V)
    (M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots G (Set.range root))) :
    (∀ i : Fin (2 * r),
      Disjoint (M.branch i) (Set.range root) →
        ∃ x : V, M.branch i = {x}) ∨
    ∃ (i : Fin (2 * r)) (a b : V),
      a ∈ M.branch i ∧ b ∈ M.branch i ∧
      G.Adj a b ∧ a ∉ Set.range root ∧ b ∉ Set.range root := by
  classical
  by_cases hs : ∀ i : Fin (2 * r),
      Disjoint (M.branch i) (Set.range root) →
        ∃ x : V, M.branch i = {x}
  · exact Or.inl hs
  right
  push Not at hs
  obtain ⟨i, havoid, hnonsingle⟩ := hs
  let a := M.representative i
  have ha : a ∈ M.branch i := M.representative_mem i
  have haR : a ∉ Set.range root := by
    intro h
    exact (Set.disjoint_left.mp havoid) ha h
  have hother : ∃ b ∈ M.branch i, b ≠ a := by
    by_contra h
    push Not at h
    apply hnonsingle a
    ext b
    constructor
    · intro hb
      simpa using (h b hb)
    · intro hb
      simpa using (hb : b = a) ▸ ha
  obtain ⟨b, hb, hab⟩ :=
    cliqueModel_actual_edge_for_contraction M i a ha haR hother
  have hbR : b ∉ Set.range root := by
    intro h
    exact (Set.disjoint_left.mp havoid) hb h
  exact ⟨i, a, b, ha, hb, hab, haR, hbR⟩
namespace RootAttachedCliqueModel

/-- Forget the root attachments, retaining the underlying clique model. -/
def toMinorModel {V : Type*} {G : SimpleGraph V} {r : ℕ}
    {root : Fin r → V} (M : RootAttachedCliqueModel G root) :
    MinorModel (SimpleGraph.completeGraph (Fin r)) G where
  branch := M.branch
  connected := M.connected
  disjoint := M.disjoint
  adjacent := by
    intro i j hij
    exact M.adjacent hij

end RootAttachedCliqueModel

namespace ConnectedPartition

/-- Lift an attached model through a connected partition when the block of
each prescribed root is a singleton. -/
noncomputable def liftRootAttached_of_singleton_roots
    {V I : Type*} {G : SimpleGraph V} {r : ℕ}
    (P : ConnectedPartition G I) (root : Fin r → V)
    (hsingle : ∀ i, P.block (P.index (root i)) = {root i})
    (M : RootAttachedCliqueModel P.touchingQuotient (P.index ∘ root)) :
    RootAttachedCliqueModel G root := by
  let N := M.toMinorModel.comp P.toMinorModel
  refine {
    branch := N.branch
    root_injective := ?_
    connected := N.connected
    disjoint := N.disjoint
    avoids_roots := ?_
    adjacent := fun hij => N.adjacent hij
    attached := ?_
  }
  · intro i j hij
    exact M.root_injective (congrArg P.index hij)
  · intro i j hroot
    obtain ⟨q, hq, hmem⟩ := hroot
    have hqroot : P.index (root j) = q := P.index_eq_of_mem hmem
    change q ∈ M.branch i at hq
    exact M.avoids_roots i j (by
      simpa only [Function.comp_apply, hqroot] using hq)
  · intro i
    obtain ⟨q, hq, hqadj⟩ := M.attached i
    obtain ⟨_, u, hu, v, hv, huv⟩ := hqadj
    have hu' : u = root i := by
      have hu'' : u ∈ ({root i} : Set V) := by
        simpa only [Function.comp_apply, hsingle i] using hu
      simpa using hu''
    subst u
    exact ⟨v, ⟨q, hq, hv⟩, huv⟩

end ConnectedPartition

/-- An attached clique model in an edge contraction lifts if both endpoints
of the contracted edge avoid the prescribed roots. -/
noncomputable def liftRootAttached_edgeContraction
    {V : Type*} {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) {r : ℕ} (root : Fin r → V)
    (ha : a ∉ Set.range root) (hb : b ∉ Set.range root)
    (M : RootAttachedCliqueModel (edgeContraction G hab)
      (edgeContractionRoot hab root)) :
    RootAttachedCliqueModel G root := by
  let P := edgeContractionPartition G hab
  apply P.liftRootAttached_of_singleton_roots root
  · intro i
    have hria : root i ≠ a := by
      intro h
      exact ha ⟨i, h⟩
    have hrib : root i ≠ b := by
      intro h
      exact hb ⟨i, h⟩
    have heq : P.index (root i) = some ⟨root i, hria, hrib⟩ :=
      P.index_eq_of_mem (by simp [P, edgeContractionPartition,
        edgeContractionBlock])
    rw [heq]
    rfl
  · exact M

end HadwigerLean
