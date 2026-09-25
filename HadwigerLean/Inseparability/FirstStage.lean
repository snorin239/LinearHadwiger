import HadwigerLean.Inseparability.Stages
import HadwigerLean.Woven.ModelPathExtension
import HadwigerLean.Woven.ThreeChildResidualTransport

/-!
# The first sequential stage

At the first stage the terminal groups in the new connected piece are
singletons. Knitting those groups provides no clique edges. We instead use a
rooted clique model inside that piece and extend its branches along the
incoming disjoint paths. All clique-edge witnesses remain inside the piece,
while each extended branch meets the future chromatic region exactly at its
incoming path start.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x : ℕ}

/-- The first-stage `K_x` connector: a rooted model in the new piece supplies
the clique adjacencies absent from singleton knitting groups. -/
theorem first_stage_model_of_woven_piece
    (D H : Finset V)
    (hDH : Disjoint D H)
    (hW : Woven (G.induce (D : Set V)) x 0)
    (P : IndexedPairs (Fin x) V) (L : IndexedLinkage G P)
    (hfinishD : ∀ i, P.finish i ∈ D)
    (hstartH : ∀ i, P.start i ∈ H)
    (hcleanD : ∀ i v, v ∈ pathVertexSet (L.path i) →
      v ∈ D → v = P.finish i)
    (hcleanH : ∀ i v, v ∈ pathVertexSet (L.path i) →
      v ∈ H → v = P.start i) :
    ∃ M : RootedMinorModel (SimpleGraph.completeGraph (Fin x)) G P.start,
      (∀ i, M.branch i ⊆ (D : Set V) ∪ pathVertexSet (L.path i)) ∧
      (∀ i, M.branch i ∩ (H : Set V) = {P.start i}) ∧
      (∀ i j, i ≠ j →
        ∃ a ∈ M.branch i, ∃ b ∈ M.branch j,
          a ∈ D ∧ b ∈ D ∧ G.Adj a b) := by
  classical
  let rootD : Fin x → (D : Set V) :=
    fun i => ⟨P.finish i, hfinishD i⟩
  have hrootD : Function.Injective rootD := by
    intro i j hij
    exact L.finish_injective (congrArg Subtype.val hij)
  have hminor : HasRootedCliqueMinor (G.induce (D : Set V)) rootD :=
    hW.rooted_minor rootD hrootD
  obtain ⟨M₀,hM₀D⟩ := Woven.residual_rooted_model_of_induced_minor
    P.finish hfinishD hminor
  let M := Woven.RootedMinorModel.extendAlongCleanLinkage M₀ L (D : Set V) hM₀D hcleanD
  refine ⟨M, ?_, ?_, ?_⟩
  · intro i v hv
    rcases hv with hvM | hvP
    · exact Or.inl (hM₀D i hvM)
    · exact Or.inr hvP
  · intro i
    apply Set.Subset.antisymm
    · intro v hv
      rcases hv.1 with hvM | hvL
      · exact False.elim ((Finset.disjoint_left.mp hDH)
          (hM₀D i hvM) hv.2)
      · have heq := hcleanH i v hvL hv.2
        simpa [heq]
    · intro v hv
      have heq : v = P.start i := by simpa using hv
      subst v
      exact ⟨M.root_mem i, hstartH i⟩
  · intro i j hij
    obtain ⟨a,ha,b,hb,hab⟩ := M₀.adjacent hij
    exact ⟨a,Or.inl ha,b,Or.inl hb,hM₀D i ha,hM₀D j hb,hab⟩

end Inseparability
end HadwigerLean




