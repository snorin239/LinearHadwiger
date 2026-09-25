import HadwigerLean.Graph.DensityBasic
import HadwigerLean.Graph.VertexConnectivity

/-!
# Massed graph-root pairs

The two density conditions are the common invariant in the linkedness and
rooted-density proofs.  In particular, the far-side condition quantifies
over *all* vertex separations of order below the root-set size.
-/

namespace HadwigerLean

universe u

variable {V : Type u} [Fintype V]

/-- Edges of `G` with at least one endpoint in `S`. -/
def edgeIncidenceSet (G : SimpleGraph V) (S : Set V) : Set G.edgeSet :=
  {e | ∃ v ∈ S, v ∈ (e.1 : Sym2 V)}

/-- The number of edges meeting a vertex set. -/
noncomputable def edgeIncidenceSetCount (G : SimpleGraph V) (S : Set V) : ℕ :=
  Nat.card (edgeIncidenceSet G S)

/-- The density invariant from (F.1) and (F.2) of the proof manuscript. -/
structure MassedPair (G : SimpleGraph V) (R : Set V) (α : ℝ) : Prop where
  global : α * (Nat.card {v : V // v ∉ R} : ℝ) < (edgeIncidenceSetCount G Rᶜ : ℝ)
  shore : ∀ S : VertexSeparation G,
    R ⊆ S.left → Nat.card S.separator < Nat.card R →
      (edgeIncidenceSetCount G S.strictRight : ℝ) ≤
        α * (Nat.card S.strictRight : ℝ)

end HadwigerLean
