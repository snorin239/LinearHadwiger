import HadwigerLean.Woven.ThreeChildGN

/-!
# Three connected chromatic children

Two separability applications make three disjoint colorful sets. Applying
the additive GN theorem in each set gives three pairwise disjoint connected
children with a uniform chromatic-loss ledger.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The chromatic/separability extraction needed by the geometric three-child
assembly, with the two separation losses and the GN loss made explicit. -/
theorem three_connected_chromatic_pieces_of_separation
    (G : SimpleGraph V) (Y : Finset V) (s κ : ℕ)
    (hκpos : 0 < κ)
    (hsep : ∀ X : Finset V, X ⊆ Y →
      2 * s < chromatic (G.induce (X : Set V)) →
      Bootstrap.ChromaticSeparable (G.induce (X : Set V)) s)
    (hχsep : 3 * s < chromatic (G.induce (Y : Set V)))
    (hχGN : 2 * s + 7 * κ ≤ chromatic (G.induce (Y : Set V))) :
    ∃ H : Fin 3 → Finset V,
      (∀ i, H i ⊆ Y) ∧
      (Pairwise fun i j => Disjoint (H i) (H j)) ∧
      (∀ i, VertexConnected (G.induce (H i : Set V)) κ) ∧
      (∀ i, chromatic (G.induce (Y : Set V)) ≤
        chromatic (G.induce (H i : Set V)) + 2 * s + 6 * κ) := by
  classical
  obtain ⟨J,hJY,hJdis,hJchrom⟩ :=
    three_chromatic_pieces_of_separation G Y s hsep hχsep
  have hGN (i : Fin 3) :
      ∃ H : Finset V,
        H ⊆ J i ∧
        VertexConnected (G.induce (H : Set V)) κ ∧
        chromatic (G.induce (J i : Set V)) ≤
          chromatic (G.induce (H : Set V)) + 6 * κ := by
    apply exists_chromatic_connected_inside G (J i) κ hκpos
    have h := hJchrom i
    omega
  choose H hHJ hconn hGNchrom using hGN
  refine ⟨H, ?_, ?_, hconn, ?_⟩
  · intro i
    exact (hHJ i).trans (hJY i)
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    exact (Finset.disjoint_left.mp (hJdis hij))
      (hHJ i hxi) (hHJ j hxj)
  · intro i
    have h₁ := hJchrom i
    have h₂ := hGNchrom i
    omega

end Woven
end HadwigerLean
