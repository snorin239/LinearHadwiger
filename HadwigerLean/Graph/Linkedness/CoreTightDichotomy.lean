import HadwigerLean.Graph.Linkedness.CoreDichotomy
import HadwigerLean.Graph.Linkedness.CoreAmbient
import HadwigerLean.Graph.Linkedness.Core
import HadwigerLean.Graph.VertexConnectivityIso
import Mathlib.Tactic
namespace HadwigerLean
namespace Linkedness

/-- The edge-tight massed estimates imply rooted linkedness or a rigid
separation, by passing through a small dense closed neighborhood. -/
theorem rootedLinked_or_rigid_of_edge_tight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (k : ℕ) (hk : 0 < k)
    (hXlower : 2 ≤ X.card) (hXupper : X.card ≤ 2 * k)
    (hm : MassedPair G (X : Set V) ((8 * k : ℕ) : ℝ))
    (htight : edgeIncidenceSetCount G (X : Set V)ᶜ =
      (8 * k) * (Xᶜ).card + 1)
    (hneighbor : ∀ v ∉ X, ∃ u, G.Adj v u)
    (hcommon : ∀ u v, v ∉ X → G.Adj u v →
      8 * k - 1 ≤ (G.neighborFinset u ∩ G.neighborFinset v).card) :
    RootedLinked G X ∨
      ∃ S : VertexSeparation G,
        (X : Set V) ⊆ S.left ∧ S.strictRight.Nonempty ∧
        S.separatorFinset.card < X.card ∧
        RootedLinked (G.induce S.right) (separationBoundaryFinset S) := by
  classical
  obtain ⟨v,hv,horder,hdegree⟩ :=
    exists_small_dense_core_of_tight_right G X k hk hXlower hXupper
      hm htight hneighbor hcommon
  let S : Finset V := Finset.univ.filter (fun w => w = v ∨ G.Adj v w)
  have hSset : (S : Set V) = {w | w = v ∨ G.Adj v w} := by
    ext w
    simp [S]
  have hSnon : S.Nonempty := by
    refine ⟨v, ?_⟩
    simp [S]
  have hScard : S.card ≤ 16 * k := by
    simpa [S] using horder
  have hSdegree : ∀ u : (S : Set V),
      8 * k ≤ (G.induce (S : Set V)).degree u := by
    let e : G.induce (S : Set V) ≃g G.induce {w | w = v ∨ G.Adj v w} := {
      toEquiv := Equiv.setCongr hSset
      map_rel_iff' := by
        intro x y
        rfl
    }
    intro u
    rw [degree_eq_of_iso e u]
    exact hdegree (e u)
  obtain ⟨J,hJnon,hJsub,hJlo,hJhi,hJrooted⟩ :=
    exists_ambient_small_rooted_core G S hSnon k hk hScard hSdegree
  let e : X ≃ Fin X.card := Fintype.equivFinOfCardEq (by simp)
  let root : Fin X.card → V := fun i => (e.symm i).1
  have hroot : Function.Injective root := by
    intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij
  have hrootImage : Finset.univ.image root = X := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hx
      rw [← hi]
      exact (e.symm i).property
    · intro hx
      apply Finset.mem_image.mpr
      refine ⟨e ⟨x,hx⟩,Finset.mem_univ _,?_⟩
      simp [root]
  have hJge : X.card ≤ J.card := by omega
  obtain hlinked | ⟨Q,hQroot,hQfar,hQsmall,hQlinked⟩ :=
    rootedLinked_or_rigid_shore_of_rooted_core G root hroot J hJge
      hXupper hJrooted
  · exact Or.inl (hrootImage ▸ hlinked)
  · right
    refine ⟨Q,?_,hQfar,?_,hQlinked⟩
    · intro x hx
      have hxR : x ∈ Finset.univ.image root := hrootImage.symm ▸ hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hxR
      exact hQroot i
    · exact hQsmall

end Linkedness
end HadwigerLean
