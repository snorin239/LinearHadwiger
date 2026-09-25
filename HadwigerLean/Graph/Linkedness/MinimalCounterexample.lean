import HadwigerLean.Graph.Linkedness.CoreTightDichotomy
import HadwigerLean.Graph.Linkedness.ContractionLift
import HadwigerLean.Graph.Linkedness.RigidTorso
import HadwigerLean.Graph.Linkedness.TorsoFarGlue
import Mathlib.Tactic

namespace HadwigerLean
namespace Linkedness

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The boundary of a separation, viewed inside its right side, has exactly
as many vertices as the original adhesion. -/
theorem separationBoundaryFinset_card_eq
    {G : SimpleGraph V} (S : VertexSeparation G) :
    (separationBoundaryFinset S).card = Nat.card S.separator := by
  classical
  have himage : (separationBoundaryFinset S).image Subtype.val =
      S.separatorFinset := by
    ext v
    simp [separationBoundaryFinset, VertexSeparation.separatorFinset,
      VertexSeparation.separator]
  have hcard := Finset.card_image_of_injective
    (separationBoundaryFinset S) Subtype.val_injective
  rw [himage] at hcard
  simpa [VertexSeparation.separatorFinset] using hcard.symm

/-- Removing one vertex strictly reduces the order. -/
theorem vertexDeletion_order_lt (z : V) :
    Fintype.card {v : V // v ≠ z} < Fintype.card V := by
  classical
  exact Fintype.card_subtype_lt (p := fun v : V => v ≠ z) (x := z) (by simp)

/-- A single-edge contraction has one fewer vertex. -/
theorem edgeContraction_order_lt_linkedness
    (G : SimpleGraph V) {a b : V} (hab : G.Adj a b) :
    Fintype.card (EdgeContractionVertex a b) < Fintype.card V := by
  classical
  let S : Finset V := {a, b}ᶜ
  have hout : Fintype.card {x : V // x ≠ a ∧ x ≠ b} = S.card := by
    apply Fintype.card_of_subtype
    intro x
    simp [S]
  have hpair : ({a, b} : Finset V).card = 2 := Finset.card_pair hab.ne
  have htotal : S.card + 2 = Fintype.card V := by
    have h := Finset.card_compl_add_card ({a, b} : Finset V)
    simpa [S, hpair] using h
  change Fintype.card (Option {x : V // x ≠ a ∧ x ≠ b}) < Fintype.card V
  rw [Fintype.card_option, hout]
  omega
/-- The smaller-order induction applies to a proper induced shore when its
adhesion has at most `2k` vertices. -/
theorem rootedLinked_induced_shore_of_smaller_order
    (G : SimpleGraph V) (k : ℕ) (S : VertexSeparation G)
    (horder : Nat.card S.right < Fintype.card V)
    (hsep : Nat.card S.separator ≤ 2 * k)
    (hm : MassedPair (G.induce S.right)
      {u : S.right | (u : V) ∈ S.left} ((8 * k : ℕ) : ℝ))
    (hsmall : ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) (Y : Finset W),
      Fintype.card W < Fintype.card V →
      Y.card ≤ 2 * k →
      MassedPair H (Y : Set W) ((8 * k : ℕ) : ℝ) →
      RootedLinked H Y) :
    RootedLinked (G.induce S.right) (separationBoundaryFinset S) := by
  classical
  apply hsmall (G.induce S.right) (separationBoundaryFinset S)
  · simpa only [Nat.card_eq_fintype_card] using horder
  · rw [separationBoundaryFinset_card_eq]
    exact hsep
  · simpa [separationBoundaryFinset] using hm

/-- A torso contains at most the original number of roots. -/
theorem torsoRootFinset_card_le
    {G : SimpleGraph V} (S : VertexSeparation G) (X : Finset V) :
    (torsoRootFinset S X).card ≤ X.card := by
  classical
  let Y := torsoRootFinset S X
  have hsub : Y.image Subtype.val ⊆ X := by
    intro x hx
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    exact (mem_torsoRootFinset S X u).mp hu
  rw [← Finset.card_image_of_injective Y Subtype.val_injective]
  exact Finset.card_le_card hsub

/-- A lower-order rigid far shore is impossible under the smaller-order
massed-pair induction. This instantiates the torso gluing theorem. -/
theorem rootedLinked_of_lower_rigid_of_smaller_order
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (k : ℕ) (hXupper : X.card ≤ 2 * k)
    (hm : MassedPair G (X : Set V) ((8 * k : ℕ) : ℝ))
    (hsmall : ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) (Y : Finset W),
      Fintype.card W < Fintype.card V →
      Y.card ≤ 2 * k →
      MassedPair H (Y : Set W) ((8 * k : ℕ) : ℝ) →
      RootedLinked H Y)
    (hex : ∃ S : VertexSeparation G,
      (X : Set V) ⊆ S.left ∧ S.strictRight.Nonempty ∧
      Nat.card S.separator < X.card ∧
      RootedLinked (G.induce S.right) (separationBoundaryFinset S)) :
    RootedLinked G X := by
  classical
  apply rootedLinked_of_lower_rigid_and_smaller_massed
    G X ((8 * k : ℕ) : ℝ) hm ?_ ?_ ?_ hex
  · intro S _ hnear hmS
    exact hsmall (torsoGraph G S) (torsoRootFinset S X)
      (by simpa only [Nat.card_eq_fintype_card] using hnear)
      ((torsoRootFinset_card_le S X).trans hXupper) hmS
  · intro S _ hnear T horder hsep hmT
    have hrootcard := torsoRootFinset_card_le S X
    have hsmallNear : ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (H : SimpleGraph W) (Y : Finset W),
        Fintype.card W < Fintype.card S.left →
        Y.card ≤ 2 * k →
        MassedPair H (Y : Set W) ((8 * k : ℕ) : ℝ) →
        RootedLinked H Y := by
      intro W _ _ H Y hW hY hmY
      have hn : Fintype.card S.left < Fintype.card V := by
        simpa only [Nat.card_eq_fintype_card] using hnear
      exact hsmall H Y (lt_trans hW hn) hY hmY
    exact rootedLinked_induced_shore_of_smaller_order
      (torsoGraph G S) k T horder (by omega) hmT hsmallNear
  · intro S _ T hBoundary hfar hT
    exact rootedLinked_glueTorsoFar S T hBoundary hfar hT
/-- Saturating edges wholly inside the root set leaves exterior incidence
unchanged. -/
theorem rootPairSaturation_incidence
    (G : SimpleGraph V) (X : Finset V) {ι : Type*}
    (P : IndexedPairs ι V) :
    edgeIncidenceSetCount (rootPairSaturation G X P) (X : Set V)ᶜ =
      edgeIncidenceSetCount G (X : Set V)ᶜ := by
  classical
  let H := rootPairSaturation G X P
  have hGH : G ≤ H := by
    intro a b hab
    exact Or.inl hab
  have hnew : ∀ a b, H.Adj a b → ¬G.Adj a b →
      a ∈ X ∧ b ∈ X := by
    intro a b hH hnot
    rcases hH with hG | hAdded
    · exact False.elim (hnot hG)
    · exact ⟨hAdded.2.1,hAdded.2.2.1⟩
  have hdis : Disjoint (X : Set V)ᶜ (X : Set V) := by
    apply Set.disjoint_left.mpr
    intro x hx hX
    exact hx hX
  exact incidence_eq_of_root_extension X (X : Set V)ᶜ hGH hnew hdis
/-- The D.2--D.5 extremal argument, with the D.1 no-rigid statement and the
root-saturation invariant exposed. The recursive assumptions cover exactly
smaller orders and smaller outside-edge incidence counts. -/
theorem rootedLinked_of_massed_extremal
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (k : ℕ) (hk : 0 < k)
    (hXupper : X.card ≤ 2 * k)
    (hm : MassedPair G (X : Set V) ((8 * k : ℕ) : ℝ))
    (hmissing : ∀ x ∈ X, (X.erase x \ G.neighborFinset x).card ≤ 1)
    (hno : NoRigidSeparation G (X : Set V))
    (hsmall : ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) (Y : Finset W),
      Fintype.card W < Fintype.card V →
      Y.card ≤ 2 * k →
      MassedPair H (Y : Set W) ((8 * k : ℕ) : ℝ) →
      RootedLinked H Y)
    (hsame : ∀ H : SimpleGraph V,
      edgeIncidenceSetCount H (X : Set V)ᶜ <
        edgeIncidenceSetCount G (X : Set V)ᶜ →
      MassedPair H (X : Set V) ((8 * k : ℕ) : ℝ) →
      RootedLinked H X) :
    RootedLinked G X := by
  classical
  by_contra hbad
  have hXlower : 2 ≤ X.card := root_card_ge_two_of_not_rootedLinked G X hbad
  have houtside : ∃ v : V, v ∉ X := by
    by_contra h
    push Not at h
    have hXu : X = Finset.univ := Finset.eq_univ_of_forall h
    have hg := hm.global
    simp [hXu, edgeIncidenceSetCount, edgeIncidenceSet] at hg
  have hneighbor : ∀ v ∉ X, ∃ u, G.Adj v u := by
    apply outside_has_neighbor_of_linked_vertex_deletions G X
      ((8 * k : ℕ) : ℝ) (by positivity) hm hbad
    intro z hz hmZ
    let S : Set V := {v : V | v ≠ z}
    let Y : Finset S := Finset.univ.filter (fun u => (u : V) ∈ X)
    have hYsub : Y.image Subtype.val ⊆ X := by
      intro v hv
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
      simpa [Y] using hu
    have hYcard : Y.card ≤ X.card := by
      rw [← Finset.card_image_of_injective Y Subtype.val_injective]
      exact Finset.card_le_card hYsub
    exact hsmall (G.induce S) Y
      (by change Fintype.card {v : V // v ≠ z} < Fintype.card V
          exact vertexDeletion_order_lt z)
      (hYcard.trans hXupper) (by simpa [S,Y] using hmZ)
  have hcommon : ∀ u v, v ∉ X → G.Adj u v →
      8 * k - 1 ≤ (G.neighborFinset u ∩ G.neighborFinset v).card := by
    intro a b hb hab
    have hquot : Fintype.card (EdgeContractionVertex a b) <
        Fintype.card V := edgeContraction_order_lt_linkedness G hab
    have hsmallQ : ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (H : SimpleGraph W) (Y : Finset W),
        Fintype.card W < Fintype.card (EdgeContractionVertex a b) →
        Y.card ≤ 2 * k →
        MassedPair H (Y : Set W) ((8 * k : ℕ) : ℝ) →
        RootedLinked H Y := by
      intro W _ _ H Y hW hY hmY
      exact hsmall H Y (lt_trans hW hquot) hY hmY
    apply common_neighbors_ge_of_noRigid_minimality hab X hb (8 * k)
      hm hbad hmissing hno
    · intro S horder hsep hmS
      have hYcard : Nat.card
          (partitionIndex (edgeContractionPartition G hab) '' (X : Set V)) ≤
          X.card := by
        simpa only [Nat.card_coe_set_eq, Set.ncard_coe_finset] using
          Set.ncard_image_le (Set.toFinite (X : Set V))
      exact rootedLinked_induced_shore_of_smaller_order
        (edgeContraction G hab) k S horder (by omega) hmS hsmallQ
    · intro T horder hsep hmT
      exact rootedLinked_induced_shore_of_smaller_order
        G k T horder (by omega) hmT hsmall
    · intro hmH
      let f := partitionIndex (edgeContractionPartition G hab)
      have hYcard : (X.image f).card ≤ 2 * k := by
        exact (Finset.card_image_le).trans hXupper
      have hYset : ((X.image f : Finset (EdgeContractionVertex a b)) :
          Set (EdgeContractionVertex a b)) = f '' (X : Set V) := by
        ext y
        simp [f]
      exact hsmall (edgeContraction G hab) (X.image f) hquot hYcard
        (by simpa [f,hYset] using hmH)
  obtain ⟨v,hv⟩ := houtside
  obtain ⟨w,hvw⟩ := hneighbor v hv
  have hcommonVW : X.card ≤
      (G.neighborFinset w ∩ G.neighborFinset v).card := by
    have hc := hcommon w v hv hvw.symm
    omega
  have htight' := massed_global_edge_tight_of_minimal_bad
    G X (8 * k) hm hbad w v hvw.symm (Or.inr hv) hcommonVW (by
      intro hmDeleted
      apply hsame (G.deleteEdges {s(w,v)})
      · have hc := edgeIncidenceSetCount_delete_edge_add_one
          G X w v hvw.symm (Or.inr hv)
        omega
      · exact hmDeleted)
  have htight : edgeIncidenceSetCount G (X : Set V)ᶜ =
      (8 * k) * (Xᶜ).card + 1 := by
    have hcompCard : ((X : Set V)ᶜ).ncard = (Xᶜ).card := by
      change Nat.card {v : V // v ∉ (X : Set V)} = (Xᶜ).card
      rw [Nat.card_eq_fintype_card]
      apply Fintype.card_of_finset' (p := {v : V | v ∉ (X : Set V)}) (Xᶜ)
      intro v
      simp
    rwa [hcompCard] at htight'
  obtain hlinked | ⟨S,hroot,hfar,hsep,hfarLinked⟩ :=
    rootedLinked_or_rigid_of_edge_tight G X k hk hXlower hXupper
      hm htight hneighbor hcommon
  · exact hbad hlinked
  · have hsep' : Nat.card S.separator ≤ Nat.card (X : Set V) := by
      have hc : Nat.card S.separator = S.separatorFinset.card := by
        simp [VertexSeparation.separatorFinset]
      simpa only [hc, Nat.card_coe_set_eq, Set.ncard_coe_finset] using
        (Nat.le_of_lt hsep)
    exact hno S hroot hfar hsep' hfarLinked

end Linkedness
end HadwigerLean
