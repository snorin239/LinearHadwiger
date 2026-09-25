import HadwigerLean.Graph.RootedCliqueMinor.SeparatorRestriction

/-!
# Connectivity of a completed separator torso

An r-connected graph remains r-connected on either side of an order-r
separation after the boundary is completed to a clique. We use the
generic connected-set restriction theorem to project paths that leave
the chosen side.
-/

namespace HadwigerLean

namespace VertexSeparation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} (S : VertexSeparation G)

/-- Deleting fewer than r vertices from the right torso leaves it
connected, provided the boundary contains at least r vertices. -/
theorem torso_connected_delete (r : ℕ)
    (hconn : VertexConnected G r)
    (hX : r ≤ S.separatorFinset.card)
    (D : Finset S.right) (hD : D.card < r) :
    (S.torso.induce (D : Set S.right)ᶜ).Connected := by
  classical
  let E : Finset V := D.image Subtype.val
  have hEcard : E.card < r := by
    have hle : E.card ≤ D.card := Finset.card_image_le
    omega
  let C : Set V := (E : Set V)ᶜ
  have hGC : (G.induce C).Connected := hconn.connected_delete E hEcard
  have hpick : E.card < S.separatorFinset.card := by omega
  obtain ⟨x, hxX, hxE⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hpick
  have hright : ∃ x ∈ C, x ∈ S.right :=
    ⟨x, hxE, (S.mem_separatorFinset x).mp hxX |>.2⟩
  have hset : {x : S.right | (x : V) ∈ C} = (D : Set S.right)ᶜ := by
    ext x
    have hmem : (x : V) ∈ E ↔ x ∈ D := by
      constructor
      · intro hx
        obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
        have heq : y = x := Subtype.ext hxy
        simpa [heq] using hy
      · intro hx
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    simpa [C] using not_congr hmem
  rw [← hset]
  exact S.connected_restrict_torso C hGC hright

/-- Completing the order-r boundary of a separation preserves
r-connectivity on a nonempty far side. -/
theorem torso_vertexConnected [Fintype S.right] (r : ℕ)
    (hconn : VertexConnected G r)
    (hX : S.separatorFinset.card = r)
    (hfar : S.strictRight.Nonempty) :
    VertexConnected S.torso r := by
  classical
  refine ⟨?_, ?_⟩
  · let Y : Finset V := S.right.toFinset
    have hsub : S.separatorFinset ⊆ Y := by
      intro x hx
      exact Set.mem_toFinset.mpr ((S.mem_separatorFinset x).mp hx).2
    obtain ⟨v, hvR, hvL⟩ := hfar
    have hvY : v ∈ Y := Set.mem_toFinset.mpr hvR
    have hvX : v ∉ S.separatorFinset := by
      intro h
      exact hvL ((S.mem_separatorFinset v).mp h).1
    have hstrict : S.separatorFinset ⊂ Y := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hsub, ?_⟩
      intro heq
      exact hvX (heq ▸ hvY)
    have hcard := Finset.card_lt_card hstrict
    simpa [Y, hX] using hcard
  · intro D hD
    exact S.torso_connected_delete r hconn (by omega) D hD


/-- If an order-r boundary contains a nonroot while all r roots are on
the left, some root lies in the strict left side. -/
theorem strictLeft_nonempty_of_nonroot_boundary
    {r : ℕ} (root : Fin r → V) (hroot : Function.Injective root)
    (hroots : ∀ i, root i ∈ S.left)
    (hX : S.separatorFinset.card = r)
    {u : V} (huX : u ∈ S.separatorFinset)
    (huR : u ∉ Set.range root) :
    S.strictLeft.Nonempty := by
  classical
  by_contra hnone
  let R : Finset V := Finset.univ.image root
  have hRcard : R.card = r := by
    simp [R, Finset.card_image_of_injective _ hroot]
  have hRsub : R ⊆ S.separatorFinset := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    apply (S.mem_separatorFinset (root i)).mpr
    refine ⟨hroots i, ?_⟩
    by_contra hnot
    exact hnone ⟨root i, hroots i, hnot⟩
  have hR : R = S.separatorFinset :=
    Finset.eq_of_subset_of_card_le hRsub (by omega)
  have hu : u ∈ R := hR.symm ▸ huX
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hu
  exact huR ⟨i, hi⟩

/-- A nonempty strict left side makes the right torso strictly smaller
than the original finite graph. -/
theorem right_order_lt_of_strictLeft_nonempty
    [Fintype S.right] (hleft : S.strictLeft.Nonempty) :
    Fintype.card S.right < Fintype.card V := by
  classical
  let Y : Finset V := S.right.toFinset
  obtain ⟨v, hvL, hvR⟩ := hleft
  have hsub : Y ⊂ (Finset.univ : Finset V) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    have hvY : v ∈ Y := by rw [heq]; simp
    exact hvR (Set.mem_toFinset.mp (by simpa [Y] using hvY))
  have hcard := Finset.card_lt_card hsub
  simpa [Y] using hcard
end VertexSeparation

end HadwigerLean
