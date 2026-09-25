import HadwigerLean.Graph.RootedDensity.PartitionLift
import HadwigerLean.Graph.Linkedness.Massed
import Mathlib.Tactic

/-!
# Real-parameter incidence loss under edge contraction

The massed-pair parameter in Appendix F is a real number.  Strict mass
before contraction and failure afterward force at least its natural floor
in edge incidences to disappear beyond the contracted edge itself.
-/

namespace HadwigerLean.RootedDensity

/-- Arithmetic core of Appendix F.b: an integer incidence loss of
`1+c+ε` across one outside vertex gives `⌊α⌋₊≤c+ε`. -/
theorem floor_le_loss_of_real_mass_drop
    (α : ℝ) (m before after c ε : ℕ)
    (hα : 0 ≤ α) (hm : 0 < m)
    (hbefore : α * (m : ℝ) < (before : ℝ))
    (hafter : (after : ℝ) ≤ α * ((m - 1 : ℕ) : ℝ))
    (hbalance : after + 1 + c + ε = before) :
    Nat.floor α ≤ c + ε := by
  have hmstep : m - 1 + 1 = m := by omega
  have hmreal : (((m - 1 : ℕ) : ℝ) + 1) = (m : ℝ) := by
    exact_mod_cast hmstep
  have hbalreal : (after : ℝ) + 1 + c + ε = before := by
    exact_mod_cast hbalance
  have hlt : α < (c + ε + 1 : ℕ) := by
    push_cast
    nlinarith
  have hfloor : (Nat.floor α : ℝ) ≤ α := Nat.floor_le hα
  have hnat : Nat.floor α < c + ε + 1 := by
    exact_mod_cast lt_of_le_of_lt hfloor hlt
  omega


universe u

/-- In the exterior-edge case of F.b, failure of the strict global mass
condition after contraction gives at least `⌊α⌋₊` common neighbors. -/
theorem floor_le_common_of_exterior_contraction_failure
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (α : ℝ) (hα : 0 ≤ α)
    (hm : MassedPair G (X : Set V) α)
    {a b : V} (hab : G.Adj a b) (ha : a ∉ X) (hb : b ∉ X)
    (hfail : let P := edgeContractionPartition G hab
      let Y : Set (EdgeContractionVertex a b) :=
        Linkedness.partitionIndex P '' (X : Set V)
      (edgeIncidenceSetCount (edgeContraction G hab) Yᶜ : ℝ) ≤
        α * ((Yᶜ).ncard : ℝ)) :
    Nat.floor α ≤ (G.neighborFinset a ∩ G.neighborFinset b).card := by
  classical
  let P := edgeContractionPartition G hab
  let Y : Set (EdgeContractionVertex a b) :=
    Linkedness.partitionIndex P '' (X : Set V)
  let Q := edgeContraction G hab
  have hnoneY : none ∉ Y := by
    rintro ⟨x, hx, hidx⟩
    have hxa : x ≠ a := by intro h; exact ha (h ▸ hx)
    have hxb : x ≠ b := by intro h; exact hb (h ▸ hx)
    have hs : Linkedness.partitionIndex P x =
        some (⟨x, hxa, hxb⟩ : EdgeOutside a b) :=
      Linkedness.edgeContraction_index_some hab x hxa hxb
    rw [hs] at hidx
    cases hidx
  have hpre : Linkedness.partitionIndex P ⁻¹' Yᶜ = (X : Set V)ᶜ := by
    ext x
    constructor
    · intro hx hroot
      exact hx ⟨x, hroot, rfl⟩
    · intro hx himage
      obtain ⟨y, hy, heq⟩ := himage
      have hya : y ≠ a := by intro h; exact ha (h ▸ hy)
      have hyb : y ≠ b := by intro h; exact hb (h ▸ hy)
      have hySome : Linkedness.partitionIndex P y ≠ none := by
        rw [Linkedness.edgeContraction_index_some hab y hya hyb]
        simp
      have hxSome : Linkedness.partitionIndex P x ≠ none := by
        rw [← heq]
        exact hySome
      have hxy : x = y :=
        Linkedness.edgeContraction_index_inj_away hab hxSome heq.symm
      exact hx (hxy ▸ hy)
  have hsize : ((X : Set V)ᶜ).ncard = (Yᶜ).ncard + 1 := by
    rw [← hpre]
    exact Linkedness.edgeContraction_preimage_card_of_mem_contract
      hab Yᶜ hnoneY
  have hmpos : 0 < ((X : Set V)ᶜ).ncard :=
    (Set.ncard_pos).mpr ⟨a, ha⟩
  have hdrop : edgeIncidenceSetCount Q Yᶜ + 1 +
      (G.neighborFinset a ∩ G.neighborFinset b).card =
        edgeIncidenceSetCount G (X : Set V)ᶜ := by
    have hfin := Linkedness.edgeContraction_incidence_drop_outside
      hab X ha hb
    change edgeIncidenceCount Q Y.toFinsetᶜ + 1 +
      (G.neighborFinset a ∩ G.neighborFinset b).card =
        edgeIncidenceCount G Xᶜ at hfin
    have hQ : edgeIncidenceCount Q Y.toFinsetᶜ =
        edgeIncidenceSetCount Q Yᶜ := by
      simpa using (Linkedness.incidenceSetCount_eq_finsetCount
        Q Y.toFinsetᶜ).symm
    have hG : edgeIncidenceCount G Xᶜ =
        edgeIncidenceSetCount G (X : Set V)ᶜ := by
      simpa using (Linkedness.incidenceSetCount_eq_finsetCount G Xᶜ).symm
    rw [hQ, hG] at hfin
    exact hfin
  have hglobal : α * (((X : Set V)ᶜ).ncard : ℝ) <
      (edgeIncidenceSetCount G (X : Set V)ᶜ : ℝ) := by
    simpa only [show Nat.card {v : V // v ∉ (X : Set V)} =
      ((X : Set V)ᶜ).ncard from rfl] using hm.global
  apply floor_le_loss_of_real_mass_drop α
    ((X : Set V)ᶜ).ncard
    (edgeIncidenceSetCount G (X : Set V)ᶜ)
    (edgeIncidenceSetCount Q Yᶜ)
    (G.neighborFinset a ∩ G.neighborFinset b).card 0 hα hmpos hglobal
  · simpa only [hsize, Nat.add_sub_cancel_right] using hfail
  · simpa using hdrop

/-- In the root-exterior case of F.b, failure of strict mass after
contraction forces `⌊α⌋₊` common neighbors plus the exact root-incidence
correction. No near-completeness assumption on the root graph is needed. -/
theorem floor_le_common_add_rootCorrection_of_contraction_failure
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (α : ℝ) (hα : 0 ≤ α)
    (hm : MassedPair G (X : Set V) α)
    {a b : V} (hab : G.Adj a b) (ha : a ∈ X) (hb : b ∉ X)
    (hfail : let P := edgeContractionPartition G hab
      let Y : Set (EdgeContractionVertex a b) :=
        Linkedness.partitionIndex P '' (X : Set V)
      (edgeIncidenceSetCount (edgeContraction G hab) Yᶜ : ℝ) ≤
        α * ((Yᶜ).ncard : ℝ)) :
    Nat.floor α ≤
      (G.neighborFinset a ∩ G.neighborFinset b).card +
      ((G.neighborFinset b ∩ X.erase a) \ G.neighborFinset a).card := by
  classical
  let P := edgeContractionPartition G hab
  let Y : Set (EdgeContractionVertex a b) :=
    Linkedness.partitionIndex P '' (X : Set V)
  let Q := edgeContraction G hab
  let ε := ((G.neighborFinset b ∩ X.erase a) \ G.neighborFinset a).card
  have hsize : ((X : Set V)ᶜ).ncard = (Yᶜ).ncard + 1 :=
    Linkedness.edgeContraction_root_compl_card hab X ha hb
  have hmpos : 0 < ((X : Set V)ᶜ).ncard :=
    (Set.ncard_pos).mpr ⟨b, hb⟩
  have hdrop : edgeIncidenceSetCount Q Yᶜ + 1 +
      (G.neighborFinset a ∩ G.neighborFinset b).card + ε =
        edgeIncidenceSetCount G (X : Set V)ᶜ := by
    have hfin := Linkedness.edgeContraction_incidence_drop_root hab X ha hb
    change edgeIncidenceCount Q Y.toFinsetᶜ + 1 +
      (G.neighborFinset a ∩ G.neighborFinset b).card + ε =
        edgeIncidenceCount G Xᶜ at hfin
    have hQ : edgeIncidenceCount Q Y.toFinsetᶜ =
        edgeIncidenceSetCount Q Yᶜ := by
      simpa using (Linkedness.incidenceSetCount_eq_finsetCount
        Q Y.toFinsetᶜ).symm
    have hG : edgeIncidenceCount G Xᶜ =
        edgeIncidenceSetCount G (X : Set V)ᶜ := by
      simpa using (Linkedness.incidenceSetCount_eq_finsetCount G Xᶜ).symm
    rw [hQ, hG] at hfin
    exact hfin
  have hglobal : α * (((X : Set V)ᶜ).ncard : ℝ) <
      (edgeIncidenceSetCount G (X : Set V)ᶜ : ℝ) := by
    simpa only [show Nat.card {v : V // v ∉ (X : Set V)} =
      ((X : Set V)ᶜ).ncard from rfl] using hm.global
  apply floor_le_loss_of_real_mass_drop α
    ((X : Set V)ᶜ).ncard
    (edgeIncidenceSetCount G (X : Set V)ᶜ)
    (edgeIncidenceSetCount Q Yᶜ)
    (G.neighborFinset a ∩ G.neighborFinset b).card ε hα hmpos hglobal
  · simpa only [hsize, Nat.add_sub_cancel_right] using hfail
  · simpa using hdrop

/-- A convenient root-neighbor formulation of the previous exact bound. -/
theorem floor_le_common_add_otherRoots_of_contraction_failure
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (α : ℝ) (hα : 0 ≤ α)
    (hm : MassedPair G (X : Set V) α)
    {a b : V} (hab : G.Adj a b) (ha : a ∈ X) (hb : b ∉ X)
    (hfail : let P := edgeContractionPartition G hab
      let Y : Set (EdgeContractionVertex a b) :=
        Linkedness.partitionIndex P '' (X : Set V)
      (edgeIncidenceSetCount (edgeContraction G hab) Yᶜ : ℝ) ≤
        α * ((Yᶜ).ncard : ℝ)) :
    Nat.floor α ≤
      (G.neighborFinset a ∩ G.neighborFinset b).card +
      (X.erase a).card := by
  have hle := floor_le_common_add_rootCorrection_of_contraction_failure
    G X α hα hm hab ha hb hfail
  have hεle :
      ((G.neighborFinset b ∩ X.erase a) \ G.neighborFinset a).card ≤
        (X.erase a).card := by
    exact Finset.card_le_card
      ((Finset.sdiff_subset).trans Finset.inter_subset_right)
  omega
end HadwigerLean.RootedDensity