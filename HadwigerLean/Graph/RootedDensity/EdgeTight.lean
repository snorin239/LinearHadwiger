import HadwigerLean.Graph.RootedDensity.EdgeTightDegree
import HadwigerLean.Graph.RootedDensity.Universal
import HadwigerLean.Graph.Linkedness.EdgeDeletionShore
import Mathlib.Tactic

/-! The real-parameter F.3 edge-tight identity from incidence minimality. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- At a minimum-incidence nonuniversal massed pair, an exterior edge
whose deletion preserves every shore condition forces the exact F.3 count. -/
theorem floor_edge_tight_of_minimal_bad
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (α : ℝ) (hα : 0 ≤ α)
    (hm : MassedPair G (X : Set V) α)
    (hbad : ¬ UniversalAt G H X)
    (hsame : ∀ D : SimpleGraph V,
      edgeIncidenceSetCount D (X : Set V)ᶜ <
        edgeIncidenceSetCount G (X : Set V)ᶜ →
      MassedPair D (X : Set V) α → UniversalAt D H X)
    (a b : V) (hab : G.Adj a b) (hout : a ∉ X ∨ b ∉ X)
    (hshore : ∀ S : VertexSeparation (G.deleteEdges {s(a,b)}),
      (X : Set V) ⊆ S.left →
      Nat.card S.separator < Nat.card (X : Set V) →
      (edgeIncidenceSetCount (G.deleteEdges {s(a,b)}) S.strictRight : ℝ) ≤
        α * (Nat.card S.strictRight : ℝ)) :
    edgeIncidenceSetCount G (X : Set V)ᶜ =
      Nat.floor (α * ((Xᶜ).card : ℝ)) + 1 := by
  classical
  let D := G.deleteEdges {s(a,b)}
  have hdrop := Linkedness.edgeIncidenceSetCount_delete_edge_add_one
    G X a b hab hout
  have hsmaller : edgeIncidenceSetCount D (X : Set V)ᶜ <
      edgeIncidenceSetCount G (X : Set V)ᶜ := by
    dsimp [D]
    omega
  have hDG : D ≤ G := by
    intro x y hxy
    exact hxy.1
  have hnotD : ¬ UniversalAt D H X := by
    intro hD
    exact hbad (hD.mono_graph hDG)
  have hsub : Nat.card {w : V // w ∉ (X : Set V)} = (Xᶜ).card := by
    rw [Nat.card_eq_fintype_card]
    apply Fintype.card_of_finset' (p := {w : V | w ∉ (X : Set V)}) (Xᶜ)
    intro w
    simp
  have hfail : ¬ α * ((Xᶜ).card : ℝ) <
      (edgeIncidenceSetCount D (X : Set V)ᶜ : ℝ) := by
    intro hg
    have hmD : MassedPair D (X : Set V) α := {
      global := by simpa only [hsub] using hg
      shore := hshore
    }
    exact hnotD (hsame D hsmaller hmD)
  have hafter : (edgeIncidenceSetCount D (X : Set V)ᶜ : ℝ) ≤
      α * ((Xᶜ).card : ℝ) := le_of_not_gt hfail
  have hbefore : α * ((Xᶜ).card : ℝ) <
      (edgeIncidenceSetCount G (X : Set V)ᶜ : ℝ) := by
    simpa only [hsub] using hm.global
  have hznonneg : 0 ≤ α * ((Xᶜ).card : ℝ) :=
    mul_nonneg hα (Nat.cast_nonneg _)
  have hfloorLower : (Nat.floor (α * ((Xᶜ).card : ℝ)) : ℝ) ≤
      α * ((Xᶜ).card : ℝ) := Nat.floor_le hznonneg
  have hfloorUpper : α * ((Xᶜ).card : ℝ) <
      (Nat.floor (α * ((Xᶜ).card : ℝ)) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hbelow : Nat.floor (α * ((Xᶜ).card : ℝ)) <
      edgeIncidenceSetCount G (X : Set V)ᶜ := by
    exact_mod_cast lt_of_le_of_lt hfloorLower hbefore
  have habove : edgeIncidenceSetCount D (X : Set V)ᶜ <
      Nat.floor (α * ((Xᶜ).card : ℝ)) + 1 := by
    exact_mod_cast lt_of_le_of_lt hafter hfloorUpper
  dsimp [D] at hdrop habove
  omega

/-- The F.3 identity and massed shore condition give the outside vertex
used as the center of the dense closed neighborhood. -/
theorem exists_outside_degree_lt_twice_of_massed_floor_tight
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (α : ℝ) (hα : 0 ≤ α)
    (hX : 3 ≤ X.card)
    (hm : MassedPair G (X : Set V) α)
    (htight : edgeIncidenceSetCount G (X : Set V)ᶜ =
      Nat.floor (α * ((Xᶜ).card : ℝ)) + 1) :
    ∃ z ∈ Xᶜ, (G.degree z : ℝ) < 2 * α := by
  apply exists_outside_degree_lt_twice_of_floor_tight G X α hα hX htight
  intro x hx
  obtain ⟨w,hw,hxw⟩ := Linkedness.root_has_outside_neighbor G X α hm x hx
  exact ⟨w,hw,hxw⟩

end HadwigerLean.RootedDensity
