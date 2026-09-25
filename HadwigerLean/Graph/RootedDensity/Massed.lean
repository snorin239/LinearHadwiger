import HadwigerLean.Graph.RootedDensity.Definitions
import HadwigerLean.Graph.Linkedness.Massed
import Mathlib.Tactic

/-! The density and connectivity entry point to Appendix F's massed-pair invariant. -/

namespace HadwigerLean.RootedDensity

universe u
variable {V : Type u} [Fintype V]

/-- If the global edge budget pays for the internal root edges with strict
slack, connectivity supplies the shore condition automatically. -/
theorem massed_of_connected_edge_budget
    (G : SimpleGraph V) (X : Finset V) (k : ℕ) (α : ℝ)
    (hconn : VertexConnected G k) (hX : X.card ≤ k)
    (hroot : ((X.card + 1).choose 2 : ℝ) < α * (X.card : ℝ))
    (hedge : α * (Fintype.card V : ℝ) ≤ (edgeCount G : ℝ)) :
    MassedPair G (X : Set V) α := by
  classical
  have hupper := Linkedness.edgeCount_le_incidence_add_internal G X
  have hupperR : (edgeCount G : ℝ) ≤
      (edgeIncidenceCount G Xᶜ : ℝ) + ((X.card + 1).choose 2 : ℝ) := by
    exact_mod_cast hupper
  have hsize : (Xᶜ).card + X.card = Fintype.card V :=
    Finset.card_compl_add_card X
  have hsizeR : ((Xᶜ).card : ℝ) + (X.card : ℝ) =
      (Fintype.card V : ℝ) := by exact_mod_cast hsize
  have hedgeSplit : α * ((Xᶜ).card : ℝ) + α * (X.card : ℝ) ≤
      (edgeCount G : ℝ) := by
    calc
      _ = α * (Fintype.card V : ℝ) := by rw [← hsizeR, mul_add]
      _ ≤ (edgeCount G : ℝ) := hedge
  have hglobalFin : α * ((Xᶜ).card : ℝ) <
      (edgeIncidenceCount G Xᶜ : ℝ) := by
    have hsizeR : ((Xᶜ).card : ℝ) + (X.card : ℝ) =
        (Fintype.card V : ℝ) := by exact_mod_cast hsize
    nlinarith
  have hsub : Nat.card {v : V // v ∉ (X : Set V)} = (Xᶜ).card := by
    rw [Nat.card_eq_fintype_card]
    apply Fintype.card_of_finset' (p := {v : V | v ∉ (X : Set V)}) (Xᶜ)
    intro v
    simp
  have hinc : edgeIncidenceSetCount G (X : Set V)ᶜ =
      edgeIncidenceCount G Xᶜ := by
    simpa using Linkedness.incidenceSetCount_eq_finsetCount G Xᶜ
  apply Linkedness.massed_of_vertexConnected_and_global X k α hconn hX
  rw [hsub, hinc]
  exact hglobalFin

/-- The real root-edge reserve follows from a linear density coefficient
once there are at least two roots. -/
theorem root_edge_reserve
    (h : ℕ) (hh : 2 ≤ h) (α : ℝ) (hα : (h : ℝ) ≤ α) :
    ((h + 1).choose 2 : ℝ) < α * (h : ℝ) := by
  have hchoose : (h + 1).choose 2 < h * h := by
    rw [Nat.choose_two_right]
    have hsub : h + 1 - 1 = h := by omega
    rw [hsub]
    have hdiv : 2 * (((h + 1) * h) / 2) ≤ (h + 1) * h := by omega
    have hmul : (h + 1) * h < 2 * (h * h) := by nlinarith
    omega
  have hchooseR : ((h + 1).choose 2 : ℝ) < (h : ℝ) * (h : ℝ) := by
    exact_mod_cast hchoose
  have hnonneg : (0 : ℝ) ≤ h := by positivity
  nlinarith

/-- The paper's density and connectivity hypotheses make every full-size
root set massed at `α=12c+5000h`. -/
theorem massed_of_rooted_density
    (G : SimpleGraph V) (X : Finset V) (h : ℕ) (c : ℝ)
    (hh : 3 ≤ h) (hc : 0 ≤ c)
    (hX : X.card = h)
    (hconn : VertexConnected G h)
    (hedge : (12 * c + 5000 * (h : ℝ)) * (Fintype.card V : ℝ) ≤
      (edgeCount G : ℝ)) :
    MassedPair G (X : Set V) (12 * c + 5000 * (h : ℝ)) := by
  apply massed_of_connected_edge_budget G X h _ hconn (by omega)
  · rw [hX]
    apply root_edge_reserve h (by omega)
    nlinarith
  · exact hedge

end HadwigerLean.RootedDensity


