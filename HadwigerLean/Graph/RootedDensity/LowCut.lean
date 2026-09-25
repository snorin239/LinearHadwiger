import HadwigerLean.Graph.VertexConnectivity
import Mathlib.Tactic

/-! A low-order cut witnessing failure of vertex connectivity. -/

namespace HadwigerLean.RootedDensity

universe u
variable {V : Type u} [Fintype V]

def LowCut [DecidableEq V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ A B : Finset V,
    A ∪ B = Finset.univ ∧
    (A ∩ B).card < k ∧
    (A \ B).Nonempty ∧
    (B \ A).Nonempty ∧
    (∀ ⦃x y : V⦄, x ∈ A → x ∉ B → y ∈ B → y ∉ A → ¬ G.Adj x y)
theorem lowCut_of_not_vertexConnected [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) (horder : k < Fintype.card V)
    (hnot : ¬ VertexConnected G k) : LowCut G k := by
  classical
  have hfail : ∃ U : Finset V, U.card < k ∧
      ¬ (G.induce (U : Set V)ᶜ).Connected := by
    by_contra hc
    apply hnot
    refine ⟨horder, ?_⟩
    intro U hU
    by_contra hn
    exact hc ⟨U, hU, hn⟩
  obtain ⟨U, hU, hconn⟩ := hfail
  let H := G.induce (U : Set V)ᶜ
  have hcomp : 0 < Uᶜ.card := by
    have hsum := Finset.card_compl_add_card U
    omega
  haveI : Nonempty ↥((U : Set V)ᶜ) := by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hcomp
    exact ⟨⟨v, by simpa using hv⟩⟩
  have hpre : ¬ H.Preconnected := by
    intro hp
    exact hconn ⟨hp⟩
  obtain ⟨x, y, hxy⟩ : ∃ x y : ↥((U : Set V)ᶜ), ¬ H.Reachable x y := by
    simpa [SimpleGraph.Preconnected] using hpre
  let R : Finset V := Finset.univ.filter fun z =>
    ∃ hz : z ∉ U, H.Reachable x ⟨z, hz⟩
  have hR (z : V) : z ∈ R ↔ ∃ hz : z ∉ U, H.Reachable x ⟨z, hz⟩ := by
    simp [R]
  let A : Finset V := U ∪ R
  let B : Finset V := Rᶜ
  have hdisj : Disjoint U R := by
    apply Finset.disjoint_left.mpr
    intro z hzU hzR
    obtain ⟨hz, _⟩ := (hR z).mp hzR
    exact hz hzU
  have hoverlap : A ∩ B = U := by
    ext z
    simp only [A, B, Finset.mem_inter, Finset.mem_union, Finset.mem_compl]
    constructor
    · rintro ⟨hzU | hzR, hznotR⟩
      · exact hzU
      · exact (hznotR hzR).elim
    · intro hzU
      exact ⟨Or.inl hzU, Finset.disjoint_left.mp hdisj hzU⟩
  have hcover : A ∪ B = Finset.univ := by
    ext z
    simp only [A, B, Finset.mem_union, Finset.mem_compl, Finset.mem_univ, iff_true]
    by_cases hz : z ∈ R
    · exact Or.inl (Or.inr hz)
    · exact Or.inr hz
  have hxR : (x : V) ∈ R := (hR x).mpr ⟨x.property, SimpleGraph.Reachable.refl x⟩
  have hyR : (y : V) ∉ R := by
    intro hy
    obtain ⟨hyU, hyReach⟩ := (hR y).mp hy
    exact hxy (by simpa using hyReach)
  have hxleft : (A \ B).Nonempty := by
    refine ⟨x, ?_⟩
    simp [A, B, hxR]
  have hyright : (B \ A).Nonempty := by
    refine ⟨y, ?_⟩
    have hyU : (y : V) ∉ U := y.property
    simp [A, B, hyR, hyU]
  refine ⟨A, B, hcover, ?_, hxleft, hyright, ?_⟩
  · rw [hoverlap]
    exact hU
  intro a b haA haB hbB hbA hab
  have haR : a ∈ R := by
    rcases Finset.mem_union.mp haA with haU | haR
    · exact False.elim (haB (Finset.mem_compl.mpr (fun haR =>
        Finset.disjoint_left.mp hdisj haU haR)))
    · exact haR
  have hbnotR : b ∉ R := by
    intro hbR
    exact hbA (Finset.mem_union.mpr (Or.inr hbR))
  have hbU : b ∉ U := by
    intro hbU
    exact hbA (Finset.mem_union.mpr (Or.inl hbU))
  obtain ⟨haU, haReach⟩ := (hR a).mp haR
  have habH : H.Adj (⟨a, haU⟩ : ↥((U : Set V)ᶜ)) ⟨b, hbU⟩ := hab
  exact hbnotR ((hR b).mpr ⟨hbU, haReach.trans habH.reachable⟩)


end HadwigerLean.RootedDensity

