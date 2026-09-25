import HadwigerLean.Woven.DoubleFanCost
import HadwigerLean.Graph.ChromaticSlice
import Mathlib.Tactic

/-!
# Pack small connected pieces from a chromatic reserve

This is the combinatorial core of Section 7.2. It is phrased against an
explicit finder for a small `k`-connected piece in every sufficiently
chromatic residual graph. The small-connected theorem and sparse coloring
will supply that finder separately.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

private theorem card_piece_union_le
    (P : Finset (Finset V)) (N : ℕ)
    (hsize : ∀ J ∈ P, J.card ≤ N) :
    (P.biUnion id).card ≤ P.card * N := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert J P hJP ih =>
    have hJ : J.card ≤ N := hsize J (Finset.mem_insert_self J P)
    have hP : ∀ K ∈ P, K.card ≤ N := by
      intro K hK
      exact hsize K (Finset.mem_insert_of_mem hK)
    have hbound := ih hP
    have hunion := Finset.card_union_le J (P.biUnion id)
    have hres : (J ∪ P.biUnion id).card ≤ (P.card + 1) * N := by
      calc
        _ ≤ J.card + (P.biUnion id).card := hunion
        _ ≤ N + P.card * N := Nat.add_le_add hJ hbound
        _ = (P.card + 1) * N := by ring
    simpa [hJP, Finset.biUnion_insert] using hres

theorem chromatic_le_piece_and_complement
    (G : SimpleGraph V) (U : Finset V) :
    chromatic G ≤ chromatic (G.induce (U : Set V)) +
      chromatic (G.induce (Uᶜ : Finset V)) := by
  classical
  have h := Woven.chromatic_induce_le_add_remainder G Set.univ (U : Set V)
  have huniv : chromatic (G.induce Set.univ) = chromatic G := by
    have hs : ((Finset.univ : Finset V) : Set V) = Set.univ := by
      ext v
      simp
    rw [← hs]
    exact chromatic_induce_univ_finset G
  have hcompl : Set.univ \ (U : Set V) = (Uᶜ : Finset V) := by
    ext v
    simp
  rw [huniv,hcompl] at h
  exact h

/-- Repeatedly select disjoint small `k`-connected pieces. A local chromatic
bound on any possible occupied union guarantees that the residual remains
colorful enough for another selection. -/
theorem exists_disjoint_small_connected_pieces
    (G : SimpleGraph V) (r k N q d : ℕ)
    (hfind : ∀ R : Finset V,
      d < chromatic (G.induce (R : Set V)) →
      ∃ J : Finset V, J ⊆ R ∧ J.card ≤ N ∧
        VertexConnected (G.induce (J : Set V)) k)
    (hlocal : ∀ U : Finset V, U.card ≤ r * N →
      chromatic (G.induce (U : Set V)) ≤ q)
    (hχ : q + d < chromatic G) :
    ∃ J : Fin r → Finset V,
      (∀ i, (J i).card ≤ N ∧
        VertexConnected (G.induce (J i : Set V)) k) ∧
      (Pairwise fun i j => Disjoint (J i) (J j)) := by
  classical
  let Good (P : Finset (Finset V)) : Prop :=
    (∀ J ∈ P, J.card ≤ N ∧
      VertexConnected (G.induce (J : Set V)) k) ∧
    (∀ J ∈ P, ∀ K ∈ P, J ≠ K → Disjoint J K)
  let all : Finset (Finset (Finset V)) :=
    Finset.univ.filter Good
  have hnonempty : all.Nonempty := by
    refine ⟨∅,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    constructor <;> simp
  obtain ⟨P,hPall,hmax⟩ := all.exists_max_image Finset.card hnonempty
  have hP : Good P := (Finset.mem_filter.mp hPall).2
  have hPcard : r ≤ P.card := by
    by_contra hsmall
    have hPr : P.card < r := by omega
    let U : Finset V := P.biUnion id
    have hUcard : U.card ≤ r * N := by
      have hbound := card_piece_union_le P N (fun J hJ => (hP.1 J hJ).1)
      dsimp [U]
      nlinarith
    have hUχ := hlocal U hUcard
    let R : Finset V := Uᶜ
    have hχR : d < chromatic (G.induce (R : Set V)) := by
      have hsplit := chromatic_le_piece_and_complement G U
      dsimp [R]
      omega
    obtain ⟨J,hJR,hJsize,hJconn⟩ := hfind R hχR
    have hJne : J.Nonempty := by
      have hord := hJconn.order_gt
      have hcard : Fintype.card (↥(J : Set V)) = J.card := by
        apply Fintype.card_of_finset' J
        intro z
        rfl
      rw [hcard] at hord
      exact Finset.card_pos.mp (by omega)
    have hJP : J ∉ P := by
      intro hmem
      have hJsubU : J ⊆ U := by
        intro z hz
        exact Finset.mem_biUnion.mpr ⟨J,hmem,hz⟩
      obtain ⟨z,hz⟩ := hJne
      exact (Finset.mem_compl.mp (hJR hz)) (hJsubU hz)
    have hPnew : Good (insert J P) := by
      constructor
      · intro K hK
        rcases Finset.mem_insert.mp hK with hK | hK
        · subst K
          exact ⟨hJsize,hJconn⟩
        · exact hP.1 K hK
      · intro K hK L hL hKL
        rcases Finset.mem_insert.mp hK with hK | hK <;>
          rcases Finset.mem_insert.mp hL with hL | hL
        · exact False.elim (hKL (hK.trans hL.symm))
        · subst K
          apply Finset.disjoint_left.mpr
          intro z hzJ hzL
          have hzU : z ∈ U := Finset.mem_biUnion.mpr ⟨L,hL,hzL⟩
          exact (Finset.mem_compl.mp (hJR hzJ)) hzU
        · subst L
          apply Finset.disjoint_left.mpr
          intro z hzK hzJ
          have hzU : z ∈ U := Finset.mem_biUnion.mpr ⟨K,hK,hzK⟩
          exact (Finset.mem_compl.mp (hJR hzJ)) hzU
        · exact hP.2 K hK L hL hKL
    have hPnewall : insert J P ∈ all :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hPnew⟩
    have hmax' := hmax (insert J P) hPnewall
    have hstep : (insert J P).card = P.card + 1 :=
      by simp [hJP]
    omega
  obtain ⟨e,he⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin r) (s := P) (by simpa using hPcard)
  refine ⟨fun i => e i, ?_, ?_⟩
  · intro i
    exact hP.1 (e i) (he ⟨i,rfl⟩)
  · intro i j hij
    apply hP.2 (e i) (he ⟨i,rfl⟩)
      (e j) (he ⟨j,rfl⟩)
    exact e.injective.ne hij

end Inseparability
end HadwigerLean




