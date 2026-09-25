import HadwigerLean.Graph.DensityBasic
import HadwigerLean.Graph.VertexConnectivity
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic

/-!
# Density and vertex connectivity

This module proves the finite density-to-connectivity lemma used in the
small connected subgraph argument. The proof follows Appendix A.4 of
`docs/theorem4-corollary24-proof.md`.
-/

namespace HadwigerLean

universe u

variable {V : Type u} [Fintype V]

private theorem vertexConnected_one_of_connected (G : SimpleGraph V)
    (hG : G.Connected) (hcard : 1 < Fintype.card V) :
    VertexConnected G 1 := by
  classical
  refine ⟨hcard, ?_⟩
  intro U hU
  have hzero : U = ∅ := Finset.card_eq_zero.mp (by omega)
  subst U
  have hset : (((∅ : Finset V) : Set V)ᶜ) = Set.univ := by ext x; simp
  rw [hset]
  exact (SimpleGraph.induceUnivIso G).connected_iff.mpr hG

private theorem vertexConnected_top (k : ℕ) (hcard : k < Fintype.card V) :
    VertexConnected (⊤ : SimpleGraph V) k := by
  classical
  refine ⟨hcard, ?_⟩
  intro U hU
  have hnonempty : Nonempty ↥((U : Set V)ᶜ) := by
    have hsmall : U.card < Fintype.card V := lt_trans hU hcard
    have hcomp : 0 < Uᶜ.card := by
      have hsum := Finset.card_compl_add_card U
      omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hcomp
    exact ⟨⟨v, by simpa using hv⟩⟩
  simpa using (SimpleGraph.connected_top (V := ↥((U : Set V)ᶜ)))

private noncomputable def edgeCountOn (G : SimpleGraph V) (S : Finset V) : ℕ := by
  classical
  exact (G.edgeFinset ∩ S.sym2).card

private theorem edgeCount_induce_eq_edgeCountOn (G : SimpleGraph V) (S : Finset V) :
    edgeCount (G.induce (S : Set V)) = edgeCountOn G S := by
  classical
  letI : Fintype ↥(S : Set V) := Subtype.fintype _
  have h := congrArg Finset.card (G.map_edgeFinset_induce (s := (S : Set V)))
  simp only [Finset.card_map] at h
  rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at h
  simpa [edgeCountOn, edgeCount] using h


private theorem edgeCount_le_induce_add [DecidableEq V] (G : SimpleGraph V) (A B : Finset V)
    (hcover : A ∪ B = Finset.univ)
    (hnocross : ∀ ⦃x y : V⦄, x ∈ A → x ∉ B → y ∈ B → y ∉ A → ¬ G.Adj x y) :
    edgeCount G ≤ edgeCount (G.induce (A : Set V)) +
      edgeCount (G.induce (B : Set V)) := by
  classical
  have hedge : G.edgeFinset ⊆
      (G.edgeFinset ∩ A.sym2) ∪ (G.edgeFinset ∩ B.sym2) := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : G.Adj x y := by simpa [SimpleGraph.mem_edgeFinset] using he
      have hx : x ∈ A ∨ x ∈ B := by
        have hh : x ∈ A ∪ B := by rw [hcover]; simp
        simpa using hh
      have hy : y ∈ A ∨ y ∈ B := by
        have hh : y ∈ A ∪ B := by rw [hcover]; simp
        simpa using hh
      have hcross : x ∈ A → x ∉ B → y ∈ B → y ∉ A → False := by
        intro hxa hxb hyb hya
        exact hnocross hxa hxb hyb hya hxy
      have hcross' : x ∈ B → x ∉ A → y ∈ A → y ∉ B → False := by
        intro hxb hxa hya hyb
        exact hnocross hya hyb hxb hxa hxy.symm
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mk_mem_sym2_iff]
      tauto
  calc
    edgeCount G = G.edgeFinset.card := edgeCount_eq_card_edgeFinset G
    _ ≤ ((G.edgeFinset ∩ A.sym2) ∪ (G.edgeFinset ∩ B.sym2)).card :=
      Finset.card_le_card hedge
    _ ≤ (G.edgeFinset ∩ A.sym2).card + (G.edgeFinset ∩ B.sym2).card :=
      Finset.card_union_le _ _
    _ = edgeCount (G.induce (A : Set V)) + edgeCount (G.induce (B : Set V)) := by
      rw [edgeCount_induce_eq_edgeCountOn, edgeCount_induce_eq_edgeCountOn]
      unfold edgeCountOn
      congr 1 <;> congr 1 <;> ext e <;> simp

private def DensityCut [DecidableEq V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ A B : Finset V,
    A ∪ B = Finset.univ ∧
    (A ∩ B).card < k ∧
    (A \ B).Nonempty ∧
    (B \ A).Nonempty ∧
    (∀ ⦃x y : V⦄, x ∈ A → x ∉ B → y ∈ B → y ∉ A → ¬ G.Adj x y)
private theorem densityCut_of_not_vertexConnected [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) (horder : k < Fintype.card V)
    (hnot : ¬ VertexConnected G k) : DensityCut G k := by
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

private theorem degree_lt_card_part [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A B : Finset V) (hcover : A ∪ B = Finset.univ)
    (hnocross : ∀ ⦃x y : V⦄, x ∈ A → x ∉ B → y ∈ B → y ∉ A → ¬ G.Adj x y)
    {x : V} (hxA : x ∈ A) (hxB : x ∉ B) : G.degree x < A.card := by
  classical
  have hneighbors : G.neighborFinset x ⊆ A := by
    intro y hy
    by_contra hyA
    have hyB : y ∈ B := by
      have h : y ∈ A ∪ B := by rw [hcover]; simp
      rcases Finset.mem_union.mp h with hh | hh
      · exact False.elim (hyA hh)
      · exact hh
    exact hnocross hxA hxB hyB hyA ((G.mem_neighborFinset x y).mp hy)
  have hproper : G.neighborFinset x ⊂ A :=
    (Finset.ssubset_iff_of_subset hneighbors).mpr ⟨x, hxA, by simp⟩
  exact Finset.card_lt_card hproper

private theorem eq_top_of_max_edgeCount (G : SimpleGraph V)
    (hmax : (Fintype.card V).choose 2 ≤ edgeCount G) : G = ⊤ := by
  classical
  have hsub : G.edgeFinset ⊆ (⊤ : SimpleGraph V).edgeFinset :=
    SimpleGraph.edgeFinset_mono le_top
  have hcard : (⊤ : SimpleGraph V).edgeFinset.card ≤ G.edgeFinset.card := by
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    simpa only [edgeCount_eq_card_edgeFinset] using hmax
  have heq : G.edgeFinset = (⊤ : SimpleGraph V).edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub hcard
  exact SimpleGraph.edgeFinset_inj.mp heq

/-- An induced subgraph, represented with an injective vertex parametrization,
that meets the paper's strict `k`-vertex-connectivity convention. -/
def HasVertexConnectedInducedSubgraph (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (W : Type u) (_ : Fintype W) (f : W ↪ V), VertexConnected (G.comap f) k

private theorem hasVertexConnected_self (G : SimpleGraph V) (k : ℕ)
    (h : VertexConnected G k) : HasVertexConnectedInducedSubgraph G k := by
  refine ⟨V, inferInstance, Function.Embedding.refl V, ?_⟩
  change VertexConnected (G.comap id) k
  simpa using h

private theorem hasVertexConnected_induce [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (h : HasVertexConnectedInducedSubgraph
      (G.induce (S : Set V)) k) : HasVertexConnectedInducedSubgraph G k := by
  rcases h with ⟨W, instW, f, hf⟩
  letI : Fintype W := instW
  refine ⟨W, instW, f.trans (Function.Embedding.subtype (· ∈ (S : Set V))), ?_⟩
  exact hf

theorem edgeCount_induce_compl_singleton_add_degree [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    edgeCount (G.induce ({v} : Set V)ᶜ) + G.degree v = edgeCount G := by
  classical
  letI : Fintype ↥(({v} : Set V)ᶜ) := Subtype.fintype _
  have h1 := G.card_edgeFinset_induce_compl_singleton v
  have h2 := G.card_edgeFinset_deleteIncidenceSet v
  rw [h2] at h1
  have hdegree : G.degree v ≤ G.edgeFinset.card := G.degree_le_card_edgeFinset v
  calc
    edgeCount (G.induce ({v} : Set V)ᶜ) + G.degree v =
        G.edgeFinset.card - G.degree v + G.degree v := by
      rw [edgeCount_eq_card_edgeFinset, h1]
    _ = G.edgeFinset.card := Nat.sub_add_cancel hdegree
    _ = edgeCount G := (edgeCount_eq_card_edgeFinset G).symm

private theorem mader_threshold_base (k n : ℕ) (hk : 2 ≤ k)
    (hn : n = 2 * k - 1) :
    n.choose 2 = (2 * k - 3) * (n - k + 1) + 1 := by
  have hnk : n - k + 1 = k := by omega
  have hq : (2 * k - 3) + 3 = 2 * k := by omega
  have hn1 : n + 1 = 2 * k := by omega
  have hn2 : (n - 1) + 2 = 2 * k := by omega
  have hmul : n * (n - 1) = 2 * ((2 * k - 3) * k + 1) := by
    nlinarith
  rw [Nat.choose_two_right, hnk, hmul]
  omega

private theorem mader_threshold_delete (k n d e e' : ℕ)
    (hk : 2 ≤ k) (hn : 2 * k ≤ n) (hd : d ≤ 2 * k - 3)
    (hbalance : e' + d = e)
    (hedges : (2 * k - 3) * (n - k + 1) + 1 ≤ e) :
    (2 * k - 3) * ((n - 1) - k + 1) + 1 ≤ e' := by
  have hstep : ((n - 1) - k + 1) + 1 = n - k + 1 := by omega
  have hfactor : (2 * k - 3) * (n - k + 1) =
      (2 * k - 3) * ((n - 1) - k + 1) + (2 * k - 3) := by
    rw [← hstep]
    ring
  omega

private theorem mader_threshold_split (k n a b u : ℕ)
    (ha : 2 * k - 1 ≤ a) (hb : 2 * k - 1 ≤ b)
    (hu : u < k) (hsum : a + b = n + u) :
    (a - k + 1) + (b - k + 1) ≤ n - k + 1 := by
  omega

private theorem mader_density_meets_threshold (k n e : ℕ)
    (hk : 1 ≤ k) (hn : 2 * k - 1 ≤ n)
    (hdense : 2 * k * n ≤ e) :
    (2 * k - 3) * (n - k + 1) + 1 ≤ e := by
  have hq : (2 * k - 3) ≤ 2 * k := Nat.sub_le _ _
  have hnk : n - k + 1 ≤ n := by omega
  have h1 : (2 * k - 3) * (n - k + 1) ≤ (2 * k - 3) * n :=
    Nat.mul_le_mul_left _ hnk
  have h2 : (2 * k - 3) * n + 1 ≤ 2 * k * n := by
    have hnpos : 0 < n := by omega
    have hqplus : (2 * k - 3) + 1 ≤ 2 * k := by omega
    have hfirst : (2 * k - 3) * n + 1 ≤ ((2 * k - 3) + 1) * n := by nlinarith
    exact hfirst.trans (Nat.mul_le_mul_right n hqplus)
  omega

private theorem mader_density_large_order (G : SimpleGraph V) (k : ℕ)
    (hk : 1 ≤ k) (hn : 0 < Fintype.card V)
    (hdense : 2 * k * Fintype.card V ≤ edgeCount G) :
    4 * k + 1 ≤ Fintype.card V := by
  classical
  by_contra hsmall
  have hbound : edgeCount G ≤ (Fintype.card V).choose 2 := by
    rw [edgeCount_eq_card_edgeFinset]
    exact G.card_edgeFinset_le_card_choose_two
  rw [Nat.choose_two_right] at hbound
  have htwo : 2 * edgeCount G ≤ Fintype.card V * (Fintype.card V - 1) := by
    omega
  have hfactor : Fintype.card V - 1 ≤ 4 * k - 1 := by omega
  have hmul : Fintype.card V * (Fintype.card V - 1) ≤
      Fintype.card V * (4 * k - 1) := Nat.mul_le_mul_left _ hfactor
  have hfactor2 : 4 * k - 1 + 1 = 4 * k := by omega
  have hpos : 0 < k * Fintype.card V := Nat.mul_pos (by omega) hn
  nlinarith

theorem card_compl_singleton_eq_sub_one [DecidableEq V] (v : V) :
    Fintype.card ↥(({v} : Set V)ᶜ) = Fintype.card V - 1 := by
  classical
  have hcard : Fintype.card ↥(({v} : Set V)ᶜ) = ({v}ᶜ : Finset V).card := by
    apply Fintype.card_of_subtype
    intro z
    simp
  rw [hcard, Finset.card_compl]
  simp

private theorem mader_extremal (k : ℕ) (hk : 2 ≤ k) :
    ∀ n : ℕ, ∀ {W : Type u} [Fintype W] (G : SimpleGraph W),
      Fintype.card W = n → 2 * k - 1 ≤ n →
      (2 * k - 3) * (n - k + 1) + 1 ≤ edgeCount G →
      HasVertexConnectedInducedSubgraph G k := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W instW G hcard hmin hedges
    classical
    let q : ℕ := 2 * k - 3
    by_cases hbase : n = 2 * k - 1
    · have hmaxN : n.choose 2 ≤ edgeCount G := by
        rw [mader_threshold_base k n hk hbase]
        exact hedges
      have hmax : (Fintype.card W).choose 2 ≤ edgeCount G := by
        simpa [hcard] using hmaxN
      have htop : G = ⊤ := eq_top_of_max_edgeCount G hmax
      rw [htop]
      exact hasVertexConnected_self _ k (vertexConnected_top k (by omega))
    have hnlarge : 2 * k ≤ n := by omega
    by_cases hlow : ∃ v : W, G.degree v ≤ q
    · obtain ⟨v, hdeg⟩ := hlow
      let H := G.induce (({v} : Set W)ᶜ)
      have hcardH : Fintype.card ↥(({v} : Set W)ᶜ) = n - 1 := by
        rw [card_compl_singleton_eq_sub_one, hcard]
      have hbalance : edgeCount H + G.degree v = edgeCount G :=
        edgeCount_induce_compl_singleton_add_degree G v
      have hdelete : q * ((n - 1) - k + 1) + 1 ≤ edgeCount H :=
        mader_threshold_delete k n (G.degree v) (edgeCount G) (edgeCount H)
          hk hnlarge hdeg hbalance hedges
      have hrec : HasVertexConnectedInducedSubgraph H k :=
        ih (n - 1) (by omega) H hcardH (by omega) hdelete
      have hco : (({v}ᶜ : Finset W) : Set W) = ({v} : Set W)ᶜ := by
        ext x; simp
      exact hasVertexConnected_induce G ({v}ᶜ : Finset W) (by
        rw [hco]
        exact hrec)
    have hdegree : ∀ v : W, 2 * k - 2 ≤ G.degree v := by
      intro v
      have hq : q + 1 = 2 * k - 2 := by dsimp [q]; omega
      have hv : q < G.degree v := by
        by_contra hc
        exact hlow ⟨v, Nat.le_of_not_gt hc⟩
      omega
    by_cases hvc : VertexConnected G k
    · exact hasVertexConnected_self G k hvc
    have horder : k < Fintype.card W := by omega
    obtain ⟨A, B, hcover, hoverlap, hleft, hright, hnocross⟩ :=
      densityCut_of_not_vertexConnected G k horder hvc
    have hAcard : Fintype.card ↥(A : Set W) = A.card := by
      simpa using Fintype.card_coe A
    have hBcard : Fintype.card ↥(B : Set W) = B.card := by
      simpa using Fintype.card_coe B
    have hAproper : A.card < n := by
      obtain ⟨v, hv⟩ := hright
      have hvnotA : v ∉ A := (Finset.mem_sdiff.mp hv).2
      have hs : A ⊂ Finset.univ :=
        (Finset.ssubset_iff_of_subset (Finset.subset_univ A)).mpr
          ⟨v, Finset.mem_univ v, hvnotA⟩
      simpa [hcard] using Finset.card_lt_card hs
    have hBproper : B.card < n := by
      obtain ⟨v, hv⟩ := hleft
      have hvnotB : v ∉ B := (Finset.mem_sdiff.mp hv).2
      have hs : B ⊂ Finset.univ :=
        (Finset.ssubset_iff_of_subset (Finset.subset_univ B)).mpr
          ⟨v, Finset.mem_univ v, hvnotB⟩
      simpa [hcard] using Finset.card_lt_card hs
    have hAmin : 2 * k - 1 ≤ A.card := by
      obtain ⟨v, hv⟩ := hleft
      have hv' := Finset.mem_sdiff.mp hv
      have hside := degree_lt_card_part G A B hcover hnocross hv'.1 hv'.2
      have hlowdeg := hdegree v
      omega
    have hBmin : 2 * k - 1 ≤ B.card := by
      obtain ⟨v, hv⟩ := hright
      have hv' := Finset.mem_sdiff.mp hv
      have hcover' : B ∪ A = Finset.univ := by simpa [Finset.union_comm] using hcover
      have hnocross' : ∀ ⦃x y : W⦄, x ∈ B → x ∉ A → y ∈ A → y ∉ B →
          ¬ G.Adj x y := by
        intro x y hxB hxA hyA hyB hxy
        exact hnocross hyA hyB hxB hxA hxy.symm
      have hside := degree_lt_card_part G B A hcover' hnocross' hv'.1 hv'.2
      have hlowdeg := hdegree v
      omega
    by_cases hA : q * (A.card - k + 1) + 1 ≤ edgeCount (G.induce (A : Set W))
    · have hrec : HasVertexConnectedInducedSubgraph (G.induce (A : Set W)) k :=
        ih A.card hAproper (G.induce (A : Set W)) hAcard hAmin hA
      exact hasVertexConnected_induce G A hrec
    by_cases hB : q * (B.card - k + 1) + 1 ≤ edgeCount (G.induce (B : Set W))
    · have hrec : HasVertexConnectedInducedSubgraph (G.induce (B : Set W)) k :=
        ih B.card hBproper (G.induce (B : Set W)) hBcard hBmin hB
      exact hasVertexConnected_induce G B hrec
    have hAupper : edgeCount (G.induce (A : Set W)) ≤ q * (A.card - k + 1) := by
      omega
    have hBupper : edgeCount (G.induce (B : Set W)) ≤ q * (B.card - k + 1) := by
      omega
    have hsum : A.card + B.card = n + (A ∩ B).card := by
      have h := Finset.card_union_add_card_inter A B
      rw [hcover] at h
      simpa [hcard] using h.symm
    have hnum := mader_threshold_split k n A.card B.card (A ∩ B).card
      hAmin hBmin hoverlap hsum
    have hcount : edgeCount G ≤ edgeCount (G.induce (A : Set W)) +
        edgeCount (G.induce (B : Set W)) :=
      edgeCount_le_induce_add G A B hcover hnocross
    have hbound : edgeCount G ≤ q * (n - k + 1) := by
      calc
        edgeCount G ≤ edgeCount (G.induce (A : Set W)) +
            edgeCount (G.induce (B : Set W)) := hcount
        _ ≤ q * (A.card - k + 1) + q * (B.card - k + 1) :=
          Nat.add_le_add hAupper hBupper
        _ = q * ((A.card - k + 1) + (B.card - k + 1)) := by ring
        _ ≤ q * (n - k + 1) := Nat.mul_le_mul_left q hnum
    have hcontra : q * (n - k + 1) + 1 ≤ q * (n - k + 1) :=
      hedges.trans hbound
    exact False.elim (Nat.not_succ_le_self _ hcontra)

/-- Lowering the requested vertex connectivity of an induced witness. -/
theorem HasVertexConnectedInducedSubgraph.of_le {G : SimpleGraph V} {k m : ℕ}
    (h : HasVertexConnectedInducedSubgraph G k) (hm : m ≤ k) :
    HasVertexConnectedInducedSubgraph G m := by
  rcases h with ⟨W, instW, f, hf⟩
  exact ⟨W, instW, f, hf.of_le hm⟩

/-- The needed Mader form in the edge-per-vertex convention: a nonempty
finite graph with at least `2k` edges per vertex has a `k`-connected induced
subgraph. The witness is carried by an injective parametrization. -/
theorem hasVertexConnectedInducedSubgraph_of_edges_ge
    (G : SimpleGraph V) (k : ℕ) (hk : 1 ≤ k)
    (hn : 0 < Fintype.card V)
    (hdense : 2 * k * Fintype.card V ≤ edgeCount G) :
    HasVertexConnectedInducedSubgraph G k := by
  classical
  have hlarge : 4 * k + 1 ≤ Fintype.card V :=
    mader_density_large_order G k hk hn hdense
  by_cases hk2 : 2 ≤ k
  · have hthreshold : (2 * k - 3) * (Fintype.card V - k + 1) + 1 ≤
        edgeCount G :=
      mader_density_meets_threshold k (Fintype.card V) (edgeCount G)
        hk (by omega) hdense
    exact mader_extremal k hk2 (Fintype.card V) G rfl (by omega) hthreshold
  · have hk1 : k = 1 := by omega
    subst k
    have hthreshold : (2 * 2 - 3) * (Fintype.card V - 2 + 1) + 1 ≤
        edgeCount G := by
      norm_num at hdense ⊢
      omega
    have htwo : HasVertexConnectedInducedSubgraph G 2 :=
      mader_extremal 2 (by omega) (Fintype.card V) G rfl (by omega) hthreshold
    exact htwo.of_le (by omega)

/-- The edge-density formulation of the Mader lemma used in Section 8. -/
theorem hasVertexConnectedInducedSubgraph_of_edgeDensity_ge
    (G : SimpleGraph V) (k : ℕ) (hk : 1 ≤ k)
    (hdense : (2 * k : ℝ) ≤ edgeDensity G) :
    HasVertexConnectedInducedSubgraph G k := by
  classical
  have hn : 0 < Fintype.card V := by
    by_contra hzero
    have hnzero : Fintype.card V = 0 := by omega
    have hdenzero : edgeDensity G = 0 := by simp [edgeDensity, hnzero]
    have hkpos : (0 : ℝ) < 2 * (k : ℝ) := by positivity
    rw [hdenzero] at hdense
    exact (not_le_of_gt hkpos) hdense
  have hdenpos : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr hn
  have hreal : (2 * (k : ℝ)) * (Fintype.card V : ℝ) ≤ (edgeCount G : ℝ) := by
    apply (le_div_iff₀ hdenpos).mp
    simpa [edgeDensity] using hdense
  have hnat : 2 * k * Fintype.card V ≤ edgeCount G := by exact_mod_cast hreal
  exact hasVertexConnectedInducedSubgraph_of_edges_ge G k hk hn hnat
end HadwigerLean
