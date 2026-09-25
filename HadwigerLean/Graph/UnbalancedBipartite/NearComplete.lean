import HadwigerLean.Graph.CliqueDensity.FinsetBranchMinor
import HadwigerLean.Graph.DensityBasic
import Mathlib.Tactic
import Mathlib.Combinatorics.Hall.Basic

/-!
# Near-complete graphs and connected short branches

The near-complete auxiliary lemma in Appendix C is assembled from finite
sampling and two-edge connector paths. This file begins with the deterministic
branch connectivity and connector-selection interfaces.
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A set is connected when every vertex can be joined to a center by a path
of length at most two staying inside the set. -/
theorem connected_induce_of_center_two_hop
    (G : SimpleGraph V) (B : Finset V) (a : V) (ha : a ∈ B)
    (hreach : ∀ v ∈ B, v = a ∨ G.Adj a v ∨
      ∃ w ∈ B, G.Adj a w ∧ G.Adj w v) :
    (G.induce (B : Set V)).Connected := by
  classical
  let K := G.induce (B : Set V)
  have hcenter : ∀ x : (B : Set V), K.Reachable ⟨a, ha⟩ x := by
    intro x
    rcases hreach x.1 x.2 with h | h | ⟨w, hw, haw, hwx⟩
    · have hx : x = ⟨a, ha⟩ := Subtype.ext h
      rw [hx]
    · exact (show K.Adj ⟨a, ha⟩ x from h).reachable
    · exact (show K.Adj ⟨a, ha⟩ ⟨w, hw⟩ from haw).reachable.trans
        (show K.Adj ⟨w, hw⟩ x from hwx).reachable
  haveI : Nonempty (B : Set V) := ⟨⟨a, ha⟩⟩
  refine (SimpleGraph.connected_iff K).mpr ⟨?_, inferInstance⟩
  intro x y
  exact (hcenter x).symm.trans (hcenter y)


/-- Uniformly large candidate sets admit globally distinct representatives.
This is the connector-choice step in the near-complete minor construction. -/
theorem exists_injective_choice_of_large_candidates
    {D : Type*} [Fintype D] [DecidableEq D]
    (T : D → Finset V)
    (hlarge : ∀ d, Fintype.card D ≤ (T d).card) :
    ∃ f : D → V, Function.Injective f ∧ ∀ d, f d ∈ T d := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective T).mp
  intro S
  by_cases hS : S.Nonempty
  · obtain ⟨d, hd⟩ := hS
    have hsub : T d ⊆ S.biUnion T := Finset.subset_biUnion_of_mem T hd
    calc
      S.card ≤ Fintype.card D := Finset.card_le_univ _
      _ ≤ (T d).card := hlarge d
      _ ≤ (S.biUnion T).card := Finset.card_le_card hsub
  · simp at hS
    simp [hS]

/-- The vertices that need a two-edge attachment to their block's anchor. -/
def nearCompleteDemands (r : ℕ) (X Y : Fin r → Finset V)
    (a : Fin r → V) : Type u :=
  Σ i : Fin r, ↥((X i ∪ Y i).erase (a i))

instance nearCompleteDemandsFintype (r : ℕ) (X Y : Fin r → Finset V)
    (a : Fin r → V) : Fintype (nearCompleteDemands r X Y a) := by
  unfold nearCompleteDemands
  infer_instance
/-- A branch consists of its two core blocks and the assigned connectors. -/
def nearCompleteBranch (r : ℕ) (X Y : Fin r → Finset V)
    (a : Fin r → V) (f : nearCompleteDemands r X Y a → V)
    (i : Fin r) : Finset V :=
  X i ∪ Y i ∪
    (Finset.univ : Finset ↥((X i ∪ Y i).erase (a i))).image
      (fun d => f ⟨i, d⟩)

/-- Disjoint core blocks and distinct outside connectors make clique-minor
branches whenever each first block meets every other second block. -/
theorem hasCliqueMinor_of_blocks_and_connectors
    (G : SimpleGraph V) (r : ℕ) (Z : Finset V)
    (X Y : Fin r → Finset V) (a : Fin r → V)
    (f : nearCompleteDemands r X Y a → V)
    (ha : ∀ i, a i ∈ X i)
    (hsub : ∀ i, X i ∪ Y i ⊆ Z)
    (hdis : Pairwise (fun i j => Disjoint (X i ∪ Y i) (X j ∪ Y j)))
    (hf : Function.Injective f)
    (hfout : ∀ d, f d ∉ Z)
    (hfadj : ∀ d, G.Adj (a d.1) (f d) ∧ G.Adj (f d) d.2.1)
    (hcross : ∀ i j, i ≠ j →
      ∃ x ∈ X i, ∃ y ∈ Y j, G.Adj x y) :
    HasCliqueMinor G r := by
  classical
  let B := nearCompleteBranch r X Y a f
  have hbase (i : Fin r) : X i ∪ Y i ⊆ B i := by
    intro v hv
    exact Finset.mem_union_left _ hv
  have hanchor (i : Fin r) : a i ∈ B i :=
    hbase i (Finset.mem_union_left _ (ha i))
  have hconn (i : Fin r) : (G.induce (B i : Set V)).Connected := by
    apply connected_induce_of_center_two_hop G (B i) (a i) (hanchor i)
    intro v hv
    change v ∈ X i ∪ Y i ∪
      (Finset.univ : Finset ↥((X i ∪ Y i).erase (a i))).image
        (fun d => f ⟨i, d⟩) at hv
    rcases Finset.mem_union.mp hv with hcore | hconnector
    · by_cases h : v = a i
      · exact Or.inl h
      · have hd : v ∈ (X i ∪ Y i).erase (a i) :=
          Finset.mem_erase.mpr ⟨h, hcore⟩
        let d : nearCompleteDemands r X Y a := ⟨i, ⟨v, hd⟩⟩
        refine Or.inr (Or.inr ⟨f d, ?_, ?_, ?_⟩)
        · exact Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨⟨v, hd⟩, Finset.mem_univ _, rfl⟩)
        · exact (hfadj d).1
        · exact (hfadj d).2
    · obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hconnector
      exact Or.inr (Or.inl (hfadj ⟨i, d⟩).1)
  have hdisB : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    have split (k : Fin r) (hv : v ∈ B k) :
        v ∈ X k ∪ Y k ∨
          ∃ d : ↥((X k ∪ Y k).erase (a k)), f ⟨k, d⟩ = v := by
      change v ∈ X k ∪ Y k ∪
        (Finset.univ : Finset ↥((X k ∪ Y k).erase (a k))).image
          (fun d => f ⟨k, d⟩) at hv
      rcases Finset.mem_union.mp hv with h | h
      · exact Or.inl h
      · obtain ⟨d, _, hd⟩ := Finset.mem_image.mp h
        exact Or.inr ⟨d, hd⟩
    rcases split i hvi with hi | ⟨di, hdi⟩
    · rcases split j hvj with hj | ⟨dj, hdj⟩
      · exact (Finset.disjoint_left.mp (hdis hij)) hi hj
      · exact (hfout ⟨j, dj⟩) (hdj.symm ▸ hsub i hi)
    · rcases split j hvj with hj | ⟨dj, hdj⟩
      · exact (hfout ⟨i, di⟩) (hdi.symm ▸ hsub j hj)
      · have heq : (⟨i, di⟩ : nearCompleteDemands r X Y a) = ⟨j, dj⟩ :=
          hf (hdi.trans hdj.symm)
        exact hij (congrArg Sigma.fst heq)
  let M : MinorModel (SimpleGraph.completeGraph (Fin r)) G := {
    branch := fun i => (B i : Set V)
    connected := hconn
    disjoint := by
      intro i j hij
      simpa only [Finset.disjoint_coe] using hdisB hij
    adjacent := by
      intro i j hij
      obtain ⟨x, hx, y, hy, hxy⟩ := hcross i j (by simpa using hij)
      exact ⟨x, hbase i (Finset.mem_union_left _ hx),
        y, hbase j (Finset.mem_union_right _ hy), hxy⟩
  }
  exact ⟨M⟩

/-- A plentiful common-neighbor pool supplies the distinct connectors
needed by the near-complete block minor construction. -/
theorem hasCliqueMinor_of_blocks_common_neighbors
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (Z : Finset V)
    (X Y : Fin r → Finset V) (a : Fin r → V)
    (ha : ∀ i, a i ∈ X i)
    (hsub : ∀ i, X i ∪ Y i ⊆ Z)
    (hdis : Pairwise (fun i j => Disjoint (X i ∪ Y i) (X j ∪ Y j)))
    (hcommon : ∀ d : nearCompleteDemands r X Y a,
      Fintype.card (nearCompleteDemands r X Y a) ≤
        ((G.neighborFinset (a d.1) ∩ G.neighborFinset d.2.1) \ Z).card)
    (hcross : ∀ i j, i ≠ j →
      ∃ x ∈ X i, ∃ y ∈ Y j, G.Adj x y) :
    HasCliqueMinor G r := by
  classical
  let T : nearCompleteDemands r X Y a → Finset V :=
    fun d => (G.neighborFinset (a d.1) ∩ G.neighborFinset d.2.1) \ Z
  obtain ⟨f, hf, hchoice⟩ :=
    exists_injective_choice_of_large_candidates T (by
      intro d
      exact hcommon d)
  apply hasCliqueMinor_of_blocks_and_connectors G r Z X Y a f
    ha hsub hdis hf
  · intro d
    exact (Finset.mem_sdiff.mp (hchoice d)).2
  · intro d
    have h := (Finset.mem_sdiff.mp (hchoice d)).1
    have h' := Finset.mem_inter.mp h
    exact ⟨(G.mem_neighborFinset _ _).mp h'.1,
      (G.mem_neighborFinset _ _).mp h'.2 |>.symm⟩
  · exact hcross

/-- Vertices whose complement degree is at most twice the average
complement degree, using an integer cross-multiplied inequality. -/
noncomputable def lowMissingDegreeVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter (fun v =>
    Fintype.card V * (Gᶜ).degree v ≤ 4 * edgeCount Gᶜ)

/-- At least half the vertices have complement degree at most twice the
average. This is the reservoir-size step of Appendix C. -/
theorem two_mul_card_lowMissingDegreeVertices_ge_order
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card V ≤ 2 * (lowMissingDegreeVertices G).card := by
  classical
  let J := Gᶜ
  let n := Fintype.card V
  let m := edgeCount J
  let bad : Finset V := Finset.univ.filter (fun v => 4 * m < n * J.degree v)
  have hcomp : (lowMissingDegreeVertices G).card + bad.card = n := by
    have heq : bad = (lowMissingDegreeVertices G)ᶜ := by
      ext v
      simp [bad, lowMissingDegreeVertices, J, m, n, Nat.not_le]
    rw [heq]
    exact Finset.card_add_card_compl _
  by_cases hm : m = 0
  · have hbad : bad = ∅ := by
      ext v
      constructor
      · intro hv
        have hdeg : J.degree v ≤ m := by
          simpa only [m, edgeCount_eq_card_edgeFinset] using J.degree_le_card_edgeFinset v
        have hvbad : 4 * m < n * J.degree v := (Finset.mem_filter.mp hv).2
        have hdeq : J.degree v = 0 := by omega
        simp [hm, hdeq] at hvbad
      · intro hv
        simp at hv
    rw [hbad] at hcomp
    simp at hcomp
    omega
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hsum : (∑ v : V, J.degree v) = 2 * m := by
      simpa only [m, edgeCount_eq_card_edgeFinset] using
        J.sum_degrees_eq_twice_card_edges
    have hbadSum : (∑ v ∈ bad, J.degree v) ≤ 2 * m := by
      calc
        (∑ v ∈ bad, J.degree v) ≤ ∑ v : V, J.degree v := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro v hv _
          omega
        _ = 2 * m := hsum
    have hlow : 4 * m * bad.card ≤ n * (∑ v ∈ bad, J.degree v) := by
      have hterm : (∑ _v ∈ bad, 4 * m) ≤
          ∑ v ∈ bad, n * J.degree v := by
        apply Finset.sum_le_sum
        intro v hv
        exact le_of_lt (Finset.mem_filter.mp hv).2
      simpa [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using hterm
    have hbound : 2 * bad.card ≤ n := by
      have hprod := Nat.mul_le_mul_left n hbadSum
      have hmul : 4 * m * bad.card ≤ 2 * m * n := by nlinarith
      exact Nat.le_of_mul_le_mul_left (by nlinarith [hmpos]) hmpos
    omega

/-- If both endpoints lie in `Z`, the complement neighborhoods account for
all outside vertices that fail to be their common neighbors. -/
theorem order_le_common_outside_add_missing_degrees
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z : Finset V) (a v : V) (ha : a ∈ Z) (hv : v ∈ Z) :
    Fintype.card V ≤
      ((G.neighborFinset a ∩ G.neighborFinset v) \ Z).card +
        Z.card + (Gᶜ).degree a + (Gᶜ).degree v := by
  classical
  let J := Gᶜ
  let U := Z ∪ J.neighborFinset a ∪ J.neighborFinset v
  have hsubset : Uᶜ ⊆ (G.neighborFinset a ∩ G.neighborFinset v) \ Z := by
    intro w hw
    have hwU : w ∉ U := Finset.mem_compl.mp hw
    have hwZ : w ∉ Z := by
      intro h
      exact hwU (by simp [U, h])
    have hwJa : ¬ J.Adj a w := by
      intro h
      exact hwU (by simp [U, h])
    have hwJv : ¬ J.Adj v w := by
      intro h
      exact hwU (by simp [U, h])
    have hneA : a ≠ w := by
      intro h
      exact hwZ (h ▸ ha)
    have hneV : v ≠ w := by
      intro h
      exact hwZ (h ▸ hv)
    have hGa : G.Adj a w := by
      simpa [J, SimpleGraph.compl_adj, hneA] using hwJa
    have hGv : G.Adj v w := by
      simpa [J, SimpleGraph.compl_adj, hneV] using hwJv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset _ _).mpr hGa,
        (G.mem_neighborFinset _ _).mpr hGv⟩, hwZ⟩
  have hcardU : U.card ≤ Z.card + J.degree a + J.degree v := by
    have h1 := Finset.card_union_le Z (J.neighborFinset a)
    have h2 := Finset.card_union_le (Z ∪ J.neighborFinset a)
      (J.neighborFinset v)
    have haDegree : (J.neighborFinset a).card = J.degree a :=
      J.card_neighborFinset_eq_degree a
    have hvDegree : (J.neighborFinset v).card = J.degree v :=
      J.card_neighborFinset_eq_degree v
    dsimp [U]
    omega
  have houtside : Uᶜ.card + U.card = Fintype.card V :=
    Finset.card_compl_add_card U
  have hsubcard := Finset.card_le_card hsubset
  dsimp [J] at hcardU
  omega

/-- Select a one-third-sized reservoir of low complement-degree vertices. -/
theorem exists_low_missing_degree_reservoir
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ Z : Finset V,
      Z.card = Fintype.card V / 3 ∧
      ∀ v ∈ Z, Fintype.card V * (Gᶜ).degree v ≤ 4 * edgeCount Gᶜ := by
  classical
  have hhalf := two_mul_card_lowMissingDegreeVertices_ge_order G
  have hsize : Fintype.card V / 3 ≤ (lowMissingDegreeVertices G).card := by
    omega
  obtain ⟨Z, hZ, hcard⟩ :=
    Finset.exists_subset_card_eq hsize
  refine ⟨Z, hcard, ?_⟩
  intro v hv
  exact (Finset.mem_filter.mp (hZ hv)).2

/-- Under one-percent missing-edge density, any two vertices of the
one-third reservoir have more than `|Z|` common neighbors outside it. -/
theorem card_common_neighbors_outside_gt_reservoir
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z : Finset V) (a v : V)
    (hn : 27 ≤ Fintype.card V)
    (hq : 200 * edgeCount Gᶜ ≤
      Fintype.card V * (Fintype.card V - 1))
    (hZ : Z.card = Fintype.card V / 3)
    (hgood : ∀ w ∈ Z,
      Fintype.card V * (Gᶜ).degree w ≤ 4 * edgeCount Gᶜ)
    (ha : a ∈ Z) (hv : v ∈ Z) :
    Z.card < ((G.neighborFinset a ∩ G.neighborFinset v) \ Z).card := by
  let n := Fintype.card V
  let m := edgeCount Gᶜ
  have hapos : 50 * (Gᶜ).degree a ≤ n - 1 := by
    have h := hgood a ha
    have hprod : n * (50 * (Gᶜ).degree a) ≤ n * (n - 1) := by
      nlinarith [hq]
    exact Nat.le_of_mul_le_mul_left hprod (by omega : 0 < n)
  have hvpos : 50 * (Gᶜ).degree v ≤ n - 1 := by
    have h := hgood v hv
    have hprod : n * (50 * (Gᶜ).degree v) ≤ n * (n - 1) := by
      nlinarith [hq]
    exact Nat.le_of_mul_le_mul_left hprod (by omega : 0 < n)
  have hzthree : 3 * Z.card ≤ n := by omega
  have hsmall : 2 * Z.card + (Gᶜ).degree a + (Gᶜ).degree v < n := by
    omega
  have hcount := order_le_common_outside_add_missing_degrees G Z a v ha hv
  omega

/-- The deterministic conclusion of the near-complete auxiliary lemma:
once the random block selection supplies cross edges, the reservoir and
connector estimates produce the clique minor. -/
theorem hasCliqueMinor_of_dense_blocks
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (Z : Finset V) (X Y : Fin r → Finset V)
    (a : Fin r → V)
    (hn : 27 ≤ Fintype.card V)
    (hq : 200 * edgeCount Gᶜ ≤
      Fintype.card V * (Fintype.card V - 1))
    (hZ : Z.card = Fintype.card V / 3)
    (hgood : ∀ w ∈ Z,
      Fintype.card V * (Gᶜ).degree w ≤ 4 * edgeCount Gᶜ)
    (ha : ∀ i, a i ∈ X i)
    (hsub : ∀ i, X i ∪ Y i ⊆ Z)
    (hdis : Pairwise (fun i j => Disjoint (X i ∪ Y i) (X j ∪ Y j)))
    (hbudget : Fintype.card (nearCompleteDemands r X Y a) ≤ Z.card)
    (hcross : ∀ i j, i ≠ j →
      ∃ x ∈ X i, ∃ y ∈ Y j, G.Adj x y) :
    HasCliqueMinor G r := by
  classical
  apply hasCliqueMinor_of_blocks_common_neighbors G r Z X Y a
    ha hsub hdis
  · intro d
    have hanchor : a d.1 ∈ Z := hsub d.1
      (Finset.mem_union_left _ (ha d.1))
    have hdmem : d.2.1 ∈ Z := hsub d.1
      (Finset.mem_erase.mp d.2.2).2
    have hc := card_common_neighbors_outside_gt_reservoir
      G Z (a d.1) d.2.1 hn hq hZ hgood hanchor hdmem
    omega
  · exact hcross

/-- The auxiliary lemma's power condition already implies at most one
percent of pairs are missing. -/
theorem one_percent_of_near_complete_power_bound
    (t ℓ : ℕ) (ht : 1 ≤ t) (hℓ : 1 ≤ ℓ)
    (q : ℝ) (hq : 0 ≤ q)
    (hpower : 6 * (t : ℝ) * (100 * q) ^ (ℓ ^ 2) ≤ 1) :
    100 * q ≤ 1 := by
  by_contra h
  have hbase : 1 < 100 * q := lt_of_not_ge h
  have hpow : 1 < (100 * q) ^ (ℓ ^ 2) :=
    one_lt_pow₀ hbase (pow_ne_zero _ (by omega : ℓ ≠ 0))
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hprod := mul_lt_mul_of_pos_left hpow (by positivity : 0 < 6 * (t : ℝ))
  nlinarith

/-- Convert the one-percent statement to the integer inequality used by
the common-neighbor count. -/
theorem missing_edge_count_bound_of_fraction_one_percent
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2 ≤ Fintype.card V)
    (hq : 100 * ((edgeCount Gᶜ : ℝ) /
      ((Fintype.card V).choose 2 : ℝ)) ≤ 1) :
    200 * edgeCount Gᶜ ≤
      Fintype.card V * (Fintype.card V - 1) := by
  let n := Fintype.card V
  let m := edgeCount Gᶜ
  have hchoose : 0 < n.choose 2 := Nat.choose_pos (by omega)
  have hchooseR : (0 : ℝ) < n.choose 2 := by exact_mod_cast hchoose
  have hreal : (100 * m : ℝ) ≤ (n.choose 2 : ℝ) := by
    have h : (100 * (m : ℝ)) / (n.choose 2 : ℝ) ≤ 1 := by
      calc
        (100 * (m : ℝ)) / (n.choose 2 : ℝ) =
            100 * ((m : ℝ) / (n.choose 2 : ℝ)) := by ring
        _ ≤ 1 := hq
    exact (div_le_iff₀ hchooseR).mp h |>.trans_eq (by ring)
  have hnat : 100 * m ≤ n.choose 2 := by exact_mod_cast hreal
  have hpair : 2 * n.choose 2 = n * (n - 1) := by
    rw [Nat.choose_two_right]
    calc
      2 * (n * (n - 1) / 2) = (n * (n - 1) / 2) * 2 := by omega
      _ = n * (n - 1) := Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)
  change 200 * m ≤ n * (n - 1)
  omega

/-- A hypergeometric upper bound obtained from falling-factorial bounds on
binomial coefficients. -/
theorem choose_ratio_le_power
    (c m k : ℕ) (hkm : k ≤ m) :
    (Nat.choose c k : ℝ) / (Nat.choose m k : ℝ) ≤
      ((c : ℝ) / ((m + 1 - k : ℕ) : ℝ)) ^ k := by
  have hchoose : (0 : ℝ) < Nat.choose m k := by
    exact_mod_cast Nat.choose_pos hkm
  have hdenNat : 0 < m + 1 - k := by omega
  have hden : (0 : ℝ) < (m + 1 - k : ℕ) := by exact_mod_cast hdenNat
  have hfact : (0 : ℝ) < (k.factorial : ℕ) := by
    exact_mod_cast Nat.factorial_pos k
  have hnum : (Nat.choose c k : ℝ) * (k.factorial : ℝ) ≤
      (c : ℝ) ^ k := by
    have h := (Nat.choose_le_pow_div k c :
      (Nat.choose c k : ℝ) ≤ (c : ℝ) ^ k / (k.factorial : ℝ))
    exact (le_div_iff₀ hfact).mp h
  have hdenBound : ((m + 1 - k : ℕ) : ℝ) ^ k ≤
      (Nat.choose m k : ℝ) * (k.factorial : ℝ) := by
    have h := (Nat.pow_le_choose k m :
      (((m + 1 - k : ℕ) : ℝ) ^ k) / (k.factorial : ℝ) ≤
        (Nat.choose m k : ℝ))
    exact (div_le_iff₀ hfact).mp h
  have hcross : (Nat.choose c k : ℝ) *
      (((m + 1 - k : ℕ) : ℝ) ^ k) ≤
      (c : ℝ) ^ k * (Nat.choose m k : ℝ) := by
    have h₁ := mul_le_mul_of_nonneg_left hdenBound
      (Nat.cast_nonneg (Nat.choose c k) : (0 : ℝ) ≤ _)
    have h₂ := mul_le_mul_of_nonneg_right hnum
      (Nat.cast_nonneg (Nat.choose m k) : (0 : ℝ) ≤ _)
    nlinarith
  rw [div_pow]
  exact (div_le_div_iff₀ hchoose (pow_pos hden k)).mpr hcross

/-- A uniform fixed-size subset lies inside a prescribed exceptional set
with probability at most the corresponding power ratio. -/
theorem card_powersetCard_contained_ratio_le_power
    (U C : Finset V) (k : ℕ) (hC : C ⊆ U) (hk : k ≤ U.card) :
    (((U.powersetCard k).filter (fun X => X ⊆ C)).card : ℝ) /
        (Nat.choose U.card k : ℝ) ≤
      ((C.card : ℝ) / ((U.card + 1 - k : ℕ) : ℝ)) ^ k := by
  classical
  have heq : (U.powersetCard k).filter (fun X => X ⊆ C) =
      C.powersetCard k := by
    ext X
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · intro h
      exact ⟨h.2, h.1.2⟩
    · intro h
      exact ⟨⟨h.1.trans hC, h.2⟩, h.1⟩
  rw [heq, Finset.card_powersetCard]
  exact choose_ratio_le_power C.card U.card k hk
end HadwigerLean



