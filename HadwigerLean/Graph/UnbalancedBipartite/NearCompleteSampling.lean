import HadwigerLean.Graph.UnbalancedBipartite.NearComplete
import Mathlib.Logic.Equiv.Embedding
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Tactic

/-! Counting disjoint ordered block samples as finite embeddings. -/

namespace HadwigerLean

universe u v
variable {D : Type u} {β : Type v} [Fintype D] [DecidableEq D]

def splitEmbeddingEquiv (T : Finset D) :
    (D ↪ β) ≃
      Σ g : ((T : Set D) ↪ β),
        (↥((T : Set D)ᶜ) ↪ ↥((Set.range g)ᶜ)) :=
  (Equiv.embeddingCongr (Equiv.Set.sumCompl (T : Set D)).symm
    (Equiv.refl β)).trans Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted

theorem splitEmbeddingEquiv_fst (T : Finset D) (f : D ↪ β)
    (x : (T : Set D)) :
    (splitEmbeddingEquiv T f).1 x = f x.1 := by
  rfl



theorem splitEmbeddingEquiv_snd (T : Finset D) (f : D ↪ β)
    (x : ↥((T : Set D)ᶜ)) :
    ((splitEmbeddingEquiv T f).2 x).1 = f x.1 := by
  rfl
private def restrictedEmbeddingEquiv (T : Finset D) (C : Finset β) :
    {f : D ↪ β // ∀ x ∈ T, f x ∈ C} ≃
      Σ g : {g : ((T : Set D) ↪ β) // ∀ x, g x ∈ C},
        (↥((T : Set D)ᶜ) ↪ ↥((Set.range g.1)ᶜ)) := by
  let E := splitEmbeddingEquiv (β := β) T
  let P (f : D ↪ β) : Prop := ∀ x ∈ T, f x ∈ C
  let Q (h : Σ g : ((T : Set D) ↪ β),
      (↥((T : Set D)ᶜ) ↪ ↥((Set.range g)ᶜ))) : Prop :=
    ∀ x, h.1 x ∈ C
  have hPQ (f : D ↪ β) : P f ↔ Q (E f) := by
    constructor
    · intro hp x
      rw [splitEmbeddingEquiv_fst]
      exact hp x.1 x.2
    · intro hq x hx
      have h := hq ⟨x, hx⟩
      rw [splitEmbeddingEquiv_fst] at h
      exact h
  exact (E.subtypeEquiv hPQ).trans
    (Equiv.subtypeSigmaEquiv
      (fun g : ((T : Set D) ↪ β) =>
        (↥((T : Set D)ᶜ) ↪ ↥((Set.range g)ᶜ)))
      (fun g => ∀ x, g x ∈ C))







/-- All ordered vertex samples whose positions in `T` land in `C`. -/
noncomputable def restrictedEmbeddings [Fintype β]
    (T : Finset D) (C : Finset β) : Finset (D ↪ β) := by
  classical
  exact Finset.univ.filter (fun f => ∀ x ∈ T, f x ∈ C)

/-- The number of completions of a fixed embedding on `T` depends only on
its image size. -/
theorem card_embedding_completion [Fintype β]
    (T : Finset D) (g : ((T : Set D) ↪ β))
    [Fintype ↥((Set.range g)ᶜ)]
    [Fintype (↥((T : Set D)ᶜ) ↪ ↥((Set.range g)ᶜ))] :
    Fintype.card (↥((T : Set D)ᶜ) ↪ ↥((Set.range g)ᶜ)) =
      (Fintype.card β - T.card).descFactorial
        (Fintype.card D - T.card) := by
  classical
  rw [Fintype.card_embedding_eq]
  rw [Fintype.card_compl_set (Set.range g), Fintype.card_range]
  rw [Fintype.card_compl_set (T : Set D)]
  have hT : Fintype.card (T : Set D) = T.card := by
    exact Fintype.card_of_finset' T (by intro x; rfl)
  rw [hT]

/-- Exact count of ordered injective samples with all designated positions
inside `C`. -/
theorem card_restrictedEmbeddings [Fintype β]
    (T : Finset D) (C : Finset β) :
    (restrictedEmbeddings T C).card =
      C.card.descFactorial T.card *
        (Fintype.card β - T.card).descFactorial
          (Fintype.card D - T.card) := by
  classical
  have htype : (restrictedEmbeddings T C).card =
      Fintype.card {f : D ↪ β // ∀ x ∈ T, f x ∈ C} := by
    change ((Finset.univ.filter (fun f : D ↪ β => ∀ x ∈ T, f x ∈ C)).card) = _
    exact (Fintype.card_subtype (fun f : D ↪ β => ∀ x ∈ T, f x ∈ C)).symm
  rw [htype, Fintype.card_congr (restrictedEmbeddingEquiv T C)]
  rw [Fintype.card_sigma]
  simp_rw [card_embedding_completion T]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hbase :
      Fintype.card {g : ((T : Set D) ↪ β) // ∀ x, g x ∈ C} =
        C.card.descFactorial T.card := by
    have hc : Fintype.card
        {g : ((T : Set D) ↪ β) // ∀ x, g x ∈ C} =
        Fintype.card ((T : Set D) ↪ (C : Set β)) :=
      Fintype.card_congr (Equiv.codRestrict _ (C : Set β))
    rw [hc, Fintype.card_embedding_eq]
    have hT : Fintype.card (T : Set D) = T.card :=
      Fintype.card_of_finset' T (by intro x; rfl)
    have hC : Fintype.card (C : Set β) = C.card :=
      Fintype.card_of_finset' C (by intro x; rfl)
    rw [hT, hC]
  rw [hbase]
  norm_cast


/-- The designated positions of a uniform ordered injective sample all lie
in `C` with probability at most `(c/(z+1-k))^k`. -/
theorem restrictedEmbeddings_ratio_le_power [Fintype β]
    (T : Finset D) (C : Finset β)
    (hd : Fintype.card D ≤ Fintype.card β) :
    ((restrictedEmbeddings T C).card : ℝ) /
        (Fintype.card (D ↪ β) : ℝ) ≤
      ((C.card : ℝ) /
        ((Fintype.card β + 1 - T.card : ℕ) : ℝ)) ^ T.card := by
  classical
  let z := Fintype.card β
  let d := Fintype.card D
  let k := T.card
  let c := C.card
  have hkd : k ≤ d := by
    dsimp [k, d]
    exact Finset.card_le_univ T
  have hkz : k ≤ z := hkd.trans hd
  have hq : 0 < (z - k).descFactorial (d - k) :=
    Nat.descFactorial_pos.mpr (by omega)
  have hzdesc : 0 < z.descFactorial k :=
    Nat.descFactorial_pos.mpr hkz
  have hden : 0 < z + 1 - k := by omega
  have hcardΩ : Fintype.card (D ↪ β) =
      (z - k).descFactorial (d - k) * z.descFactorial k := by
    rw [Fintype.card_embedding_eq]
    exact (Nat.descFactorial_mul_descFactorial hkd).symm
  have hcardE : (restrictedEmbeddings T C).card =
      c.descFactorial k * (z - k).descFactorial (d - k) := by
    simpa only [c, k, z, d, mul_comm] using
      card_restrictedEmbeddings T C
  have hratio : ((restrictedEmbeddings T C).card : ℝ) /
      (Fintype.card (D ↪ β) : ℝ) =
        (c.descFactorial k : ℝ) / (z.descFactorial k : ℝ) := by
    rw [hcardE, hcardΩ]
    push_cast
    field_simp
  have hnum : (c.descFactorial k : ℝ) ≤ (c : ℝ) ^ k := by
    exact_mod_cast Nat.descFactorial_le_pow c k
  have hdenBound : (((z + 1 - k : ℕ) : ℝ) ^ k) ≤
      (z.descFactorial k : ℝ) := by
    exact_mod_cast Nat.pow_sub_le_descFactorial z k
  have hcross : (c.descFactorial k : ℝ) *
      (((z + 1 - k : ℕ) : ℝ) ^ k) ≤
      (c : ℝ) ^ k * (z.descFactorial k : ℝ) := by
    have h₁ := mul_le_mul_of_nonneg_left hdenBound
      (Nat.cast_nonneg (c.descFactorial k) : (0 : ℝ) ≤ _)
    have h₂ := mul_le_mul_of_nonneg_right hnum
      (Nat.cast_nonneg (z.descFactorial k) : (0 : ℝ) ≤ _)
    nlinarith
  rw [hratio, div_pow]
  exact (div_le_div_iff₀ (by exact_mod_cast hzdesc)
    (pow_pos (by exact_mod_cast hden) k)).mpr hcross

section Blocks

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One labelled block of positions in an ordered injective sample. -/
def blockPositions (r ℓ : ℕ) (i : Fin r) : Finset (Fin r × Fin ℓ) :=
  Finset.univ.image (fun j : Fin ℓ => (i, j))

/-- The vertex block at label `i` in an injective sample into `Z`. -/
noncomputable def sampledBlock (Z : Finset V) (r ℓ : ℕ)
    (f : (Fin r × Fin ℓ) ↪ (Z : Set V)) (i : Fin r) : Finset V := by
  classical
  exact Finset.univ.image (fun j : Fin ℓ => (f (i, j)).1)

theorem card_blockPositions (r ℓ : ℕ) (i : Fin r) :
    (blockPositions r ℓ i).card = ℓ := by
  classical
  rw [blockPositions, Finset.card_image_of_injective]
  · simp
  · intro j k h
    exact congrArg Prod.snd h

/-- Each sampled block has exactly `ℓ` vertices. -/
theorem sampledBlock_card (Z : Finset V) (r ℓ : ℕ)
    (f : (Fin r × Fin ℓ) ↪ (Z : Set V)) (i : Fin r) :
    (sampledBlock Z r ℓ f i).card = ℓ := by
  classical
  unfold sampledBlock
  rw [Finset.card_image_of_injective]
  · simp
  · intro j k h
    have hh : (i, j) = (i, k) := f.injective (Subtype.ext h)
    exact congrArg Prod.snd hh

/-- Every sampled block lies in the sampling reservoir. -/
theorem sampledBlock_subset (Z : Finset V) (r ℓ : ℕ)
    (f : (Fin r × Fin ℓ) ↪ (Z : Set V)) (i : Fin r) :
    sampledBlock Z r ℓ f i ⊆ Z := by
  classical
  intro v hv
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
  exact (f (i, j)).property

/-- Distinct sampled blocks are disjoint because the sample is injective. -/
theorem sampledBlock_disjoint (Z : Finset V) (r ℓ : ℕ)
    (f : (Fin r × Fin ℓ) ↪ (Z : Set V)) (i j : Fin r) (hij : i ≠ j) :
    Disjoint (sampledBlock Z r ℓ f i) (sampledBlock Z r ℓ f j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hvi
  obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hvj
  have heq : (i, p) = (j, q) := f.injective (Subtype.ext (hp.trans hq.symm))
  exact hij (congrArg Prod.fst heq)

end Blocks

/-- Both the first-block and conditional second-block sampling reservoirs
have denominator at least one quarter of the ambient order. -/
theorem four_mul_reservoir_gap_ge_order
    (t n : ℕ) (ht : 3 ≤ t) :
    n ≤ 4 * (n / 3 + 1 - 2 * (n / (9 * t))) := by
  let z := n / 3
  let ℓ := n / (9 * t)
  have hdiv : 9 * t * ℓ ≤ n := by
    dsimp [ℓ]
    exact Nat.mul_div_le n (9 * t)
  have h27 : 27 * ℓ ≤ n := by
    nlinarith
  have hupper : n < 3 * (z + 1) := by
    dsimp [z]
    simpa [mul_comm] using
      (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3)).mp
        (Nat.lt_succ_self (n / 3))
  have hgap : 2 * ℓ ≤ z + 1 := by omega
  dsimp [z, ℓ] at *
  omega

section ExceptionalVertices

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Reservoir vertices other than `v` that are not adjacent to `v`. -/
noncomputable def reservoirNonNeighbors
    (G : SimpleGraph V) (Z : Finset V) (v : V) :
    Finset (Z : Set V) := by
  classical
  exact Finset.univ.filter (fun z => z.1 ≠ v ∧ ¬ G.Adj v z.1)

/-- The exceptional set inside a reservoir is bounded by the complement
degree in the full graph. -/
theorem card_reservoirNonNeighbors_le_compl_degree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z : Finset V) (v : V) :
    (reservoirNonNeighbors G Z v).card ≤ (Gᶜ).degree v := by
  classical
  have hsubset : (reservoirNonNeighbors G Z v).map
      (.subtype (· ∈ (Z : Set V))) ⊆ (Gᶜ).neighborFinset v := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hw
    have hbad : z.1 ≠ v ∧ ¬G.Adj v z.1 := by
      simpa [reservoirNonNeighbors] using hz
    exact ((Gᶜ).mem_neighborFinset _ _).mpr
      (by simpa [SimpleGraph.compl_adj] using
        (show v ≠ z.1 ∧ ¬G.Adj v z.1 from ⟨hbad.1.symm, hbad.2⟩))
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_map, (Gᶜ).card_neighborFinset_eq_degree] at hcard
  exact hcard

/-- A block is contained in the exceptional vertices exactly when it avoids
`v` and has no edge to `v`. -/
theorem sampledBlock_subset_reservoirNonNeighbors_iff
    (G : SimpleGraph V) (Z : Finset V) (r ℓ : ℕ)
    (f : (Fin r × Fin ℓ) ↪ (Z : Set V)) (i : Fin r) (v : V) :
    (∀ p ∈ blockPositions r ℓ i,
      f p ∈ reservoirNonNeighbors G Z v) ↔
      v ∉ sampledBlock Z r ℓ f i ∧
        (∀ x ∈ sampledBlock Z r ℓ f i, ¬ G.Adj v x) := by
  classical
  constructor
  · intro h
    constructor
    · intro hv
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hv
      have hmem : (i, j) ∈ blockPositions r ℓ i := by
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      have hbad : (f (i, j)).1 ≠ v ∧ ¬G.Adj v (f (i, j)).1 := by
        simpa [reservoirNonNeighbors] using h (i, j) hmem
      exact hbad.1 hj
    · intro x hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      have hmem : (i, j) ∈ blockPositions r ℓ i := by
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      have hbad : (f (i, j)).1 ≠ v ∧ ¬G.Adj v (f (i, j)).1 := by
        simpa [reservoirNonNeighbors] using h (i, j) hmem
      exact hbad.2
  · rintro ⟨havoid, hnon⟩ p hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
    have hbad : (f (i, j)).1 ≠ v ∧ ¬G.Adj v (f (i, j)).1 := by
      constructor
      · intro heq
        apply havoid
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, heq⟩
      · apply hnon
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    simpa [reservoirNonNeighbors] using hbad

end ExceptionalVertices

/-- For any fixed vertex, an injectively sampled block avoiding it and all
its neighbors has the expected hypergeometric upper bound. -/
theorem reservoirNonNeighbors_sample_ratio_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z : Finset V) (r ℓ : ℕ) (i : Fin r) (v : V)
    (hsize : r * ℓ ≤ Z.card) :
    ((restrictedEmbeddings (blockPositions r ℓ i)
      (reservoirNonNeighbors G Z v)).card : ℝ) /
        (Fintype.card ((Fin r × Fin ℓ) ↪ (Z : Set V)) : ℝ) ≤
      (((Gᶜ).degree v : ℝ) /
        ((Z.card + 1 - ℓ : ℕ) : ℝ)) ^ ℓ := by
  classical
  have hd : Fintype.card (Fin r × Fin ℓ) ≤
      Fintype.card (Z : Set V) := by
    have hZ : Fintype.card (Z : Set V) = Z.card :=
      Fintype.card_of_finset' Z (by intro; rfl)
    simpa [Fintype.card_prod, hZ] using hsize
  have hratio := restrictedEmbeddings_ratio_le_power
    (blockPositions r ℓ i) (reservoirNonNeighbors G Z v) hd
  have hT : (blockPositions r ℓ i).card = ℓ := card_blockPositions r ℓ i
  have hZ : Fintype.card (Z : Set V) = Z.card :=
    Fintype.card_of_finset' Z (by intro; rfl)
  rw [hT, hZ] at hratio
  have hC := card_reservoirNonNeighbors_le_compl_degree G Z v
  have hden : (0 : ℝ) < (Z.card + 1 - ℓ : ℕ) := by
    have hℓZ : ℓ ≤ Z.card := by
      have hr : 1 ≤ r := by
        have hi := i.isLt
        omega
      calc
        ℓ = 1 * ℓ := by omega
        _ ≤ r * ℓ := Nat.mul_le_mul_right ℓ hr
        _ ≤ Z.card := hsize
    exact_mod_cast (by omega : 0 < Z.card + 1 - ℓ)
  have hquot : ((reservoirNonNeighbors G Z v).card : ℝ) /
      ((Z.card + 1 - ℓ : ℕ) : ℝ) ≤
      ((Gᶜ).degree v : ℝ) / ((Z.card + 1 - ℓ : ℕ) : ℝ) := by
    gcongr
  exact hratio.trans (pow_le_pow_left₀ (by positivity) hquot ℓ)

/-- A low complement degree and a quarter-order sampling denominator give
the `8q` one-vertex failure factor. -/
theorem low_degree_ratio_le_eight_missing_fraction
    (n m d den : ℕ) (hn : 2 ≤ n) (hgap : n ≤ 4 * den)
    (hdegree : n * d ≤ 4 * m) :
    (d : ℝ) / (den : ℝ) ≤
      8 * ((m : ℝ) / (n.choose 2 : ℝ)) := by
  have hden : (0 : ℝ) < den := by
    exact_mod_cast (by omega : 0 < den)
  have hchoose : (0 : ℝ) < n.choose 2 := by
    exact_mod_cast Nat.choose_pos hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hgapR : (n : ℝ) ≤ 4 * den := by exact_mod_cast hgap
  have hdegreeR : (n : ℝ) * d ≤ 4 * m := by exact_mod_cast hdegree
  have hchooseNat : 2 * n.choose 2 = n * (n - 1) := by
    rw [mul_comm 2, Nat.choose_two_right,
      Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)]
  have hchooseR : 2 * (n.choose 2 : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) := by
    have hh := congrArg (fun x : ℕ => (x : ℝ)) hchooseNat
    push_cast at hh
    have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have hnat : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
      have hreal : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        exact_mod_cast hnat
      linarith
    rw [hsub] at hh
    exact hh
  have hprod1 := mul_le_mul_of_nonneg_right hdegreeR
    (by linarith : (0 : ℝ) ≤ n)
  have hprod2 := mul_le_mul_of_nonneg_left hgapR
    (by positivity : (0 : ℝ) ≤ 4 * m)
  have hcross : (d : ℝ) * (n.choose 2 : ℝ) ≤
      8 * (m : ℝ) * (den : ℝ) := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ d by positivity)
      (show (0 : ℝ) ≤ (n : ℝ) by positivity)]
  have hgoal : (d : ℝ) / (den : ℝ) ≤
      (8 * (m : ℝ)) / (n.choose 2 : ℝ) :=
    (div_le_div_iff₀ hden hchoose).mpr hcross
  convert hgoal using 1 <;> ring
end HadwigerLean