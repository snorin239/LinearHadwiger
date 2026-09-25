import HadwigerLean.Graph.UnbalancedBipartite.NearCompleteSampling
import Mathlib.Tactic

/-! Finite double counting for the near-complete block selection. -/

namespace HadwigerLean
set_option maxHeartbeats 800000

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def sampledBadVertices
    (G : SimpleGraph V) [DecidableRel G.Adj] (Z : Finset V)
    (r ℓ : ℕ) (f : (Fin r × Fin ℓ) ↪ (Z : Set V)) (i : Fin r) :
    Finset V := by
  classical
  exact Z.filter (fun v => v ∉ sampledBlock Z r ℓ f i ∧
    ∀ x ∈ sampledBlock Z r ℓ f i, ¬ G.Adj v x)

theorem sum_sampledBadVertices_card
    (G : SimpleGraph V) [DecidableRel G.Adj] (Z : Finset V)
    (r ℓ : ℕ) (i : Fin r) :
    (∑ f : (Fin r × Fin ℓ) ↪ (Z : Set V),
      (sampledBadVertices G Z r ℓ f i).card) =
      ∑ v ∈ Z,
        (restrictedEmbeddings (blockPositions r ℓ i)
          (reservoirNonNeighbors G Z v)).card := by
  classical
  simp only [sampledBadVertices, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [restrictedEmbeddings, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro f hf
  simp only [sampledBlock_subset_reservoirNonNeighbors_iff]

/-- The average number of reservoir vertices missed by a labelled block is
bounded by the elementary `8q` factor. -/
theorem sum_sampledBadVertices_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (Z : Finset V)
    (r ℓ : ℕ) (i : Fin r)
    (hn : 2 ≤ Fintype.card V)
    (hsize : r * ℓ ≤ Z.card)
    (hgap : Fintype.card V ≤ 4 * (Z.card + 1 - ℓ))
    (hgood : ∀ v ∈ Z,
      Fintype.card V * (Gᶜ).degree v ≤ 4 * edgeCount Gᶜ) :
    (∑ f : (Fin r × Fin ℓ) ↪ (Z : Set V),
      ((sampledBadVertices G Z r ℓ f i).card : ℝ)) ≤
      (Fintype.card ((Fin r × Fin ℓ) ↪ (Z : Set V)) : ℝ) *
        (Z.card : ℝ) *
          (8 * ((edgeCount Gᶜ : ℝ) /
            ((Fintype.card V).choose 2 : ℝ))) ^ ℓ := by
  classical
  let Ω := (Fin r × Fin ℓ) ↪ (Z : Set V)
  let q : ℝ := (edgeCount Gᶜ : ℝ) /
    ((Fintype.card V).choose 2 : ℝ)
  have hZ : Fintype.card (Z : Set V) = Z.card :=
    Fintype.card_of_finset' Z (by intro; rfl)
  have hD : Fintype.card (Fin r × Fin ℓ) ≤
      Fintype.card (Z : Set V) := by
    simpa [Fintype.card_prod, hZ] using hsize
  have hΩ : (0 : ℝ) < Fintype.card Ω := by
    have hpos : 0 < Fintype.card Ω := by
      rw [Fintype.card_embedding_eq]
      exact Nat.descFactorial_pos.mpr hD
    exact_mod_cast hpos
  have hqnonneg : 0 ≤ q := by dsimp [q]; positivity
  have hterm (v : V) (hv : v ∈ Z) :
      ((restrictedEmbeddings (blockPositions r ℓ i)
        (reservoirNonNeighbors G Z v)).card : ℝ) ≤
        (Fintype.card Ω : ℝ) * (8 * q) ^ ℓ := by
    have hratio := reservoirNonNeighbors_sample_ratio_le
      G Z r ℓ i v hsize
    have hden : Fintype.card V ≤ 4 * (Z.card + 1 - ℓ) := hgap
    have hlow := low_degree_ratio_le_eight_missing_fraction
      (Fintype.card V) (edgeCount Gᶜ) ((Gᶜ).degree v)
      (Z.card + 1 - ℓ) hn hden (hgood v hv)
    have hpow :
        (((Gᶜ).degree v : ℝ) /
          ((Z.card + 1 - ℓ : ℕ) : ℝ)) ^ ℓ ≤ (8 * q) ^ ℓ := by
      exact pow_le_pow_left₀ (by positivity) hlow ℓ
    have hbound := hratio.trans hpow
    simpa [mul_comm] using (div_le_iff₀ hΩ).mp hbound
  have hsum := sum_sampledBadVertices_card G Z r ℓ i
  have hreal :
      (∑ f : Ω, ((sampledBadVertices G Z r ℓ f i).card : ℝ)) =
      ∑ v ∈ Z,
        ((restrictedEmbeddings (blockPositions r ℓ i)
          (reservoirNonNeighbors G Z v)).card : ℝ) := by
    exact_mod_cast hsum
  rw [hreal]
  calc
    (∑ v ∈ Z,
      ((restrictedEmbeddings (blockPositions r ℓ i)
        (reservoirNonNeighbors G Z v)).card : ℝ)) ≤
        ∑ _v ∈ Z, (Fintype.card Ω : ℝ) * (8 * q) ^ ℓ := by
          apply Finset.sum_le_sum
          intro v hv
          exact hterm v hv
    _ = (Fintype.card Ω : ℝ) * (Z.card : ℝ) * (8 * q) ^ ℓ := by
      simp only [Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul]
      ring
/-- Finite Markov counting with the one-third threshold. -/
theorem two_thirds_samples_good
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (b : Ω → ℕ) (M : ℝ) (hM : 0 < M)
    (hsum : (∑ ω : Ω, (b ω : ℝ)) ≤ (Fintype.card Ω : ℝ) * M) :
    2 * Fintype.card Ω ≤
      3 * (Finset.univ.filter (fun ω : Ω => (b ω : ℝ) ≤ 3 * M)).card := by
  classical
  let P (ω : Ω) : Prop := (b ω : ℝ) ≤ 3 * M
  let B := Finset.univ.filter (fun ω : Ω => ¬ P ω)
  have hBsum : (3 * M) * (B.card : ℝ) ≤ ∑ ω ∈ B, (b ω : ℝ) := by
    calc
      (3 * M) * (B.card : ℝ) = ∑ _ω ∈ B, 3 * M := by
        simp [mul_comm]
      _ ≤ ∑ ω ∈ B, (b ω : ℝ) := by
        apply Finset.sum_le_sum
        intro ω hω
        have hbad : ¬ P ω := (Finset.mem_filter.mp hω).2
        exact le_of_lt (lt_of_not_ge hbad)
  have hBsub : (∑ ω ∈ B, (b ω : ℝ)) ≤ ∑ ω : Ω, (b ω : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro ω _ _
    positivity
  have hcardR : 3 * (B.card : ℝ) ≤ Fintype.card Ω := by
    have hh : M * (3 * (B.card : ℝ)) ≤ M * (Fintype.card Ω : ℝ) := by
      nlinarith [hBsum, hBsub, hsum]
    exact le_of_mul_le_mul_left hh hM
  have hcard : 3 * B.card ≤ Fintype.card Ω := by
    exact_mod_cast hcardR
  have hpart :
      (Finset.univ.filter P).card + B.card = Fintype.card Ω := by
    simpa [B] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ) P)
  simpa only [P] using (show
    2 * Fintype.card Ω ≤ 3 * (Finset.univ.filter P).card by omega)
section ConditionalEmbedding

variable {D β : Type*} [Fintype D] [DecidableEq D]
  [Fintype β] [DecidableEq β]

noncomputable def conditionalEmbeddings
    (T : Finset D) (U : Finset (↥((T : Set D)ᶜ)))
    (C : ∀ g : ((T : Set D) ↪ β),
      Finset (↥((Set.range g)ᶜ))) : Finset (D ↪ β) := by
  classical
  exact Finset.univ.filter (fun f =>
    ∀ u ∈ U, (splitEmbeddingEquiv T f).2 u ∈
      C (splitEmbeddingEquiv T f).1)

set_option maxHeartbeats 800000 in
theorem card_conditionalEmbeddings
    (T : Finset D) (U : Finset (↥((T : Set D)ᶜ)))
    (C : ∀ g : ((T : Set D) ↪ β),
      Finset (↥((Set.range g)ᶜ))) :
    (conditionalEmbeddings T U C).card =
      ∑ g : ((T : Set D) ↪ β),
        (restrictedEmbeddings U (C g)).card := by
  classical
  let E := splitEmbeddingEquiv (β := β) T
  let P (f : D ↪ β) : Prop :=
    ∀ u ∈ U, (E f).2 u ∈ C (E f).1
  let Q (g : ((T : Set D) ↪ β))
      (h : ↥((T : Set D)ᶜ) ↪ ↥((Set.range g)ᶜ)) : Prop :=
    ∀ u ∈ U, h u ∈ C g
  have e₁ : {f : D ↪ β // P f} ≃
      {s : Σ g : ((T : Set D) ↪ β),
        (↥((T : Set D)ᶜ) ↪ ↥((Set.range g)ᶜ)) //
          Q s.1 s.2} :=
    E.subtypeEquiv (by intro f; rfl)
  have e₂ : {s : Σ g : ((T : Set D) ↪ β),
        (↥((T : Set D)ᶜ) ↪ ↥((Set.range g)ᶜ)) //
          Q s.1 s.2} ≃
      Σ g : ((T : Set D) ↪ β),
        {h : ↥((T : Set D)ᶜ) ↪ ↥((Set.range g)ᶜ) // Q g h} := {
    toFun := fun s => ⟨s.1.1, ⟨s.1.2, s.2⟩⟩
    invFun := fun s => ⟨⟨s.1, s.2.1⟩, s.2.2⟩
    left_inv := by
      rintro ⟨⟨g, h⟩, hh⟩
      rfl
    right_inv := by
      rintro ⟨g, ⟨h, hh⟩⟩
      rfl
  }
  let e := e₁.trans e₂
  have htype : (conditionalEmbeddings T U C).card =
      Fintype.card {f : D ↪ β // P f} := by
    exact (Fintype.card_subtype P).symm
  rw [htype, Fintype.card_congr e, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro g _
  rw [Fintype.card_subtype]
  congr 1
  ext f
  simp [restrictedEmbeddings, Q]

/-- Uniform conditional bound after exposing the positions in `T`. -/
theorem card_conditionalEmbeddings_le_power
    (T : Finset D) (U : Finset (↥((T : Set D)ᶜ)))
    (C : ∀ g : ((T : Set D) ↪ β),
      Finset (↥((Set.range g)ᶜ)))
    (c : ℝ) (hd : Fintype.card D ≤ Fintype.card β)
    (hC : ∀ g, ((C g).card : ℝ) ≤ c) :
    ((conditionalEmbeddings T U C).card : ℝ) ≤
      (Fintype.card (D ↪ β) : ℝ) *
        (c /
          ((Fintype.card β - T.card + 1 - U.card : ℕ) : ℝ)) ^ U.card := by
  classical
  let z := Fintype.card β
  let d := Fintype.card D
  let k := T.card
  let u := U.card
  let den := z - k + 1 - u
  let rate : ℝ := (c / (den : ℝ)) ^ u
  have hTcard : Fintype.card (T : Set D) = k :=
    Fintype.card_of_finset' T (by intro x; rfl)
  have hk : k ≤ d := Finset.card_le_univ T
  have hrest (g : ((T : Set D) ↪ β)) :
      Fintype.card ↥((T : Set D)ᶜ) ≤
        Fintype.card ↥((Set.range g)ᶜ) := by
    rw [Fintype.card_compl_set (T : Set D), hTcard,
      Fintype.card_compl_set (Set.range g), Fintype.card_range]
    omega
  have htarget (g : ((T : Set D) ↪ β)) :
      Fintype.card ↥((Set.range g)ᶜ) = z - k := by
    rw [Fintype.card_compl_set (Set.range g), Fintype.card_range,
      hTcard]
  have hHpos (g : ((T : Set D) ↪ β)) :
      (0 : ℝ) < Fintype.card
        (↥((T : Set D)ᶜ) ↪ ↥((Set.range g)ᶜ)) := by
    have hh : 0 < Fintype.card
        (↥((T : Set D)ᶜ) ↪ ↥((Set.range g)ᶜ)) := by
      rw [Fintype.card_embedding_eq]
      exact Nat.descFactorial_pos.mpr (hrest g)
    exact_mod_cast hh
  have hden : (0 : ℝ) < den := by
    have hu : u ≤ d - k := by
      dsimp [u]
      have h := Finset.card_le_univ U
      rw [Fintype.card_compl_set (T : Set D), hTcard] at h
      exact h
    have : 0 < den := by dsimp [den]; omega
    exact_mod_cast this
  have hterm (g : ((T : Set D) ↪ β)) :
      ((restrictedEmbeddings U (C g)).card : ℝ) ≤
        (Fintype.card
          (↥((T : Set D)ᶜ) ↪ ↥((Set.range g)ᶜ)) : ℝ) * rate := by
    have hratio := restrictedEmbeddings_ratio_le_power
      U (C g) (hrest g)
    rw [htarget g] at hratio
    have hquot : ((C g).card : ℝ) / (den : ℝ) ≤
        c / (den : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact hC g
      · exact le_of_lt hden
    have hpow := pow_le_pow_left₀ (by positivity) hquot u
    have hb := hratio.trans hpow
    simpa [rate, u, den, mul_comm] using
      (div_le_iff₀ (hHpos g)).mp hb
  have hfull :
      (∑ g : ((T : Set D) ↪ β),
        Fintype.card
          (↥((T : Set D)ᶜ) ↪ ↥((Set.range g)ᶜ))) =
        Fintype.card (D ↪ β) := by
    rw [Fintype.card_congr (splitEmbeddingEquiv (β := β) T),
      Fintype.card_sigma]
  have hcount := card_conditionalEmbeddings T U C
  have hreal : ((conditionalEmbeddings T U C).card : ℝ) =
      ∑ g : ((T : Set D) ↪ β),
        ((restrictedEmbeddings U (C g)).card : ℝ) := by
    exact_mod_cast hcount
  rw [hreal]
  calc
    (∑ g : ((T : Set D) ↪ β),
      ((restrictedEmbeddings U (C g)).card : ℝ)) ≤
      ∑ g : ((T : Set D) ↪ β),
        (Fintype.card
          (↥((T : Set D)ᶜ) ↪ ↥((Set.range g)ᶜ)) : ℝ) * rate := by
          apply Finset.sum_le_sum
          intro g _
          exact hterm g
    _ = (Fintype.card (D ↪ β) : ℝ) * rate := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, hfull]
    _ = _ := rfl
end ConditionalEmbedding
section ExceptionalAfterFirst

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Vertices outside an exposed first sample with no neighbor in it. -/
noncomputable def exceptionalAfterFirst
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z : Finset V) (T : Finset D)
    (g : ((T : Set D) ↪ (Z : Set V))) :
    Finset (↥((Set.range g)ᶜ)) := by
  classical
  exact Finset.univ.filter (fun y =>
    ∀ x : (T : Set D), ¬ G.Adj y.1.1 (g x).1)

end ExceptionalAfterFirst

/-- The exceptional vertices after exposing a sampled block inject into the
bad-vertex count used by the first-block averaging. -/
theorem card_exceptionalAfterFirst_le_sampledBadVertices
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z : Finset V) (r ℓ : ℕ)
    (f : (Fin r × Fin ℓ) ↪ (Z : Set V)) (i : Fin r) :
    (exceptionalAfterFirst G Z (blockPositions r ℓ i)
      (splitEmbeddingEquiv (blockPositions r ℓ i) f).1).card ≤
      (sampledBadVertices G Z r ℓ f i).card := by
  classical
  let T := blockPositions r ℓ i
  let g := (splitEmbeddingEquiv T f).1
  apply Finset.card_le_card_of_injOn
    (fun y : ↥((Set.range g)ᶜ) => y.1.1)
  · intro y hy
    have hybad : ∀ x : (T : Set (Fin r × Fin ℓ)),
        ¬ G.Adj y.1.1 (g x).1 := by
      simpa [exceptionalAfterFirst] using hy
    have hyoutside : y.1 ∉ Set.range g := y.2
    have hyZ : y.1.1 ∈ Z := y.1.2
    have hnot : y.1.1 ∉ sampledBlock Z r ℓ f i := by
      intro hmem
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
      let x : (T : Set (Fin r × Fin ℓ)) :=
        ⟨(i, j), Finset.mem_image.mpr
          ⟨j, Finset.mem_univ _, rfl⟩⟩
      have hfirst : (g x).1 = (f (i, j)).1 := by
        simpa [g] using congrArg Subtype.val
          (splitEmbeddingEquiv_fst T f x)
      apply hyoutside
      refine ⟨x, ?_⟩
      apply Subtype.ext
      exact hfirst.trans hj
    have hnone : ∀ x ∈ sampledBlock Z r ℓ f i,
        ¬ G.Adj y.1.1 x := by
      intro x hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      let p : (T : Set (Fin r × Fin ℓ)) :=
        ⟨(i, j), Finset.mem_image.mpr
          ⟨j, Finset.mem_univ _, rfl⟩⟩
      have hp := hybad p
      have hfirst : (g p).1 = (f (i, j)).1 := by
        simpa [g] using congrArg Subtype.val
          (splitEmbeddingEquiv_fst T f p)
      simpa [hfirst] using hp
    change y.1.1 ∈ Z.filter (fun v =>
      v ∉ sampledBlock Z r ℓ f i ∧
        ∀ x ∈ sampledBlock Z r ℓ f i, ¬G.Adj v x)
    exact Finset.mem_filter.mpr ⟨hyZ, hnot, hnone⟩
  · intro a _ b _ hab
    apply Subtype.ext
    apply Subtype.ext
    exact hab
/-- The zero-mean case of the same finite Markov estimate. -/
theorem two_thirds_samples_good_of_nonneg
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (b : Ω → ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hsum : (∑ ω : Ω, (b ω : ℝ)) ≤ (Fintype.card Ω : ℝ) * M) :
    2 * Fintype.card Ω ≤
      3 * (Finset.univ.filter (fun ω : Ω => (b ω : ℝ) ≤ 3 * M)).card := by
  classical
  by_cases hpos : 0 < M
  · exact two_thirds_samples_good b M hpos hsum
  have hzero : M = 0 := le_antisymm (le_of_not_gt hpos) hM
  have hbzero (ω : Ω) : b ω = 0 := by
    have hle : (b ω : ℝ) ≤ ∑ x : Ω, (b x : ℝ) :=
      Finset.single_le_sum (f := fun x : Ω => (b x : ℝ))
        (fun _ _ => by positivity) (Finset.mem_univ ω)
    have hsum0 : (∑ x : Ω, (b x : ℝ)) ≤ 0 := by
      simpa [hzero] using hsum
    have hb : (b ω : ℝ) = 0 := by
      have : (0 : ℝ) ≤ b ω := by positivity
      linarith
    exact_mod_cast hb
  have hfilter :
      (Finset.univ.filter (fun ω : Ω => (b ω : ℝ) ≤ 3 * M)) =
        (Finset.univ : Finset Ω) := by
    ext ω
    simp [hzero, hbzero ω]
  rw [hfilter]
  simp only [Finset.card_univ]
  omega
/-- At least two thirds of ordered samples expose a first block with few
vertices having no neighbor in it. -/
theorem two_thirds_first_blocks_good
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z : Finset V) (r ℓ : ℕ) (i : Fin r)
    (hn : 2 ≤ Fintype.card V)
    (hsize : r * ℓ ≤ Z.card)
    (hgap : Fintype.card V ≤ 4 * (Z.card + 1 - ℓ))
    (hgood : ∀ v ∈ Z,
      Fintype.card V * (Gᶜ).degree v ≤ 4 * edgeCount Gᶜ) :
    2 * Fintype.card ((Fin r × Fin ℓ) ↪ (Z : Set V)) ≤
      3 * (Finset.univ.filter
        (fun f : (Fin r × Fin ℓ) ↪ (Z : Set V) =>
          ((exceptionalAfterFirst G Z (blockPositions r ℓ i)
            (splitEmbeddingEquiv (blockPositions r ℓ i) f).1).card : ℝ) ≤
            3 * (Fintype.card V : ℝ) *
              (8 * ((edgeCount Gᶜ : ℝ) /
                ((Fintype.card V).choose 2 : ℝ))) ^ ℓ)).card := by
  classical
  let Ω := (Fin r × Fin ℓ) ↪ (Z : Set V)
  let q : ℝ := (edgeCount Gᶜ : ℝ) /
    ((Fintype.card V).choose 2 : ℝ)
  let M : ℝ := (Fintype.card V : ℝ) * (8 * q) ^ ℓ
  let b (f : Ω) : ℕ :=
    (exceptionalAfterFirst G Z (blockPositions r ℓ i)
      (splitEmbeddingEquiv (blockPositions r ℓ i) f).1).card
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hsumBad := sum_sampledBadVertices_le G Z r ℓ i
    hn hsize hgap hgood
  have hsumC : (∑ f : Ω, (b f : ℝ)) ≤
      ∑ f : Ω, ((sampledBadVertices G Z r ℓ f i).card : ℝ) := by
    apply Finset.sum_le_sum
    intro f _
    exact_mod_cast card_exceptionalAfterFirst_le_sampledBadVertices
      G Z r ℓ f i
  have hZn : Z.card ≤ Fintype.card V := Finset.card_le_univ Z
  have hZnR : (Z.card : ℝ) ≤ Fintype.card V := by exact_mod_cast hZn
  have hfactor : 0 ≤ (8 * q) ^ ℓ := by positivity
  have hbound : (∑ f : Ω, (b f : ℝ)) ≤
      (Fintype.card Ω : ℝ) * M := by
    calc
      (∑ f : Ω, (b f : ℝ)) ≤
          ∑ f : Ω, ((sampledBadVertices G Z r ℓ f i).card : ℝ) := hsumC
      _ ≤ (Fintype.card Ω : ℝ) * (Z.card : ℝ) * (8 * q) ^ ℓ := hsumBad
      _ ≤ (Fintype.card Ω : ℝ) * M := by
        dsimp [M]
        have h := mul_le_mul_of_nonneg_right hZnR hfactor
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ Fintype.card Ω by positivity)
          (show (0 : ℝ) ≤ (Fintype.card V : ℝ) - Z.card by linarith)]
  simpa only [b, M, q, mul_assoc] using
    two_thirds_samples_good_of_nonneg b M hM hbound
/-- Elementary numeric slack in the second-block failure probability. -/
theorem twelve_mul_eight_pow_le_hundred_pow
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : 12 * 8 ^ ℓ ≤ 100 ^ ℓ := by
  induction ℓ, hℓ using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ, pow_succ]
    nlinarith [Nat.zero_le (100 ^ k)]

/-- A good first block has conditional second-block failure at most
`(100q)^(ℓ²)`. -/
theorem good_first_conditional_rate_le
    (n den ℓ : ℕ) (c q : ℝ)
    (hℓ : 1 ≤ ℓ) (hq : 0 ≤ q) (hc : 0 ≤ c) (hn : 1 ≤ n)
    (hgap : n ≤ 4 * den)
    (hgood : c ≤ 3 * (n : ℝ) * (8 * q) ^ ℓ) :
    (c / (den : ℝ)) ^ ℓ ≤
      (100 * q) ^ (ℓ ^ 2) := by
  have hden : (0 : ℝ) < den := by
    exact_mod_cast (by omega : 0 < den)
  have hgapR : (n : ℝ) ≤ 4 * den := by exact_mod_cast hgap
  have hpow : 0 ≤ (8 * q) ^ ℓ := by positivity
  have hquot : c / (den : ℝ) ≤ 12 * (8 * q) ^ ℓ := by
    apply (div_le_iff₀ hden).mpr
    have hh := mul_le_mul_of_nonneg_right hgapR hpow
    nlinarith
  have hnum : (12 : ℝ) * 8 ^ ℓ ≤ 100 ^ ℓ := by
    exact_mod_cast twelve_mul_eight_pow_le_hundred_pow ℓ hℓ
  have hbase : 12 * (8 * q) ^ ℓ ≤ (100 * q) ^ ℓ := by
    rw [mul_pow, mul_pow]
    nlinarith [mul_le_mul_of_nonneg_right hnum
      (pow_nonneg hq ℓ)]
  have h := pow_le_pow_left₀ (by positivity) (hquot.trans hbase) ℓ
  simpa only [← pow_mul, pow_two] using h
/-- Positions of another block, viewed in the complement of the first
block's positions. -/
def secondBlockPositions (r ℓ : ℕ) (i j : Fin r) (hij : i ≠ j) :
    Finset (↥((blockPositions r ℓ i : Set (Fin r × Fin ℓ))ᶜ)) := by
  classical
  exact Finset.univ.image (fun k : Fin ℓ =>
    (⟨(j, k), by
      change (j, k) ∉ blockPositions r ℓ i
      intro hm
      obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hm
      exact hij (congrArg Prod.fst hp)⟩ :
      ↥((blockPositions r ℓ i : Set (Fin r × Fin ℓ))ᶜ)))

theorem secondBlockPositions_card
    (r ℓ : ℕ) (i j : Fin r) (hij : i ≠ j) :
    (secondBlockPositions r ℓ i j hij).card = ℓ := by
  classical
  unfold secondBlockPositions
  rw [Finset.card_image_of_injective]
  · simp
  · intro p q hpq
    exact congrArg (Prod.snd ∘ Subtype.val) hpq
/-- Truncate exceptional second vertices unless the first block meets the
good-block threshold. -/
noncomputable def truncatedExceptional
    {D : Type*} [Fintype D] [DecidableEq D]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z : Finset V) (T : Finset D) (c : ℝ)
    (g : ((T : Set D) ↪ (Z : Set V))) :
    Finset (↥((Set.range g)ᶜ)) := by
  classical
  exact if ((exceptionalAfterFirst G Z T g).card : ℝ) ≤ c then
    exceptionalAfterFirst G Z T g else ∅

theorem card_truncatedExceptional_le
    {D : Type*} [Fintype D] [DecidableEq D]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z : Finset V) (T : Finset D) (c : ℝ) (hc : 0 ≤ c)
    (g : ((T : Set D) ↪ (Z : Set V))) :
    ((truncatedExceptional G Z T c g).card : ℝ) ≤ c := by
  classical
  unfold truncatedExceptional
  split_ifs with h
  · exact h
  · simpa using hc

/-- A graph-nonadjacent second block is contained in the exceptional
vertices of the exposed first block. -/
theorem second_block_mem_conditionalEmbeddings
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z : Finset V) (r ℓ : ℕ)
    (f : (Fin r × Fin ℓ) ↪ (Z : Set V))
    (i j : Fin r) (hij : i ≠ j)
    (hno : ∀ x ∈ sampledBlock Z r ℓ f i,
      ∀ y ∈ sampledBlock Z r ℓ f j, ¬ G.Adj x y) :
    f ∈ conditionalEmbeddings (blockPositions r ℓ i)
      (secondBlockPositions r ℓ i j hij)
      (exceptionalAfterFirst G Z (blockPositions r ℓ i)) := by
  classical
  let T := blockPositions r ℓ i
  let E := splitEmbeddingEquiv (β := (Z : Set V)) T
  simp only [conditionalEmbeddings, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change ∀ u ∈ secondBlockPositions r ℓ i j hij,
    (E f).2 u ∈ exceptionalAfterFirst G Z T (E f).1
  intro u hu
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hu
  simp only [exceptionalAfterFirst, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change ∀ x : (T : Set (Fin r × Fin ℓ)),
    ¬ G.Adj (((E f).2 ⟨(j, k), by
      change (j, k) ∉ T
      intro hm
      obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hm
      exact hij (congrArg Prod.fst hp)⟩).1.1) (((E f).1 x).1)
  intro x
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp x.2
  have hfirst : (((E f).1 x).1) = (f (i, p)).1 := by
    simpa [E, T, hp] using congrArg Subtype.val
      (splitEmbeddingEquiv_fst T f x)
  have hsecond : (((E f).2 ⟨(j, k), by
      change (j, k) ∉ T
      intro hm
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hm
      exact hij (congrArg Prod.fst ha)⟩).1.1) = (f (j, k)).1 := by
    simpa [E, T] using congrArg Subtype.val
      (splitEmbeddingEquiv_snd T f
        ⟨(j, k), by
          change (j, k) ∉ T
          intro hm
          obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hm
          exact hij (congrArg Prod.fst ha)⟩)
  rw [hfirst, hsecond]
  intro hadj
  exact hno (f (i, p)).1
    (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩)
    (f (j, k)).1
    (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩) hadj.symm
/-- The sample outcomes in which a good first block has no edge to a
specified second block occupy at most the `(100q)^(ℓ²)` fraction. -/
theorem good_pair_failure_count_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z : Finset V) (r ℓ : ℕ) (i j : Fin r) (hij : i ≠ j)
    (hn : 1 ≤ Fintype.card V) (hℓ : 1 ≤ ℓ)
    (hsize : r * ℓ ≤ Z.card)
    (hgap : Fintype.card V ≤ 4 * (Z.card + 1 - 2 * ℓ)) :
    let q : ℝ := (edgeCount Gᶜ : ℝ) /
      ((Fintype.card V).choose 2 : ℝ);
    let c : ℝ := 3 * (Fintype.card V : ℝ) * (8 * q) ^ ℓ;
    ((Finset.univ.filter
      (fun f : (Fin r × Fin ℓ) ↪ (Z : Set V) =>
        ((exceptionalAfterFirst G Z (blockPositions r ℓ i)
          (splitEmbeddingEquiv (blockPositions r ℓ i) f).1).card : ℝ) ≤ c ∧
        ∀ x ∈ sampledBlock Z r ℓ f i,
          ∀ y ∈ sampledBlock Z r ℓ f j, ¬ G.Adj x y)).card : ℝ) ≤
      (Fintype.card ((Fin r × Fin ℓ) ↪ (Z : Set V)) : ℝ) *
        (100 * q) ^ (ℓ ^ 2) := by
  classical
  let q : ℝ := (edgeCount Gᶜ : ℝ) /
    ((Fintype.card V).choose 2 : ℝ)
  let c : ℝ := 3 * (Fintype.card V : ℝ) * (8 * q) ^ ℓ
  let T := blockPositions r ℓ i
  let U := secondBlockPositions r ℓ i j hij
  let C := truncatedExceptional G Z T c
  let Ω := (Fin r × Fin ℓ) ↪ (Z : Set V)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcardT : T.card = ℓ := card_blockPositions r ℓ i
  have hcardU : U.card = ℓ := secondBlockPositions_card r ℓ i j hij
  have hZ : Fintype.card (Z : Set V) = Z.card :=
    Fintype.card_of_finset' Z (by intro; rfl)
  have hD : Fintype.card (Fin r × Fin ℓ) ≤
      Fintype.card (Z : Set V) := by
    simpa [Fintype.card_prod, hZ] using hsize
  have hr : 2 ≤ r := by
    have hi := i.isLt
    have hj := j.isLt
    by_contra h
    interval_cases r <;> fin_cases i <;> fin_cases j <;> contradiction
  have h2ℓ : 2 * ℓ ≤ Z.card := by
    nlinarith [hsize]
  have hdenNat :
      Fintype.card (Z : Set V) - T.card + 1 - U.card =
        Z.card + 1 - 2 * ℓ := by
    rw [hZ, hcardT, hcardU]
    omega
  have hdenGap : Fintype.card V ≤
      4 * (Fintype.card (Z : Set V) - T.card + 1 - U.card) := by
    rw [hdenNat]
    exact hgap
  have hrate := good_first_conditional_rate_le
    (Fintype.card V)
    (Fintype.card (Z : Set V) - T.card + 1 - U.card)
    ℓ c q hℓ hq hc hn hdenGap (le_refl c)
  have hC (g : ((T : Set (Fin r × Fin ℓ)) ↪ (Z : Set V))) :
      ((C g).card : ℝ) ≤ c :=
    card_truncatedExceptional_le G Z T c hc g
  have hcond := card_conditionalEmbeddings_le_power T U C c hD hC
  rw [hcardU] at hcond hrate
  have hbound : ((conditionalEmbeddings T U C).card : ℝ) ≤
      (Fintype.card Ω : ℝ) * (100 * q) ^ (ℓ ^ 2) := by
    exact hcond.trans (mul_le_mul_of_nonneg_left hrate (by positivity))
  have hsubset :
      (Finset.univ.filter
        (fun f : Ω =>
          ((exceptionalAfterFirst G Z T (splitEmbeddingEquiv T f).1).card : ℝ) ≤ c ∧
          ∀ x ∈ sampledBlock Z r ℓ f i,
            ∀ y ∈ sampledBlock Z r ℓ f j, ¬ G.Adj x y)) ⊆
        conditionalEmbeddings T U C := by
    intro f hf
    obtain ⟨hgood, hno⟩ := (Finset.mem_filter.mp hf).2
    have hmem := second_block_mem_conditionalEmbeddings G Z r ℓ f i j hij hno
    have htrunc : C (splitEmbeddingEquiv T f).1 =
        exceptionalAfterFirst G Z T (splitEmbeddingEquiv T f).1 := by
      simpa [C, truncatedExceptional, hgood]
    simp only [conditionalEmbeddings, Finset.mem_filter,
      Finset.mem_univ, true_and] at hmem ⊢
    simpa only [htrunc] using hmem
  have hcard := Finset.card_le_card hsubset
  exact (by exact_mod_cast hcard :
    ((Finset.univ.filter
      (fun f : Ω =>
        ((exceptionalAfterFirst G Z T (splitEmbeddingEquiv T f).1).card : ℝ) ≤ c ∧
        ∀ x ∈ sampledBlock Z r ℓ f i,
          ∀ y ∈ sampledBlock Z r ℓ f j, ¬ G.Adj x y)).card : ℝ) ≤
      ((conditionalEmbeddings T U C).card : ℝ)).trans hbound
/-- A finite union bound and averaging: if at least two thirds of outcomes
are good and each of `t` failures occupies at most a `p` fraction of good
outcomes, then at least half avoid every failure when `6tp ≤ 1`. -/
theorem half_samples_avoid_all_failures
    {Ω J : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype J] [DecidableEq J]
    (Good : Ω → Prop) (Fail : J → Ω → Prop)
    [DecidablePred Good] [∀ j, DecidablePred (Fail j)]
    (p : ℝ) (hp : 0 ≤ p)
    (hgood : 2 * Fintype.card Ω ≤
      3 * (Finset.univ.filter Good).card)
    (hfail : ∀ j,
      ((Finset.univ.filter (fun ω => Good ω ∧ Fail j ω)).card : ℝ) ≤
        (Fintype.card Ω : ℝ) * p)
    (hsmall : 6 * (Fintype.card J : ℝ) * p ≤ 1) :
    Fintype.card Ω ≤
      2 * (Finset.univ.filter (fun ω =>
        Good ω ∧ ∀ j, ¬ Fail j ω)).card := by
  classical
  let A := Finset.univ.filter Good
  let S := A.filter (fun ω => ∀ j, ¬ Fail j ω)
  let B := A.filter (fun ω => ∃ j, Fail j ω)
  let F (j : J) := Finset.univ.filter (fun ω => Good ω ∧ Fail j ω)
  have hBsub : B ⊆ Finset.univ.biUnion F := by
    intro ω hω
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hω).2
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp (Finset.mem_filter.mp hω).1).2, hj⟩⟩
  have hBcard : B.card ≤ ∑ j : J, (F j).card :=
    (Finset.card_le_card hBsub).trans Finset.card_biUnion_le
  have hBreal : (B.card : ℝ) ≤
      (Fintype.card J : ℝ) * (Fintype.card Ω : ℝ) * p := by
    have hh : (B.card : ℝ) ≤ ∑ j : J, ((F j).card : ℝ) := by
      exact_mod_cast hBcard
    calc
      (B.card : ℝ) ≤ ∑ j : J, ((F j).card : ℝ) := hh
      _ ≤ ∑ _j : J, (Fintype.card Ω : ℝ) * p := by
        apply Finset.sum_le_sum
        intro j _
        exact hfail j
      _ = (Fintype.card J : ℝ) * (Fintype.card Ω : ℝ) * p := by
        simp [mul_assoc]
  have hpart : S.card + B.card = A.card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := A) (fun ω : Ω => ∀ j, ¬ Fail j ω)
    simpa [S, B, not_forall, not_not] using h
  have hgoodR : 2 * (Fintype.card Ω : ℝ) ≤ 3 * (A.card : ℝ) := by
    exact_mod_cast hgood
  have hsmallR : 6 * (Fintype.card J : ℝ) * p *
      (Fintype.card Ω : ℝ) ≤ Fintype.card Ω := by
    have hh := mul_le_mul_of_nonneg_right hsmall
      (show (0 : ℝ) ≤ Fintype.card Ω by positivity)
    nlinarith
  have hresultR : (Fintype.card Ω : ℝ) ≤ 2 * (S.card : ℝ) := by
    have hpartR : (S.card : ℝ) + B.card = A.card := by
      exact_mod_cast hpart
    nlinarith [hBreal, hgoodR, hsmallR]
  have hresultN : Fintype.card Ω ≤ 2 * S.card := by
    exact_mod_cast hresultR
  simpa [S, A, Finset.filter_filter, and_comm] using hresultN
/-- If each of `2t` labels succeeds on at least half the samples, some
sample has at least `t` successful labels. -/
theorem exists_sample_with_half_successful_labels
    {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    [Fintype I] [DecidableEq I]
    (Success : I → Ω → Prop) [∀ i, DecidablePred (Success i)]
    (hhalf : ∀ i,
      Fintype.card Ω ≤
        2 * (Finset.univ.filter (Success i)).card) :
    ∃ ω : Ω,
      Fintype.card I ≤
        2 * (Finset.univ.filter (fun i => Success i ω)).card := by
  classical
  let a (i : I) : ℕ := (Finset.univ.filter (Success i)).card
  let b (ω : Ω) : ℕ :=
    (Finset.univ.filter (fun i : I => Success i ω)).card
  have hsum : Fintype.card I * Fintype.card Ω ≤
      2 * ∑ i : I, a i := by
    have hh : ∑ _i : I, Fintype.card Ω ≤
        ∑ i : I, 2 * a i := by
      apply Finset.sum_le_sum
      intro i _
      exact hhalf i
    simpa [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using hh
  have hswap : (∑ i : I, a i) = ∑ ω : Ω, b ω := by
    simp only [a, b, Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hswap] at hsum
  by_contra hnone
  push_neg at hnone
  have hstrict (ω : Ω) : 2 * b ω + 1 ≤ Fintype.card I := by
    have hh : 2 * b ω < Fintype.card I := by
      simpa only [b] using hnone ω
    omega
  have hsumBound : ∑ ω : Ω, (2 * b ω + 1) ≤
      ∑ _ω : Ω, Fintype.card I := by
    apply Finset.sum_le_sum
    intro ω _
    exact hstrict ω
  have hpos : 0 < Fintype.card Ω := Fintype.card_pos
  have hleft : (∑ ω : Ω, (2 * b ω + 1)) =
      2 * (∑ ω : Ω, b ω) + Fintype.card Ω := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hright : (∑ _ω : Ω, Fintype.card I) =
      Fintype.card I * Fintype.card Ω := by
    simp [mul_comm]
  rw [hleft, hright] at hsumBound
  omega
/-- The first `2t` labels and the last `t` labels of a `3t`-block sample. -/
def xBlockLabel (t : ℕ) (i : Fin (2 * t)) : Fin (3 * t) :=
  ⟨i.1, by omega⟩

def yBlockLabel (t : ℕ) (j : Fin t) : Fin (3 * t) :=
  ⟨2 * t + j.1, by omega⟩

theorem xBlockLabel_ne_yBlockLabel
    (t : ℕ) (i : Fin (2 * t)) (j : Fin t) :
    xBlockLabel t i ≠ yBlockLabel t j := by
  intro h
  have hh := congrArg Fin.val h
  dsimp [xBlockLabel, yBlockLabel] at hh
  omega
/-- For each first label, at least half of all disjoint block samples give
it an edge to every second label. -/
theorem half_samples_first_block_crosses_all
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : ℕ) (ht : 3 ≤ t)
    (Z : Finset V) (i : Fin (2 * t))
    (hn : 9 * t ≤ Fintype.card V)
    (hZ : Z.card = Fintype.card V / 3)
    (hgood : ∀ v ∈ Z,
      Fintype.card V * (Gᶜ).degree v ≤ 4 * edgeCount Gᶜ)
    (hpower : 6 * (t : ℝ) *
      (100 * ((edgeCount Gᶜ : ℝ) /
        ((Fintype.card V).choose 2 : ℝ))) ^
          ((Fintype.card V / (9 * t)) ^ 2) ≤ 1) :
    let ℓ := Fintype.card V / (9 * t)
    Fintype.card ((Fin (3 * t) × Fin ℓ) ↪ (Z : Set V)) ≤
      2 * (Finset.univ.filter
        (fun f : (Fin (3 * t) × Fin ℓ) ↪ (Z : Set V) =>
          ∀ j : Fin t,
            ∃ x ∈ sampledBlock Z (3 * t) ℓ f (xBlockLabel t i),
              ∃ y ∈ sampledBlock Z (3 * t) ℓ f (yBlockLabel t j),
                G.Adj x y)).card := by
  classical
  let n := Fintype.card V
  let ℓ := n / (9 * t)
  let q : ℝ := (edgeCount Gᶜ : ℝ) / (n.choose 2 : ℝ)
  let c : ℝ := 3 * (n : ℝ) * (8 * q) ^ ℓ
  let Ω := (Fin (3 * t) × Fin ℓ) ↪ (Z : Set V)
  let ix := xBlockLabel t i
  let Good (f : Ω) : Prop :=
    ((exceptionalAfterFirst G Z (blockPositions (3 * t) ℓ ix)
      (splitEmbeddingEquiv (blockPositions (3 * t) ℓ ix) f).1).card : ℝ) ≤ c
  let Fail (j : Fin t) (f : Ω) : Prop :=
    ∀ x ∈ sampledBlock Z (3 * t) ℓ f ix,
      ∀ y ∈ sampledBlock Z (3 * t) ℓ f (yBlockLabel t j), ¬G.Adj x y
  have hn2 : 2 ≤ n := by omega
  have hℓ : 1 ≤ ℓ := by
    dsimp [ℓ]
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 9 * t)).mpr
    simpa using hn
  have hdiv : 9 * t * ℓ ≤ n := by
    dsimp [ℓ]
    exact Nat.mul_div_le n (9 * t)
  have hsize : 3 * t * ℓ ≤ Z.card := by
    rw [hZ]
    have hh : 3 * (3 * t * ℓ) ≤ n := by nlinarith [hdiv]
    omega
  have hgap2 : n ≤ 4 * (Z.card + 1 - 2 * ℓ) := by
    rw [hZ]
    exact four_mul_reservoir_gap_ge_order t n ht
  have hgap1 : n ≤ 4 * (Z.card + 1 - ℓ) := by
    omega
  have hGood : 2 * Fintype.card Ω ≤
      3 * (Finset.univ.filter Good).card := by
    simpa only [Good, ix, c, q, n, Ω] using
      two_thirds_first_blocks_good G Z (3 * t) ℓ ix hn2
        hsize hgap1 hgood
  have hFail (j : Fin t) :
      ((Finset.univ.filter (fun f : Ω => Good f ∧ Fail j f)).card : ℝ) ≤
        (Fintype.card Ω : ℝ) * (100 * q) ^ (ℓ ^ 2) := by
    simpa only [Good, Fail, ix, c, q, n, Ω] using
      good_pair_failure_count_le G Z (3 * t) ℓ ix
        (yBlockLabel t j) (xBlockLabel_ne_yBlockLabel t i j)
        (by omega : 1 ≤ n) hℓ hsize hgap2
  have hq : 0 ≤ (100 * q) ^ (ℓ ^ 2) := by
    dsimp [q]
    positivity
  have hsmall : 6 * (Fintype.card (Fin t) : ℝ) *
      (100 * q) ^ (ℓ ^ 2) ≤ 1 := by
    simpa only [Fintype.card_fin, q, ℓ, n] using hpower
  have hhalf := half_samples_avoid_all_failures Good Fail
    ((100 * q) ^ (ℓ ^ 2)) hq hGood hFail hsmall
  have hsubset :
      (Finset.univ.filter (fun f : Ω => Good f ∧
        ∀ j : Fin t, ¬Fail j f)) ⊆
      (Finset.univ.filter (fun f : Ω =>
        ∀ j : Fin t,
          ∃ x ∈ sampledBlock Z (3 * t) ℓ f ix,
            ∃ y ∈ sampledBlock Z (3 * t) ℓ f (yBlockLabel t j),
              G.Adj x y)) := by
    intro f hf
    obtain ⟨_, hall⟩ := (Finset.mem_filter.mp hf).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro j
    by_contra h
    apply hall j
    dsimp [Fail]
    push_neg at h
    exact h
  have hcsub := Finset.card_le_card hsubset
  have hhalfLocal : Fintype.card Ω ≤
      2 * (Finset.univ.filter (fun f : Ω => Good f ∧
        ∀ j : Fin t, ¬Fail j f)).card := by
    convert hhalf using 1
    apply congrArg (fun n : ℕ => 2 * n)
    apply congrArg Finset.card
    ext f
    simp
  have hfin : Fintype.card Ω ≤
      2 * (Finset.univ.filter (fun f : Ω =>
        ∀ j : Fin t,
          ∃ x ∈ sampledBlock Z (3 * t) ℓ f ix,
            ∃ y ∈ sampledBlock Z (3 * t) ℓ f (yBlockLabel t j),
              G.Adj x y)).card :=
    hhalfLocal.trans (Nat.mul_le_mul_left 2 hcsub)
  simpa only [ℓ, n, ix, Ω] using hfin
/-- Fix one disjoint-block outcome with at least `t` first blocks meeting
every one of the `t` second blocks. -/
theorem exists_sample_with_many_crossing_blocks
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : ℕ) (ht : 3 ≤ t)
    (Z : Finset V)
    (hn : 9 * t ≤ Fintype.card V)
    (hZ : Z.card = Fintype.card V / 3)
    (hgood : ∀ v ∈ Z,
      Fintype.card V * (Gᶜ).degree v ≤ 4 * edgeCount Gᶜ)
    (hpower : 6 * (t : ℝ) *
      (100 * ((edgeCount Gᶜ : ℝ) /
        ((Fintype.card V).choose 2 : ℝ))) ^
          ((Fintype.card V / (9 * t)) ^ 2) ≤ 1) :
    let ℓ := Fintype.card V / (9 * t)
    ∃ f : (Fin (3 * t) × Fin ℓ) ↪ (Z : Set V),
      t ≤ (Finset.univ.filter (fun i : Fin (2 * t) =>
        ∀ j : Fin t,
          ∃ x ∈ sampledBlock Z (3 * t) ℓ f (xBlockLabel t i),
            ∃ y ∈ sampledBlock Z (3 * t) ℓ f (yBlockLabel t j),
              G.Adj x y)).card := by
  classical
  let n := Fintype.card V
  let ℓ := n / (9 * t)
  let Ω := (Fin (3 * t) × Fin ℓ) ↪ (Z : Set V)
  let Success (i : Fin (2 * t)) (f : Ω) : Prop :=
    ∀ j : Fin t,
      ∃ x ∈ sampledBlock Z (3 * t) ℓ f (xBlockLabel t i),
        ∃ y ∈ sampledBlock Z (3 * t) ℓ f (yBlockLabel t j),
          G.Adj x y
  have hdiv : 9 * t * ℓ ≤ n := by
    dsimp [ℓ]
    exact Nat.mul_div_le n (9 * t)
  have hsize : 3 * t * ℓ ≤ Z.card := by
    rw [hZ]
    have hh : 3 * (3 * t * ℓ) ≤ n := by nlinarith [hdiv]
    omega
  have hD : Fintype.card (Fin (3 * t) × Fin ℓ) ≤
      Fintype.card (Z : Set V) := by
    have hcardZ : Fintype.card (Z : Set V) = Z.card :=
      Fintype.card_of_finset' Z (by intro; rfl)
    simpa [Fintype.card_prod, hcardZ] using hsize
  have hΩpos : 0 < Fintype.card Ω := by
    rw [Fintype.card_embedding_eq]
    exact Nat.descFactorial_pos.mpr hD
  letI : Nonempty Ω := Fintype.card_pos_iff.mp hΩpos
  have hhalf (i : Fin (2 * t)) :
      Fintype.card Ω ≤
        2 * (Finset.univ.filter (Success i)).card := by
    simpa only [Success, Ω, ℓ, n] using
      half_samples_first_block_crosses_all G t ht Z i hn hZ
        hgood hpower
  obtain ⟨f, hf⟩ := exists_sample_with_half_successful_labels
    Success hhalf
  have hcard : Fintype.card (Fin (2 * t)) = 2 * t := by simp
  rw [hcard] at hf
  refine ⟨f, ?_⟩
  have hh : t ≤
      (Finset.univ.filter (fun i : Fin (2 * t) => Success i f)).card := by
    omega
  simpa only [Success, Ω, ℓ, n] using hh
/-- Choose ordered distinct labels from a finite set with enough elements. -/
theorem exists_label_embedding_in_finset
    {α : Type*} [DecidableEq α] (S : Finset α) (t : ℕ)
    (hcard : t ≤ S.card) :
    ∃ e : Fin t ↪ α, ∀ i, e i ∈ S := by
  classical
  obtain ⟨T, hsub, hT⟩ := Finset.exists_subset_card_eq hcard
  let e₀ : Fin t ≃ T := (Finset.equivFinOfCardEq hT).symm
  let e : Fin t ↪ α :=
    ⟨fun i => (e₀ i).1, Subtype.val_injective.comp e₀.injective⟩
  exact ⟨e, fun i => hsub (e₀ i).2⟩

/-- The deterministic branch construction applied to a successful labelled
block sample. -/
theorem hasCliqueMinor_of_successful_sample
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : ℕ) (ht : 3 ≤ t) (Z : Finset V)
    (hn : 9 * t ≤ Fintype.card V)
    (hZ : Z.card = Fintype.card V / 3)
    (hgood : ∀ v ∈ Z,
      Fintype.card V * (Gᶜ).degree v ≤ 4 * edgeCount Gᶜ)
    (hpower : 6 * (t : ℝ) *
      (100 * ((edgeCount Gᶜ : ℝ) /
        ((Fintype.card V).choose 2 : ℝ))) ^
          ((Fintype.card V / (9 * t)) ^ 2) ≤ 1)
    (f : (Fin (3 * t) × Fin (Fintype.card V / (9 * t))) ↪ (Z : Set V))
    (hmany : t ≤ (Finset.univ.filter (fun i : Fin (2 * t) =>
      ∀ j : Fin t,
        ∃ x ∈ sampledBlock Z (3 * t) (Fintype.card V / (9 * t)) f
          (xBlockLabel t i),
          ∃ y ∈ sampledBlock Z (3 * t) (Fintype.card V / (9 * t)) f
            (yBlockLabel t j), G.Adj x y)).card) :
    HasCliqueMinor G t := by
  classical
  let n := Fintype.card V
  let ℓ := n / (9 * t)
  let S : Finset (Fin (2 * t)) := Finset.univ.filter (fun i =>
    ∀ j : Fin t,
      ∃ x ∈ sampledBlock Z (3 * t) ℓ f (xBlockLabel t i),
        ∃ y ∈ sampledBlock Z (3 * t) ℓ f (yBlockLabel t j), G.Adj x y)
  obtain ⟨e, he⟩ := exists_label_embedding_in_finset S t hmany
  let ix (k : Fin t) := xBlockLabel t (e k)
  let iy (k : Fin t) := yBlockLabel t k
  let X (k : Fin t) := sampledBlock Z (3 * t) ℓ f (ix k)
  let Y (k : Fin t) := sampledBlock Z (3 * t) ℓ f (iy k)
  have hℓ : 0 < ℓ := by
    dsimp [ℓ]
    apply Nat.div_pos hn
    omega
  let a (k : Fin t) : V := (f (ix k, ⟨0, hℓ⟩)).1
  have ha (k : Fin t) : a k ∈ X k := by
    exact Finset.mem_image.mpr ⟨⟨0, hℓ⟩, Finset.mem_univ _, rfl⟩
  have hsub (k : Fin t) : X k ∪ Y k ⊆ Z := by
    exact Finset.union_subset
      (sampledBlock_subset Z (3 * t) ℓ f (ix k))
      (sampledBlock_subset Z (3 * t) ℓ f (iy k))
  have hix (k m : Fin t) (hkm : k ≠ m) : ix k ≠ ix m := by
    intro heq
    apply hkm
    apply e.injective
    apply Fin.ext
    simpa [ix, xBlockLabel] using congrArg Fin.val heq
  have hiy (k m : Fin t) (hkm : k ≠ m) : iy k ≠ iy m := by
    intro heq
    apply hkm
    apply Fin.ext
    have hh := congrArg Fin.val heq
    dsimp [iy, yBlockLabel] at hh
    omega
  have hxy (k m : Fin t) : ix k ≠ iy m :=
    xBlockLabel_ne_yBlockLabel t (e k) m
  have hdis : Pairwise (fun k m => Disjoint (X k ∪ Y k) (X m ∪ Y m)) := by
    intro k m hkm
    simp only [Finset.disjoint_union_left, Finset.disjoint_union_right]
    exact ⟨⟨sampledBlock_disjoint Z (3 * t) ℓ f (ix k) (ix m) (hix k m hkm),
      sampledBlock_disjoint Z (3 * t) ℓ f (iy k) (ix m) (hxy m k).symm⟩,
      ⟨sampledBlock_disjoint Z (3 * t) ℓ f (ix k) (iy m) (hxy k m),
        sampledBlock_disjoint Z (3 * t) ℓ f (iy k) (iy m) (hiy k m hkm)⟩⟩
  have hcross (k m : Fin t) (_ : k ≠ m) :
      ∃ x ∈ X k, ∃ y ∈ Y m, G.Adj x y := by
    have hs : e k ∈ S := he k
    exact (Finset.mem_filter.mp hs).2 m
  have hsize : 3 * t * ℓ ≤ Z.card := by
    rw [hZ]
    have hdiv : 9 * t * ℓ ≤ n := Nat.mul_div_le n (9 * t)
    have hh : 3 * (3 * t * ℓ) ≤ n := by nlinarith [hdiv]
    omega
  have hbudget : Fintype.card (nearCompleteDemands t X Y a) ≤ Z.card := by
    have hterm (k : Fin t) : ((X k ∪ Y k).erase (a k)).card ≤ 2 * ℓ := by
      have hh := Finset.card_union_le (X k) (Y k)
      have hX : (X k).card = ℓ := sampledBlock_card Z (3 * t) ℓ f (ix k)
      have hY : (Y k).card = ℓ := sampledBlock_card Z (3 * t) ℓ f (iy k)
      have he : ((X k ∪ Y k).erase (a k)).card ≤
          (X k ∪ Y k).card := Finset.card_erase_le
      omega
    have hsum : (∑ k : Fin t, ((X k ∪ Y k).erase (a k)).card) ≤
        t * (2 * ℓ) := by
      calc
        (∑ k : Fin t, ((X k ∪ Y k).erase (a k)).card) ≤
          ∑ _k : Fin t, 2 * ℓ := by
            apply Finset.sum_le_sum
            intro k _
            exact hterm k
        _ = t * (2 * ℓ) := by simp
    have hcard : Fintype.card (nearCompleteDemands t X Y a) =
        ∑ k : Fin t, ((X k ∪ Y k).erase (a k)).card := by
      let E : nearCompleteDemands t X Y a ≃
          (Σ k : Fin t, ↥((X k ∪ Y k).erase (a k))) := Equiv.refl _
      calc
        Fintype.card (nearCompleteDemands t X Y a) =
            Fintype.card (Σ k : Fin t,
              ↥((X k ∪ Y k).erase (a k))) := Fintype.card_congr E
        _ = ∑ k : Fin t, ((X k ∪ Y k).erase (a k)).card := by
          rw [Fintype.card_sigma]
          apply Finset.sum_congr rfl
          intro k _
          exact Fintype.card_coe _
    nlinarith [hsize]
  have hqnonneg : 0 ≤ ((edgeCount Gᶜ : ℝ) / (n.choose 2 : ℝ)) := by
    positivity
  have hℓNat : 1 ≤ ℓ := hℓ
  have hone := one_percent_of_near_complete_power_bound
    t ℓ (by omega : 1 ≤ t) hℓNat
    ((edgeCount Gᶜ : ℝ) / (n.choose 2 : ℝ)) hqnonneg hpower
  have hqint : 200 * edgeCount Gᶜ ≤ n * (n - 1) :=
    missing_edge_count_bound_of_fraction_one_percent G
      (by omega : 2 ≤ n) (by nlinarith)
  exact hasCliqueMinor_of_dense_blocks G t Z X Y a
    (by omega : 27 ≤ n) hqint hZ hgood ha hsub hdis
    hbudget hcross
/-- Appendix C's near-complete auxiliary lemma, with all integer rounding
made explicit. -/
theorem hasCliqueMinor_of_near_complete_power_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : ℕ) (ht : 3 ≤ t)
    (hn : 9 * t ≤ Fintype.card V)
    (hpower : 6 * (t : ℝ) *
      (100 * ((edgeCount Gᶜ : ℝ) /
        ((Fintype.card V).choose 2 : ℝ))) ^
          ((Fintype.card V / (9 * t)) ^ 2) ≤ 1) :
    HasCliqueMinor G t := by
  classical
  obtain ⟨Z, hZ, hgood⟩ := exists_low_missing_degree_reservoir G
  obtain ⟨f, hmany⟩ := exists_sample_with_many_crossing_blocks
    G t ht Z hn hZ hgood hpower
  exact hasCliqueMinor_of_successful_sample G t ht Z hn hZ hgood
    hpower f hmany
end HadwigerLean