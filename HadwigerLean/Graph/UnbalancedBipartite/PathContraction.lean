import HadwigerLean.Graph.MinorFree
import HadwigerLean.Graph.DensityBasic
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Contracting a two-edge path in a bipartite graph

The graph keeps the first endpoint, removes the center and second endpoint,
and transfers the second endpoint's incident edges to the first endpoint.
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The surviving vertices after contracting `u₁-v-u₂` onto `u₁`. -/
def twoNeighborContractionSet (v u₂ : V) : Set V :=
  {x | x ≠ v ∧ x ≠ u₂}

noncomputable instance twoNeighborContractionSet.fintype (v u₂ : V) :
    Fintype (twoNeighborContractionSet v u₂) := Fintype.ofFinite _

/-- The graph obtained by contracting the path `u₁-v-u₂` onto `u₁`. -/
def twoNeighborContractionGraph (G : SimpleGraph V) (v u₁ u₂ : V) :
    SimpleGraph (twoNeighborContractionSet v u₂) where
  Adj x y := x ≠ y ∧
    (G.Adj x.1 y.1 ∨
      (x.1 = u₁ ∧ G.Adj u₂ y.1) ∨
      (y.1 = u₁ ∧ G.Adj u₂ x.1))
  symm := by
    constructor
    intro x y h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h.1, h.2⟩)
    · exact Or.inr (Or.inl ⟨h.1, h.2⟩)
  loopless := by
    constructor
    intro x h
    exact h.1 rfl

private def twoNeighborContractionBranch (u₁ v u₂ : V)
    (x : twoNeighborContractionSet v u₂) : Set V :=
  {z | z = x.1 ∨ (x.1 = u₁ ∧ (z = v ∨ z = u₂))}

/-- The explicit connected-branch model of the two-edge path contraction. -/
noncomputable def twoNeighborContractionMinorModel
    (G : SimpleGraph V) (v u₁ u₂ : V)
    (h₁ : G.Adj v u₁) (h₂ : G.Adj v u₂) :
    MinorModel (twoNeighborContractionGraph G v u₁ u₂) G := by
  classical
  let B : twoNeighborContractionSet v u₂ → Set V :=
    twoNeighborContractionBranch u₁ v u₂
  have hcenter (x : twoNeighborContractionSet v u₂) : x.1 ∈ B x := Or.inl rfl
  have hconn (x : twoNeighborContractionSet v u₂) :
      (G.induce (B x)).Connected := by
    let J := G.induce (B x)
    haveI : Nonempty (B x) := ⟨⟨x.1, hcenter x⟩⟩
    have hreach (z : B x) : J.Reachable ⟨x.1, hcenter x⟩ z := by
      rcases z.2 with hz | ⟨hx, hz⟩
      · have heq : z = ⟨x.1, hcenter x⟩ := Subtype.ext hz
        rw [heq]
      · rcases hz with hzv | hzu
        · have hadj : G.Adj x.1 z.1 := by
            rw [hx, hzv]
            exact h₁.symm
          exact (show J.Adj ⟨x.1, hcenter x⟩ z from hadj).reachable
        · have hvB : v ∈ B x := Or.inr ⟨hx, Or.inl rfl⟩
          have hfirst : G.Adj x.1 v := by rw [hx]; exact h₁.symm
          have hsecond : G.Adj v z.1 := by rw [hzu]; exact h₂
          exact (show J.Adj ⟨x.1, hcenter x⟩ ⟨v, hvB⟩ from
            hfirst).reachable.trans
            (show J.Adj ⟨v, hvB⟩ z from hsecond).reachable
    refine (SimpleGraph.connected_iff J).mpr ⟨?_, inferInstance⟩
    intro p q
    exact (hreach p).symm.trans (hreach q)
  have hdis : Pairwise (fun x y : twoNeighborContractionSet v u₂ =>
      Disjoint (B x) (B y)) := by
    intro x y hxy
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    rcases hzx with hx | ⟨hxu, hxz⟩
    · rcases hzy with hy | ⟨_, hyz⟩
      · exact hxy (Subtype.ext (hx.symm.trans hy))
      · rcases hyz with hzv | hzu
        · exact x.property.1 (hx.symm.trans hzv)
        · exact x.property.2 (hx.symm.trans hzu)
    · rcases hzy with hy | ⟨hyu, _⟩
      · rcases hxz with hzv | hzu
        · exact y.property.1 (hy.symm.trans hzv)
        · exact y.property.2 (hy.symm.trans hzu)
      · exact hxy (Subtype.ext (hxu.trans hyu.symm))
  exact {
    branch := B
    connected := hconn
    disjoint := hdis
    adjacent := by
      intro x y hxy
      rcases hxy.2 with h | ⟨hxu, huy⟩ | ⟨hyu, hux⟩
      · exact ⟨x.1, Or.inl rfl, y.1, Or.inl rfl, h⟩
      · exact ⟨u₂, Or.inr ⟨hxu, Or.inr rfl⟩,
          y.1, Or.inl rfl, huy⟩
      · exact ⟨x.1, Or.inl rfl,
          u₂, Or.inr ⟨hyu, Or.inr rfl⟩, hux.symm⟩
  }

/-- The two-neighbor path contraction is a minor of the original graph. -/
theorem twoNeighborContraction_isMinor
    (G : SimpleGraph V) (v u₁ u₂ : V)
    (h₁ : G.Adj v u₁) (h₂ : G.Adj v u₂) :
    IsMinor (twoNeighborContractionGraph G v u₁ u₂) G :=
  ⟨twoNeighborContractionMinorModel G v u₁ u₂ h₁ h₂⟩


/-- Contracting a path with both endpoints in the right class preserves the
bipartition on the surviving vertices. -/
theorem twoNeighborContraction_isBipartiteWith
    (G : SimpleGraph V) (A B : Finset V)
    (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (v u₁ u₂ : V) (hu₁ : u₁ ∈ B) (hu₂ : u₂ ∈ B) :
    (twoNeighborContractionGraph G v u₁ u₂).IsBipartiteWith
      {x | x.1 ∈ A} {x | x.1 ∈ B} := by
  classical
  let H := twoNeighborContractionGraph G v u₁ u₂
  refine ⟨?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro x hxA hxB
    exact (Set.disjoint_left.mp hG.disjoint) hxA hxB
  · intro x y hxy
    rcases hxy.2 with h | ⟨hxu, huy⟩ | ⟨hyu, hux⟩
    · exact hG.mem_of_adj h
    · have hyA : y.1 ∈ A :=
        hG.mem_of_mem_adj' hu₂ huy.symm
      have hxB : x.1 ∈ B := hxu.symm ▸ hu₁
      exact Or.inr ⟨hxB, hyA⟩
    · have hxA : x.1 ∈ A :=
        hG.mem_of_mem_adj' hu₂ hux.symm
      have hyB : y.1 ∈ B := hyu.symm ▸ hu₁
      exact Or.inl ⟨hxA, hyB⟩

/-- Replace a deleted vertex in a finite neighbor set by its contraction mate. -/
def replaceFinset (S : Finset V) (u₁ u₂ : V) : Finset V :=
  S.erase u₂ ∪ if u₂ ∈ S then {u₁} else ∅

/-- A replacement reduces cardinality exactly when both vertices were
already present in the original set. -/
theorem replaceFinset_card_add_common
    (S : Finset V) (u₁ u₂ : V) (hneq : u₁ ≠ u₂) :
    (replaceFinset S u₁ u₂).card +
      (if u₁ ∈ S ∧ u₂ ∈ S then 1 else 0) = S.card := by
  classical
  by_cases h₂ : u₂ ∈ S
  · by_cases h₁ : u₁ ∈ S
    · have hmem : u₁ ∈ S.erase u₂ := Finset.mem_erase.mpr ⟨hneq, h₁⟩
      simp [replaceFinset, h₁, h₂, hmem, Finset.card_erase_of_mem]
      have hpos : 0 < S.card := Finset.card_pos.mpr ⟨u₂, h₂⟩
      omega
    · have hnot : u₁ ∉ S.erase u₂ := by simp [h₁]
      simp [replaceFinset, h₁, h₂, hnot, Finset.card_erase_of_mem]
      have hpos : 0 < S.card := Finset.card_pos.mpr ⟨u₂, h₂⟩
      omega
  · simp [replaceFinset, h₂]

/-- On the left side, the contracted neighborhood is obtained by replacing
`u₂` with `u₁` in the original neighborhood. -/
theorem twoNeighborContraction_neighborFinset_left
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V)
    (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (v u₁ u₂ : V) [DecidableRel (twoNeighborContractionGraph G v u₁ u₂).Adj]
    (hv : v ∈ A) (hu₁ : u₁ ∈ B)
    (hneq : u₁ ≠ u₂)
    (y : twoNeighborContractionSet v u₂) (hy : y.1 ∈ A) :
    ((twoNeighborContractionGraph G v u₁ u₂).neighborFinset y).map
      (.subtype (· ∈ twoNeighborContractionSet v u₂)) =
    replaceFinset (G.neighborFinset y.1) u₁ u₂ := by
  classical
  let H := twoNeighborContractionGraph G v u₁ u₂
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
    have hwy : H.Adj y w := (H.mem_neighborFinset y w).mp hw
    rcases hwy.2 with h | ⟨hyu, h⟩ | ⟨hwu, h⟩
    · have hne : w.1 ≠ u₂ := w.property.2
      exact Finset.mem_union_left _ (Finset.mem_erase.mpr
        ⟨hne, (G.mem_neighborFinset _ _).mpr h⟩)
    · have hyB : y.1 ∈ B := hyu.symm ▸ hu₁
      exact ((Set.disjoint_left.mp hG.disjoint) hy hyB).elim
    · have hu₂mem : u₂ ∈ G.neighborFinset y.1 :=
        (G.mem_neighborFinset _ _).mpr h.symm
      simpa [replaceFinset, hu₂mem, hwu]
  · intro hz
    have hmem : z ∈ G.neighborFinset y.1 ∧ z ≠ u₂ ∨
        u₂ ∈ G.neighborFinset y.1 ∧ z = u₁ := by
      by_cases h₂ : u₂ ∈ G.neighborFinset y.1
      · simpa [replaceFinset, h₂, Finset.mem_erase, and_comm,
          and_left_comm, or_comm] using hz
      · have hGyz : G.Adj y.1 z := by
          simpa [replaceFinset, h₂] using hz
        have hzu : z ≠ u₂ := by
          intro heq
          subst z
          exact h₂ ((G.mem_neighborFinset _ _).mpr hGyz)
        exact Or.inl ⟨(G.mem_neighborFinset _ _).mpr hGyz, hzu⟩
    rcases hmem with ⟨hGyz, hzu⟩ | ⟨hGyu₂, hzu⟩
    · have hadj : G.Adj y.1 z := (G.mem_neighborFinset _ _).mp hGyz
      have hzB : z ∈ B := hG.mem_of_mem_adj hy hadj
      have hzv : z ≠ v := by
        intro heq
        exact (Set.disjoint_left.mp hG.disjoint) hv (heq ▸ hzB)
      let w : twoNeighborContractionSet v u₂ := ⟨z, hzv, hzu⟩
      have hyw : y ≠ w := by
        intro heq
        have heqval : y.1 = z := congrArg Subtype.val heq
        exact (Set.disjoint_left.mp hG.disjoint) hy (heqval.symm ▸ hzB)
      apply Finset.mem_map.mpr
      refine ⟨w, ?_, rfl⟩
      exact (H.mem_neighborFinset y w).mpr ⟨hyw, Or.inl hadj⟩
    · subst z
      have hu₁v : u₁ ≠ v := by
        intro heq
        exact (Set.disjoint_left.mp hG.disjoint) hv (heq ▸ hu₁)
      let w : twoNeighborContractionSet v u₂ := ⟨u₁, hu₁v, hneq⟩
      have hyw : y ≠ w := by
        intro heq
        have hyB : y.1 ∈ B := by
          have heq' : y.1 = u₁ := congrArg Subtype.val heq
          exact heq' ▸ hu₁
        exact (Set.disjoint_left.mp hG.disjoint) hy hyB
      apply Finset.mem_map.mpr
      refine ⟨w, ?_, rfl⟩
      have hadj : G.Adj u₂ y.1 :=
        ((G.mem_neighborFinset _ _).mp hGyu₂).symm
      exact (H.mem_neighborFinset y w).mpr
        ⟨hyw, Or.inr (Or.inr ⟨rfl, hadj⟩)⟩

/-- Every left-side degree loses one precisely at common neighbors of the
two contracted right-side endpoints. -/
theorem twoNeighborContraction_degree_left_add_common
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V)
    (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (v u₁ u₂ : V) [DecidableRel (twoNeighborContractionGraph G v u₁ u₂).Adj]
    (hv : v ∈ A) (hu₁ : u₁ ∈ B) (hneq : u₁ ≠ u₂)
    (y : twoNeighborContractionSet v u₂) (hy : y.1 ∈ A) :
    (twoNeighborContractionGraph G v u₁ u₂).degree y +
      (if G.Adj y.1 u₁ ∧ G.Adj y.1 u₂ then 1 else 0) = G.degree y.1 := by
  classical
  let H := twoNeighborContractionGraph G v u₁ u₂
  have hmap := twoNeighborContraction_neighborFinset_left
    G A B hG v u₁ u₂ hv hu₁ hneq y hy
  have hcard : H.degree y =
      (replaceFinset (G.neighborFinset y.1) u₁ u₂).card := by
    rw [← H.card_neighborFinset_eq_degree y,
      ← Finset.card_map (.subtype (· ∈ twoNeighborContractionSet v u₂))]
    exact congrArg Finset.card hmap
  rw [hcard, ← G.card_neighborFinset_eq_degree y.1]
  simpa only [G.mem_neighborFinset] using
    replaceFinset_card_add_common (G.neighborFinset y.1) u₁ u₂ hneq

/-- Summation over the surviving left class agrees with deleting its center. -/
theorem sum_twoNeighborContraction_left
    (A B : Finset V) (hAB : Disjoint A B)
    (v u₂ : V) (hu₂ : u₂ ∈ B)
    (f : V → ℕ) :
    (∑ y ∈ (Finset.univ.filter (fun y : twoNeighborContractionSet v u₂ =>
      y.1 ∈ A)), f y.1) = ∑ y ∈ A.erase v, f y := by
  classical
  apply Finset.sum_bij (fun y _ => y.1)
  · intro y hy
    have hyA : y.1 ∈ A := (Finset.mem_filter.mp hy).2
    exact Finset.mem_erase.mpr ⟨y.property.1, hyA⟩
  · intro y₁ _ y₂ _ heq
    exact Subtype.ext heq
  · intro z hz
    have hzA : z ∈ A := (Finset.mem_erase.mp hz).2
    have hzv : z ≠ v := (Finset.mem_erase.mp hz).1
    have hzu₂ : z ≠ u₂ := by
      intro heq
      exact (Finset.disjoint_left.mp hAB) hzA (heq ▸ hu₂)
    refine ⟨⟨z, hzv, hzu₂⟩, ?_, rfl⟩
    simp [hzA]
  · intro y _
    rfl

/-- The two-edge path contraction loses the center's degree plus one edge
at every other common neighbor of its endpoints. -/
theorem twoNeighborContraction_edgeCount_add_loss
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V)
    (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (v u₁ u₂ : V) [DecidableRel (twoNeighborContractionGraph G v u₁ u₂).Adj]
    (hv : v ∈ A) (hu₁ : u₁ ∈ B) (hu₂ : u₂ ∈ B)
    (hneq : u₁ ≠ u₂) :
    edgeCount (twoNeighborContractionGraph G v u₁ u₂) +
      ((A.erase v).filter (fun y => G.Adj y u₁ ∧ G.Adj y u₂)).card +
      G.degree v = edgeCount G := by
  classical
  let S := twoNeighborContractionSet v u₂
  let H := twoNeighborContractionGraph G v u₁ u₂
  let L : Finset S := Finset.univ.filter (fun y => y.1 ∈ A)
  let R : Finset S := Finset.univ.filter (fun y => y.1 ∈ B)
  have hfinAB : Disjoint A B := by
    simpa only [Finset.disjoint_coe] using hG.disjoint
  have hHB : H.IsBipartiteWith (L : Set S) (R : Set S) := by
    simpa [L, R] using
      twoNeighborContraction_isBipartiteWith G A B hG v u₁ u₂ hu₁ hu₂
  have hsumH : edgeCount H = ∑ y ∈ L, H.degree y := by
    simpa only [edgeCount_eq_card_edgeFinset] using
      (H.isBipartiteWith_sum_degrees_eq_card_edges
        (s := L) (t := R) hHB).symm
  have hsumG : edgeCount G = ∑ y ∈ A, G.degree y := by
    simpa only [edgeCount_eq_card_edgeFinset] using
      (G.isBipartiteWith_sum_degrees_eq_card_edges
        (s := A) (t := B) hG).symm
  have hlocal : (∑ y ∈ L, H.degree y) +
      (∑ y ∈ L, if G.Adj y.1 u₁ ∧ G.Adj y.1 u₂ then 1 else 0) =
      ∑ y ∈ L, G.degree y.1 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    exact twoNeighborContraction_degree_left_add_common
      G A B hG v u₁ u₂ hv hu₁ hneq y (Finset.mem_filter.mp hy).2
  have hdegreeSum : (∑ y ∈ L, G.degree y.1) =
      ∑ y ∈ A.erase v, G.degree y :=
    sum_twoNeighborContraction_left A B hfinAB v u₂ hu₂ (fun y => G.degree y)
  have hcommonSum :
      (∑ y ∈ L, if G.Adj y.1 u₁ ∧ G.Adj y.1 u₂ then 1 else 0) =
      ((A.erase v).filter (fun y => G.Adj y u₁ ∧ G.Adj y u₂)).card := by
    rw [sum_twoNeighborContraction_left A B hfinAB v u₂ hu₂
      (fun y => if G.Adj y u₁ ∧ G.Adj y u₂ then 1 else 0)]
    exact Finset.sum_boole _ _
  have herase : (∑ y ∈ A.erase v, G.degree y) + G.degree v =
      ∑ y ∈ A, G.degree y := by
    exact Finset.sum_erase_add A _ hv
  rw [hsumH, hsumG]
  omega

/-- The common-neighbor loss can be expressed as the intersection of the
two endpoint neighborhoods, with the center removed. -/
theorem common_left_filter_eq_neighbor_inter_erase
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V)
    (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (v u₁ u₂ : V) (hu₁ : u₁ ∈ B) :
    (A.erase v).filter (fun y => G.Adj y u₁ ∧ G.Adj y u₂) =
      (G.neighborFinset u₁ ∩ G.neighborFinset u₂).erase v := by
  classical
  ext y
  constructor
  · intro hy
    have hyerase := (Finset.mem_filter.mp hy).1
    have hadj := (Finset.mem_filter.mp hy).2
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hyerase).1,
      Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset _ _).mpr hadj.1.symm,
        (G.mem_neighborFinset _ _).mpr hadj.2.symm⟩⟩
  · intro hy
    have hyneq := (Finset.mem_erase.mp hy).1
    have hyinter := Finset.mem_inter.mp (Finset.mem_erase.mp hy).2
    have hu₁y : G.Adj u₁ y := (G.mem_neighborFinset _ _).mp hyinter.1
    have hu₂y : G.Adj u₂ y := (G.mem_neighborFinset _ _).mp hyinter.2
    have hyA : y ∈ A := hG.symm.mem_of_mem_adj hu₁ hu₁y
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨hyneq, hyA⟩, hu₁y.symm, hu₂y.symm⟩

/-- Exact edge loss in the form used in Appendix C. -/
theorem twoNeighborContraction_edgeCount_add_degree_add_common
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V)
    (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (v u₁ u₂ : V) [DecidableRel (twoNeighborContractionGraph G v u₁ u₂).Adj]
    (hv : v ∈ A) (hu₁ : u₁ ∈ B) (hu₂ : u₂ ∈ B)
    (hneq : u₁ ≠ u₂) :
    edgeCount (twoNeighborContractionGraph G v u₁ u₂) + G.degree v +
      ((G.neighborFinset u₁ ∩ G.neighborFinset u₂).erase v).card =
      edgeCount G := by
  have h := twoNeighborContraction_edgeCount_add_loss G A B hG
    v u₁ u₂ hv hu₁ hu₂ hneq
  rw [common_left_filter_eq_neighbor_inter_erase G A B hG v u₁ u₂ hu₁] at h
  omega

/-- Summation over the surviving right class agrees with deleting the
second path endpoint. -/
theorem sum_twoNeighborContraction_right
    (A B : Finset V) (hAB : Disjoint A B)
    (v u₂ : V) (hv : v ∈ A)
    (f : V → ℕ) :
    (∑ y ∈ (Finset.univ.filter (fun y : twoNeighborContractionSet v u₂ =>
      y.1 ∈ B)), f y.1) = ∑ y ∈ B.erase u₂, f y := by
  classical
  apply Finset.sum_bij (fun y _ => y.1)
  · intro y hy
    have hyB : y.1 ∈ B := (Finset.mem_filter.mp hy).2
    exact Finset.mem_erase.mpr ⟨y.property.2, hyB⟩
  · intro y₁ _ y₂ _ heq
    exact Subtype.ext heq
  · intro z hz
    have hzB : z ∈ B := (Finset.mem_erase.mp hz).2
    have hzu₂ : z ≠ u₂ := (Finset.mem_erase.mp hz).1
    have hzv : z ≠ v := by
      intro heq
      exact (Finset.disjoint_left.mp hAB) hv (heq ▸ hzB)
    refine ⟨⟨z, hzv, hzu₂⟩, ?_, rfl⟩
    simp [hzB]
  · intro y _
    rfl

/-- The contraction deletes one vertex from each bipartition class. -/
theorem twoNeighborContraction_class_card
    (A B : Finset V) (hAB : Disjoint A B)
    (v u₂ : V) (hv : v ∈ A) (hu₂ : u₂ ∈ B) :
    let S := twoNeighborContractionSet v u₂
    let L : Finset S := Finset.univ.filter (fun y => y.1 ∈ A)
    let R : Finset S := Finset.univ.filter (fun y => y.1 ∈ B)
    L.card + 1 = A.card ∧ R.card + 1 = B.card := by
  classical
  dsimp
  constructor
  · have h := sum_twoNeighborContraction_left A B hAB v u₂ hu₂
      (fun _ => 1)
    simp only [Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul,
      mul_one] at h
    rw [Finset.card_erase_of_mem hv] at h
    have hpos : 0 < A.card := Finset.card_pos.mpr ⟨v, hv⟩
    have hnat : (Finset.univ.filter (fun y : twoNeighborContractionSet v u₂ =>
      y.1 ∈ A)).card = A.card - 1 := by exact_mod_cast h
    omega
  · have h := sum_twoNeighborContraction_right A B hAB v u₂ hv
      (fun _ => 1)
    simp only [Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul,
      mul_one] at h
    rw [Finset.card_erase_of_mem hu₂] at h
    have hpos : 0 < B.card := Finset.card_pos.mpr ⟨u₂, hu₂⟩
    have hnat : (Finset.univ.filter (fun y : twoNeighborContractionSet v u₂ =>
      y.1 ∈ B)).card = B.card - 1 := by exact_mod_cast h
    omega
end HadwigerLean