import HadwigerLean.Graph.RootedDensity.Universal
import HadwigerLean.Graph.Linkedness.Massed
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Small-root massed pairs

For two roots, the F.2 shore bounds force the roots into one connected
component. This file also constructs the rooted model of a two-vertex
target from a path between its roots.
-/

namespace HadwigerLean.RootedDensity

universe u v

private theorem edgeIncidenceCount_union_of_no_cross
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W : Finset V) (hUW : Disjoint U W)
    (hcross : ∀ u ∈ U, ∀ w ∈ W, ¬ G.Adj u w) :
    edgeIncidenceSetCount G ((U ∪ W : Finset V) : Set V) =
      edgeIncidenceSetCount G (U : Set V) +
      edgeIncidenceSetCount G (W : Set V) := by
  classical
  have hdisj : Disjoint (edgeIncidenceSet G (U : Set V))
      (edgeIncidenceSet G (W : Set V)) := by
    apply Set.disjoint_left.mpr
    intro e heU heW
    obtain ⟨u, hu, hue⟩ := heU
    obtain ⟨w, hw, hwe⟩ := heW
    have hne : u ≠ w := by
      intro heq
      subst w
      exact (Finset.disjoint_left.mp hUW) hu hw
    have heq : (e.1 : Sym2 V) = s(u,w) :=
      (Sym2.mem_and_mem_iff hne).mp ⟨hue,hwe⟩
    have hadj : G.Adj u w := by
      have hs : s(u,w) ∈ G.edgeSet := heq ▸ e.2
      simpa using hs
    exact hcross u hu w hw hadj
  have heq : edgeIncidenceSet G ((U ∪ W : Finset V) : Set V) =
      edgeIncidenceSet G (U : Set V) ∪
        edgeIncidenceSet G (W : Set V) := by
    ext e
    simp only [edgeIncidenceSet, Set.mem_setOf_eq, Set.mem_union,
      Finset.coe_union]
    constructor
    · rintro ⟨x, hx, hxe⟩
      rcases hx with hu | hw
      · exact Or.inl ⟨x, hu, hxe⟩
      · exact Or.inr ⟨x, hw, hxe⟩
    · rintro (⟨x,hx,hxe⟩ | ⟨x,hx,hxe⟩)
      · exact ⟨x,Or.inl hx,hxe⟩
      · exact ⟨x,Or.inr hx,hxe⟩
  unfold edgeIncidenceSetCount
  rw [heq]
  simpa only [Nat.card_coe_set_eq] using Set.ncard_union_eq hdisj


/-- The two roots of a massed pair lie in one connected component. -/
theorem reachable_two_roots_of_massed
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V) (hxy : x ≠ y) (α : ℝ)
    (hm : MassedPair G ({x,y} : Finset V) α) :
    G.Reachable x y := by
  classical
  by_contra hnot
  let C : Finset V := Finset.univ.filter (fun z => G.Reachable x z)
  have hxC : x ∈ C := by simp [C]
  have hyC : y ∉ C := by simpa [C] using hnot
  have hclosed : ∀ u ∈ C, ∀ v, G.Adj u v → v ∈ C := by
    intro u hu v huv
    have hxu : G.Reachable x u := by simpa [C] using hu
    have hxv : G.Reachable x v := hxu.trans huv.reachable
    simpa [C] using hxv
  let Sx : VertexSeparation G := {
    left := (C : Set V)ᶜ ∪ {x}
    right := (C : Set V)
    cover := by
      ext v
      simp only [Set.mem_union, Set.mem_compl_iff, Finset.mem_coe,
        Set.mem_singleton_iff, Set.mem_univ, iff_true]
      by_cases hv : v ∈ C <;> simp [hv]
    no_cross := by
      intro u v huL huNotR hvR hvNotL huv
      exact huNotR (hclosed v hvR u huv.symm)
  }
  let Sy : VertexSeparation G := {
    left := (C : Set V) ∪ {y}
    right := (C : Set V)ᶜ
    cover := by
      ext v
      simp only [Set.mem_union, Set.mem_compl_iff, Finset.mem_coe,
        Set.mem_singleton_iff, Set.mem_univ, iff_true]
      by_cases hv : v ∈ C <;> simp [hv]
    no_cross := by
      intro u v huL huNotR hvR hvNotL huv
      exact hvR (hclosed u (by simpa using huNotR) v huv)
  }
  let U : Finset V := C.erase x
  let W : Finset V := Cᶜ.erase y
  have hSxroot : (({x,y} : Finset V) : Set V) ⊆ Sx.left := by
    intro v hv
    simp only [Finset.coe_pair, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (by simpa using hyC)
  have hSyroot : (({x,y} : Finset V) : Set V) ⊆ Sy.left := by
    intro v hv
    simp only [Finset.coe_pair, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact Or.inl hxC
    · exact Or.inr rfl
  have hSxsep : Sx.separator = ({x} : Set V) := by
    ext v
    by_cases hv : v = x
    · subst v
      simp [Sx, VertexSeparation.separator, hxC]
    · simp [Sx, VertexSeparation.separator, hv]
  have hSysep : Sy.separator = ({y} : Set V) := by
    ext v
    by_cases hv : v = y
    · subst v
      simp [Sy, VertexSeparation.separator, hyC]
    · simp [Sy, VertexSeparation.separator, hv]
  have hrootcard : Nat.card (({x,y} : Finset V) : Set V) = 2 := by
    simp [Finset.card_pair hxy]
  have hSxsmall : Nat.card Sx.separator <
      Nat.card (({x,y} : Finset V) : Set V) := by
    rw [hSxsep,hrootcard]
    simp
  have hSysmall : Nat.card Sy.separator <
      Nat.card (({x,y} : Finset V) : Set V) := by
    rw [hSysep,hrootcard]
    simp
  have hSxfar : Sx.strictRight = (U : Set V) := by
    ext v
    simp [Sx, VertexSeparation.strictRight, U]
    tauto
  have hSyfar : Sy.strictRight = (W : Set V) := by
    ext v
    simp [Sy, VertexSeparation.strictRight, W]
    tauto
  have hdisj : Disjoint U W := by
    apply Finset.disjoint_left.mpr
    intro u hu hw
    have huc : u ∈ C := (Finset.mem_erase.mp hu).2
    have hunc : u ∉ C := by simpa [W] using (Finset.mem_erase.mp hw).2
    exact hunc huc
  have hcross : ∀ u ∈ U, ∀ w ∈ W, ¬ G.Adj u w := by
    intro u hu w hw huw
    have huC : u ∈ C := (Finset.mem_erase.mp hu).2
    have hwNotC : w ∉ C := by simpa [W] using (Finset.mem_erase.mp hw).2
    exact hwNotC (hclosed u huC w huw)
  have hcover : U ∪ W = ({x,y} : Finset V)ᶜ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_compl,
      Finset.mem_insert, Finset.mem_singleton]
    by_cases hvC : v ∈ C
    · have hvy : v ≠ y := by
        intro heq
        subst v
        exact hyC hvC
      simp [U,W,hvC,hvy]
    · have hvx : v ≠ x := by
        intro heq
        subst v
        exact hvC hxC
      simp [U,W,hvC,hvx]
  have hcount : edgeIncidenceSetCount G (({x,y} : Finset V)ᶜ : Set V) =
      edgeIncidenceSetCount G (U : Set V) +
        edgeIncidenceSetCount G (W : Set V) := by
    rw [← Finset.coe_compl, ← hcover]
    exact edgeIncidenceCount_union_of_no_cross G U W hdisj hcross
  have hcard : (({x,y} : Finset V)ᶜ).card = U.card + W.card := by
    rw [← hcover, Finset.card_union_of_disjoint hdisj]
  have hshorex := hm.shore Sx hSxroot hSxsmall
  have hshorey := hm.shore Sy hSyroot hSysmall
  rw [hSxfar] at hshorex
  rw [hSyfar] at hshorey
  have hglobal := hm.global
  have houtside : Nat.card
      {v : V // v ∉ (({x,y} : Finset V) : Set V)} =
        (({x,y} : Finset V)ᶜ).card := by
    rw [Nat.card_eq_fintype_card]
    apply Fintype.card_of_finset'
      (p := {v : V | v ∉ (({x,y} : Finset V) : Set V)})
      (({x,y} : Finset V)ᶜ)
    intro v
    simp
  rw [houtside] at hglobal
  have hcountR : (edgeIncidenceSetCount G
      (({x,y} : Finset V)ᶜ : Set V) : ℝ) =
      (edgeIncidenceSetCount G (U : Set V) : ℝ) +
        (edgeIncidenceSetCount G (W : Set V) : ℝ) := by
    exact_mod_cast hcount
  have hcardR : ((({x,y} : Finset V)ᶜ).card : ℝ) =
      (U.card : ℝ) + (W.card : ℝ) := by
    exact_mod_cast hcard
  have hUcard : Nat.card (U : Set V) = U.card := by simp
  have hWcard : Nat.card (W : Set V) = W.card := by simp
  rw [hUcard] at hshorex
  rw [hWcard] at hshorey
  change α * ((({x,y} : Finset V)ᶜ).card : ℝ) <
      (edgeIncidenceSetCount G
        (({x,y} : Finset V)ᶜ : Set V) : ℝ) at hglobal
  rw [hcardR, hcountR] at hglobal
  nlinarith


/-- A path between distinct vertices gives a rooted model of every
two-label target whose root map takes values in those vertices. -/
theorem rooted_minor_of_two_reachable
    {V : Type u} {T : Type v}
    (G : SimpleGraph V) (H : SimpleGraph T)
    (x y : V) (hxy : x ≠ y) (hreach : G.Reachable x y)
    (root : T → V) (hroot : ∀ i, root i = x ∨ root i = y)
    (hinj : Function.Injective root) :
    Nonempty (RootedMinorModel H G root) := by
  classical
  obtain ⟨p, hp, _⟩ := hreach.exists_path_of_dist
  have hnn : ¬ p.Nil := by
    intro hn
    exact hxy hn.eq
  let A : Set V := {v | v ∈ p.dropLast.support}
  have hAconn : (G.induce A).Connected := by
    exact p.dropLast.connected_induce_support
  have hyNotA : y ∉ A := by
    dsimp [A]
    have hsupport : p.dropLast.support ++ [y] = p.support :=
      p.support_dropLast_concat hnn
    have hnodup : (p.dropLast.support ++ [y]).Nodup := by
      rw [hsupport]
      exact hp.support_nodup
    grind
  have hAroot : x ∈ A := p.dropLast.start_mem_support
  have hApen : p.penultimate ∈ A := p.dropLast.end_mem_support
  have hpAdj : G.Adj p.penultimate y := p.adj_penultimate hnn
  have hdisj : Disjoint A ({y} : Set V) := by
    apply Set.disjoint_left.mpr
    intro z hz hzy
    have heq : z = y := by simpa using hzy
    subst z
    exact hyNotA hz
  let branch : T → Set V := fun i =>
    if root i = x then A else {y}
  refine ⟨{
    toMinorModel := {
      branch := branch
      connected := ?_
      disjoint := ?_
      adjacent := ?_
    }
    root_mem := ?_
  }⟩
  · intro i
    by_cases hi : root i = x
    · change (G.induce (if root i = x then A else {y})).Connected
      rw [if_pos hi]
      exact hAconn
    · change (G.induce (if root i = x then A else {y})).Connected
      rw [if_neg hi]
      simp
  · intro i j hij
    have hrij : root i ≠ root j := hinj.ne hij
    rcases hroot i with hix | hiy
    · rcases hroot j with hjx | hjy
      · exact False.elim (hrij (hix.trans hjx.symm))
      · simpa [branch, hix, hjy, hxy.symm] using hdisj
    · rcases hroot j with hjx | hjy
      · have hiNot : root i ≠ x := hiy ▸ hxy.symm
        simpa [branch, hiNot, hjx] using hdisj.symm
      · exact False.elim (hrij (hiy.trans hjy.symm))
  · intro i j hij
    have hne : i ≠ j := H.ne_of_adj hij
    have hrij : root i ≠ root j := hinj.ne hne
    rcases hroot i with hix | hiy
    · have hjy : root j = y := (hroot j).resolve_left
        (fun hjx => hrij (hix.trans hjx.symm))
      refine ⟨p.penultimate, ?_, y, ?_, hpAdj⟩
      · simpa [branch, hix] using hApen
      · simp [branch, hjy, hxy.symm]
    · have hjx : root j = x := (hroot j).resolve_right
        (fun hjy => hrij (hiy.trans hjy.symm))
      refine ⟨y, ?_, p.penultimate, ?_, hpAdj.symm⟩
      · have hiNot : root i ≠ x := hiy ▸ hxy.symm
        simp [branch, hiNot]
      · simpa [branch, hjx] using hApen
  · intro i
    rcases hroot i with hi | hi
    · simpa [branch, hi] using hAroot
    · have hiNot : root i ≠ x := hi ▸ hxy.symm
      simpa [branch, hiNot] using hi


/-- Every massed pair with at most two prescribed roots is universal for
any finite target: the two-root edge case follows from reachability. -/
theorem universalAt_of_massed_card_le_two
    {V : Type u} {W : Type v} [Fintype V] [DecidableEq V]
    [Fintype W] (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) (X : Finset V) (α : ℝ)
    (hm : MassedPair G (X : Set V) α)
    (hX : X.card ≤ 2) :
    UniversalAt G H X := by
  classical
  by_cases hsmall : X.card ≤ 1
  · exact UniversalAt.of_card_le_one G H X hsmall
  have htwo : X.card = 2 := by omega
  obtain ⟨x,y,hxy,hXpair⟩ := Finset.card_eq_two.mp htwo
  subst X
  have hreach : G.Reachable x y :=
    reachable_two_roots_of_massed G x y hxy α hm
  intro Y root hinj hrange
  have hroot : ∀ i : ↥(Y : Set W), root i = x ∨ root i = y := by
    intro i
    have hi : root i ∈ Set.range root := ⟨i,rfl⟩
    rw [hrange] at hi
    simpa using hi
  exact rooted_minor_of_two_reachable G (H.induce (Y : Set W))
    x y hxy hreach root hroot hinj

end HadwigerLean.RootedDensity
