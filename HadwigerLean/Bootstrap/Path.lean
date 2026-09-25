import HadwigerLean.Bootstrap.Definitions
import Mathlib.Combinatorics.SimpleGraph.Ends.Defs
import Mathlib.Tactic

/-!
# Local combinatorial bounds for induced-path localization

The star argument controls stable sets inside a closed neighborhood when
large connected bipartite induced subgraphs are excluded.
-/

namespace HadwigerLean.Bootstrap

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A vertex joined to every vertex of a stable set induces a connected
bipartite star. -/
private theorem induced_star_connected_bipartite (G : SimpleGraph V)
    (v : V) (S : Finset V) (hstable : G.IsIndepSet (S : Set V))
    (hadj : ∀ w ∈ S, G.Adj v w) :
    (G.induce (insert v (S : Set V))).Connected ∧
      (G.induce (insert v (S : Set V))).IsBipartite := by
  classical
  constructor
  · apply (G.induce (insert v (S : Set V))).connected_iff_exists_forall_reachable.mpr
    refine ⟨⟨v, by simp⟩, ?_⟩
    rintro ⟨w, hw⟩
    by_cases hwv : w = v
    · subst w
      exact SimpleGraph.Reachable.refl _
    · have hws : w ∈ S := by simpa [hwv] using hw
      have ha : (G.induce (insert v (S : Set V))).Adj
          ⟨v, by simp⟩ ⟨w, hw⟩ := hadj w hws
      exact ha.reachable
  · refine ⟨SimpleGraph.Coloring.mk
      (fun x => if x.1 = v then (0 : Fin 2) else 1) ?_⟩
    intro x y hxy
    have hxy' : G.Adj x.1 y.1 := hxy
    by_cases hx : x.1 = v
    · have hy : y.1 ≠ v := by
        intro hy
        exact (G.ne_of_adj hxy') (hx.trans hy.symm)
      simp [hx, hy]
    · have hxs : x.1 ∈ S := (Set.mem_insert_iff.mp x.2).resolve_left hx
      by_cases hy : y.1 = v
      · simp [hx, hy]
      · have hys : y.1 ∈ S := (Set.mem_insert_iff.mp y.2).resolve_left hy
        exact False.elim (hstable hxs hys (G.ne_of_adj hxy') hxy')

/-- A stable set of neighbors cannot have `k` vertices when no connected
bipartite induced graph has `k+1` vertices. -/
theorem stable_neighbors_card_lt (G : SimpleGraph V) (k : ℕ)
    (hno : NoLargeConnectedBipartite G (k + 1))
    (v : V) (S : Finset V) (hstable : G.IsIndepSet (S : Set V))
    (hadj : ∀ w ∈ S, G.Adj v w) : S.card < k := by
  classical
  by_contra hlt
  have hk : k ≤ S.card := Nat.le_of_not_gt hlt
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hk
  have hTv : v ∉ T := by
    intro hv
    exact (G.ne_of_adj (hadj v (hTS hv))) rfl
  have hcard : (insert v T).card = k + 1 := by
    rw [Finset.card_insert_of_notMem hTv, hTcard]
  have hTstable : G.IsIndepSet (T : Set V) := by
    intro x hx y hy hxy
    exact hstable (hTS hx) (hTS hy) hxy
  have hTadj : ∀ w ∈ T, G.Adj v w :=
    fun w hw => hadj w (hTS hw)
  have hset : ((insert v T : Finset V) : Set V) = insert v (T : Set V) := by
    ext w
    simp
  apply hno (insert v T) hcard
  rw [hset]
  exact induced_star_connected_bipartite G v T hTstable hTadj

/-- The closed neighborhood of one vertex has independence number at most
one less than the first excluded connected bipartite induced order. -/
theorem independence_closedNeighborhood_le (G : SimpleGraph V) (k : ℕ)
    (hk : 2 ≤ k) (hno : NoLargeConnectedBipartite G k) (v : V) :
    HadwigerLean.independenceNumber
      (G.induce (insert v (G.neighborSet v))) ≤ k - 1 := by
  classical
  let U : Set V := insert v (G.neighborSet v)
  obtain ⟨S, hS, hScard⟩ :=
    HadwigerLean.exists_stable_card_eq_independenceNumber (G.induce U)
  let T : Finset V := S.map ⟨Subtype.val, Subtype.val_injective⟩
  have hTcard : T.card = S.card := by simp [T]
  have hTU : (T : Set V) ⊆ U := by
    intro w hw
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hw
    exact a.property
  have hTstable : G.IsIndepSet (T : Set V) := by
    intro x hx y hy hxy hadj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact hS ha hb (by intro hab; exact hxy (congrArg Subtype.val hab)) hadj
  have hcard : T.card =
      HadwigerLean.independenceNumber (G.induce U) := by
    rw [hTcard, hScard]
  change HadwigerLean.independenceNumber (G.induce U) ≤ k - 1
  rw [← hcard]
  by_cases hv : v ∈ T
  · have hsub : T ⊆ {v} := by
      intro w hw
      by_contra hne
      have hne' : v ≠ w := by
        intro hvw
        apply hne
        simp [hvw]
      have hadj : G.Adj v w := by
        rcases Set.mem_insert_iff.mp (hTU hw) with hwv | hwN
        · exact False.elim (hne (by simp [hwv]))
        · exact hwN
      exact hTstable hv hw hne' hadj
    have hle : T.card ≤ 1 := by
      calc
        T.card ≤ ({v} : Finset V).card := Finset.card_le_card hsub
        _ = 1 := by simp
    omega
  · have hadj : ∀ w ∈ T, G.Adj v w := by
      intro w hw
      rcases Set.mem_insert_iff.mp (hTU hw) with hwv | hwN
      · exact False.elim (hv (hwv ▸ hw))
      · exact hwN
    have hpred : (k - 1) + 1 = k := Nat.sub_add_cancel (by omega)
    have hno' : NoLargeConnectedBipartite G ((k - 1) + 1) := by
      simpa [hpred] using hno
    have hlt := stable_neighbors_card_lt G (k - 1) hno' v T hTstable hadj
    omega

/-- The numerical conclusion of the induced-path localization lemma.
The path witness is omitted here because the separation argument uses only
its closed-neighborhood and complement bounds. -/
def PathLocalizationStatement (G : SimpleGraph V) (k q : ℕ) : Prop :=
  2 ≤ k → 1 ≤ q → NoLargeConnectedBipartite G k →
    q ≤ HadwigerLean.chromatic G →
    (∀ A B : Set V, Disjoint A B →
      HadwigerLean.chromatic (G.induce A) < q ∨
        HadwigerLean.chromatic (G.induce B) < q) →
    ∃ J : Set V,
      HadwigerLean.independenceNumber (G.induce J) ≤ k * (k - 1) ∧
      HadwigerLean.chromatic (G.induce Jᶜ) < q

/-- The closed neighborhood of a finite vertex set, represented as a set. -/
def closedNeighborhoodSet (G : SimpleGraph V) (P : Finset V) : Set V :=
  {w | ∃ v ∈ P, w = v ∨ G.Adj v w}

/-- A stable set covered by closed neighborhoods of vertices of P has
cardinality at most |P|(k-1). -/
theorem stable_closedNeighborhood_card_le (G : SimpleGraph V) (k : ℕ)
    (hk : 2 ≤ k) (hno : NoLargeConnectedBipartite G k)
    (P S : Finset V) (hS : G.IsIndepSet (S : Set V))
    (hcover : (S : Set V) ⊆ closedNeighborhoodSet G P) :
    S.card ≤ P.card * (k - 1) := by
  classical
  let B : V → Finset V := fun v =>
    S.filter (fun w => w = v ∨ G.Adj v w)
  have hBcard (v : V) : (B v).card ≤ k - 1 := by
    have hBstable : G.IsIndepSet (B v : Set V) := by
      intro x hx y hy hxy
      exact hS (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy
    by_cases hv : v ∈ B v
    · have hsub : B v ⊆ {v} := by
        intro w hw
        by_contra hne
        have hadj : G.Adj v w := by
          rcases (Finset.mem_filter.mp hw).2 with hwv | hwN
          · exact False.elim (hne (by simp [hwv]))
          · exact hwN
        have hne' : v ≠ w := by
          intro hvw
          exact hne (by simp [hvw])
        exact hBstable hv hw hne' hadj
      have hle : (B v).card ≤ 1 := by
        calc
          (B v).card ≤ ({v} : Finset V).card := Finset.card_le_card hsub
          _ = 1 := by simp
      omega
    · have hadj : ∀ w ∈ B v, G.Adj v w := by
        intro w hw
        rcases (Finset.mem_filter.mp hw).2 with hwv | hwN
        · exact False.elim (hv (hwv ▸ hw))
        · exact hwN
      have hpred : (k - 1) + 1 = k := Nat.sub_add_cancel (by omega)
      have hno' : NoLargeConnectedBipartite G ((k - 1) + 1) := by
        simpa [hpred] using hno
      have hlt := stable_neighbors_card_lt G (k - 1) hno' v (B v) hBstable hadj
      omega
  have hScover : S ⊆ P.biUnion B := by
    intro w hw
    obtain ⟨v, hv, hwv⟩ := hcover hw
    exact Finset.mem_biUnion.mpr
      ⟨v, hv, Finset.mem_filter.mpr ⟨hw, hwv⟩⟩
  calc
    S.card ≤ (P.biUnion B).card := Finset.card_le_card hScover
    _ ≤ P.card * (k - 1) :=
      Finset.card_biUnion_le_card_mul P B (k - 1) (fun v _ => hBcard v)

/-- Turning a bound for ambient stable finsets into an independence-number
bound for an induced graph. -/
private theorem independence_induce_le_of_stable_bound (G : SimpleGraph V)
    (U : Set V) (m : ℕ)
    (hbound : ∀ T : Finset V, G.IsIndepSet (T : Set V) →
      (T : Set V) ⊆ U → T.card ≤ m) :
    HadwigerLean.independenceNumber (G.induce U) ≤ m := by
  classical
  obtain ⟨S, hS, hScard⟩ :=
    HadwigerLean.exists_stable_card_eq_independenceNumber (G.induce U)
  let T : Finset V := S.map ⟨Subtype.val, Subtype.val_injective⟩
  have hTcard : T.card = S.card := by simp [T]
  have hTU : (T : Set V) ⊆ U := by
    intro w hw
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hw
    exact a.property
  have hTstable : G.IsIndepSet (T : Set V) := by
    intro x hx y hy hxy hadj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact hS ha hb (by intro hab; exact hxy (congrArg Subtype.val hab)) hadj
  rw [← hScard, ← hTcard]
  exact hbound T hTstable hTU

/-- Independence is at most the number of centers times the local bound. -/
theorem independence_closedNeighborhoodSet_le (G : SimpleGraph V) (k : ℕ)
    (hk : 2 ≤ k) (hno : NoLargeConnectedBipartite G k) (P : Finset V) :
    HadwigerLean.independenceNumber (G.induce (closedNeighborhoodSet G P)) ≤
      P.card * (k - 1) := by
  apply independence_induce_le_of_stable_bound G (closedNeighborhoodSet G P)
    (P.card * (k - 1))
  intro T hT hTU
  exact stable_closedNeighborhood_card_le G k hk hno P T hT hTU

/-- The numeric conclusion of path localization follows once a short path
has a low-chromatic complement of its closed neighborhood. -/
theorem localization_of_short_closed_path (G : SimpleGraph V) (k q : ℕ)
    (hk : 2 ≤ k) (hno : NoLargeConnectedBipartite G k)
    (P : Finset V) (hPcard : P.card ≤ k)
    (hcomp : HadwigerLean.chromatic
      (G.induce (closedNeighborhoodSet G P)ᶜ) < q) :
    ∃ J : Set V,
      HadwigerLean.independenceNumber (G.induce J) ≤ k * (k - 1) ∧
      HadwigerLean.chromatic (G.induce Jᶜ) < q := by
  refine ⟨closedNeighborhoodSet G P, ?_, hcomp⟩
  exact (independence_closedNeighborhoodSet_le G k hk hno P).trans
    (Nat.mul_le_mul_right (k - 1) hPcard)

@[simp] theorem closedNeighborhoodSet_empty (G : SimpleGraph V) :
    closedNeighborhoodSet G (∅ : Finset V) = ∅ := by
  ext w
  simp [closedNeighborhoodSet]

/-- Closed neighborhoods increase with their center set. -/
theorem closedNeighborhoodSet_mono (G : SimpleGraph V)
    {P Q : Finset V} (hPQ : P ⊆ Q) :
    closedNeighborhoodSet G P ⊆ closedNeighborhoodSet G Q := by
  rintro w ⟨v, hv, hw⟩
  exact ⟨v, hPQ hv, hw⟩

/-- The closed neighborhood after adding one center. -/
theorem closedNeighborhoodSet_insert (G : SimpleGraph V)
    (v : V) (P : Finset V) :
    closedNeighborhoodSet G (insert v P) =
      insert v (G.neighborSet v) ∪ closedNeighborhoodSet G P := by
  ext w
  simp only [closedNeighborhoodSet, Set.mem_setOf_eq, Finset.mem_insert,
    Set.mem_union, Set.mem_insert_iff, SimpleGraph.mem_neighborSet]
  aesop

/-- Vertices outside the closed neighborhood have no edge to a center. -/
theorem not_adj_of_not_mem_closedNeighborhoodSet (G : SimpleGraph V)
    (P : Finset V) {w v : V} (hw : w ∉ closedNeighborhoodSet G P)
    (hv : v ∈ P) : ¬ G.Adj v w := by
  intro hadj
  exact hw ⟨v, hv, Or.inr hadj⟩

/-- A component of G outside K maps into the graph induced on its
ambient vertex support. -/
private def componentToInduce (G : SimpleGraph V) (K : Set V)
    (C : G.ComponentCompl K) :
    C.toSimpleGraph →g G.induce (C : Set V) where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  map_rel' := by intro x y h; exact h

/-- If the complement of K has at least q colors, one of its
connected components has at least q colors. -/
theorem exists_high_component (G : SimpleGraph V) (K : Set V) (q : ℕ)
    (hq : 1 ≤ q)
    (h : q ≤ HadwigerLean.chromatic (G.induce Kᶜ)) :
    ∃ C : G.ComponentCompl K,
      q ≤ HadwigerLean.chromatic (G.induce (C : Set V)) := by
  classical
  by_contra hn
  have hall : ∀ C : G.ComponentCompl K,
      HadwigerLean.chromatic (G.induce (C : Set V)) < q := by
    intro C
    by_contra hC
    exact hn ⟨C, Nat.le_of_not_gt hC⟩
  have hcol : (G.induce Kᶜ).Colorable (q - 1) := by
    apply SimpleGraph.colorable_iff_forall_connectedComponents.mpr
    intro C
    have hlt := hall C
    have hc : (G.induce (C : Set V)).Colorable (q - 1) :=
      (HadwigerLean.chromatic_le_iff_colorable _ _).mp (by omega)
    obtain ⟨f⟩ := hc
    exact ⟨f.comp (componentToInduce G K C)⟩
  have hle := (HadwigerLean.chromatic_le_iff_colorable (G.induce Kᶜ) (q - 1)).mpr hcol
  omega

/-- Two high-chromatic components of one deleted graph must coincide
when the ambient graph contains no disjoint pair of high subgraphs. -/
theorem high_component_unique (G : SimpleGraph V) (K : Set V) (q : ℕ)
    (hnopair : ∀ A B : Set V, Disjoint A B →
      HadwigerLean.chromatic (G.induce A) < q ∨
        HadwigerLean.chromatic (G.induce B) < q)
    (C D : G.ComponentCompl K)
    (hC : q ≤ HadwigerLean.chromatic (G.induce (C : Set V)))
    (hD : q ≤ HadwigerLean.chromatic (G.induce (D : Set V))) :
    C = D := by
  by_contra hne
  have hdisj : Disjoint (C : Set V) (D : Set V) :=
    SimpleGraph.ComponentCompl.pairwise_disjoint hne
  rcases hnopair _ _ hdisj with h | h
  · omega
  · omega

/-- The new high component is contained in the previous one after
deleting more vertices. -/
theorem high_component_nested (G : SimpleGraph V) (K L : Set V)
    (q : ℕ) (hKL : K ⊆ L)
    (hnopair : ∀ A B : Set V, Disjoint A B →
      HadwigerLean.chromatic (G.induce A) < q ∨
        HadwigerLean.chromatic (G.induce B) < q)
    (C : G.ComponentCompl L) (D : G.ComponentCompl K)
    (hC : q ≤ HadwigerLean.chromatic (G.induce (C : Set V)))
    (hD : q ≤ HadwigerLean.chromatic (G.induce (D : Set V))) :
    (C : Set V) ⊆ (D : Set V) := by
  have heq : C.hom hKL = D := by
    by_contra hne
    have hdisj : Disjoint (C : Set V) (D : Set V) := by
      by_contra hnot
      exact hne ((SimpleGraph.ComponentCompl.hom_eq_iff_not_disjoint C hKL D).mpr hnot)
    rcases hnopair _ _ hdisj with h | h
    · omega
    · omega
  simpa [heq] using C.subset_hom hKL

/-- The high component after deleting L maps to the previous high
component after deleting K. -/
theorem high_component_hom_eq (G : SimpleGraph V) (K L : Set V)
    (q : ℕ) (hKL : K ⊆ L)
    (hnopair : ∀ A B : Set V, Disjoint A B →
      HadwigerLean.chromatic (G.induce A) < q ∨
        HadwigerLean.chromatic (G.induce B) < q)
    (C : G.ComponentCompl L) (D : G.ComponentCompl K)
    (hC : q ≤ HadwigerLean.chromatic (G.induce (C : Set V)))
    (hD : q ≤ HadwigerLean.chromatic (G.induce (D : Set V))) :
    C.hom hKL = D := by
  apply (SimpleGraph.ComponentCompl.hom_eq_iff_le C hKL D).2
  exact high_component_nested G K L q hKL hnopair C D hC hD

/-- A boundary vertex adjacent to the current path endpoint also
touches the next high component. -/
theorem boundary_extension (G : SimpleGraph V)
    (K L : Set V) (v : V) (hKL : K ⊆ L)
    (hL_v : v ∈ L) (hL_adj : ∀ x, G.Adj v x → x ∈ L)
    (hL_new : ∀ x ∈ L, x ∉ K → x = v ∨ G.Adj v x)
    (C : G.ComponentCompl K) (D : G.ComponentCompl L)
    (hhom : D.hom hKL = C)
    (htouch : ∃ x ∈ (C : Set V), x = v ∨ G.Adj v x) :
    ∃ w ∈ (C : Set V), G.Adj v w ∧
      ∃ a ∈ (D : Set V), G.Adj w a := by
  classical
  have hsub : (D : Set V) ⊆ (C : Set V) := by
    simpa only [hhom] using D.subset_hom hKL
  obtain ⟨u, huD⟩ := D.nonempty
  have huC := hsub huD
  obtain ⟨x, hxC, hxTouch⟩ := htouch
  have hxL : x ∈ L := by
    rcases hxTouch with rfl | hadj
    · exact hL_v
    · exact hL_adj x hadj
  have hxNotD : x ∉ (D : Set V) := by
    intro hxD
    exact D.notMem_of_mem hxD hxL
  let H := G.induce Kᶜ
  let C' : H.ConnectedComponent := C
  rcases huC with ⟨huK, huEq⟩
  rcases hxC with ⟨hxK, hxEq⟩
  let uu : C'.supp := ⟨⟨u, huK⟩, huEq⟩
  let xx : C'.supp := ⟨⟨x, hxK⟩, hxEq⟩
  let A : Set C'.supp := {z | z.1.1 ∈ (D : Set V)}
  obtain ⟨p⟩ := C'.connected_toSimpleGraph.preconnected uu xx
  obtain ⟨d, _, hdA, hdNotA⟩ :=
    p.exists_boundary_dart A (by exact huD) (by exact hxNotD)
  let a : V := d.fst.1.1
  let w : V := d.snd.1.1
  have haD : a ∈ (D : Set V) := hdA
  have hwNotD : w ∉ (D : Set V) := hdNotA
  have hwC : w ∈ (C : Set V) := ⟨d.snd.1.2, d.snd.2⟩
  have haw : G.Adj a w := d.adj
  have hwL : w ∈ L := by
    by_contra hwNotL
    exact hwNotD
      (SimpleGraph.ComponentCompl.mem_of_adj a w haD hwNotL haw)
  have hwNotK : w ∉ K := C.notMem_of_mem hwC
  rcases hL_new w hwL hwNotK with hweq | hvw
  · have hva : G.Adj v a := by simpa only [hweq] using haw.symm
    exact False.elim ((D.notMem_of_mem haD) (hL_adj a hva))
  · exact ⟨w, hwC, hvw, a, haD, haw.symm⟩

/-- Inducing on all vertices leaves the finite chromatic number unchanged. -/
theorem chromatic_induce_univ (G : SimpleGraph V) :
    HadwigerLean.chromatic (G.induce Set.univ) =
      HadwigerLean.chromatic G := by
  apply Nat.le_antisymm
  · apply (HadwigerLean.chromatic_le_iff_colorable _ _).2
    exact SimpleGraph.Colorable.of_hom
      (SimpleGraph.induceUnivIso G).toHom
      (HadwigerLean.colorable_chromatic G)
  · apply (HadwigerLean.chromatic_le_iff_colorable _ _).2
    exact SimpleGraph.Colorable.of_hom
      (SimpleGraph.induceUnivIso G).symm.toHom
      (HadwigerLean.colorable_chromatic (G.induce Set.univ))

/-- A single vertex induces a connected bipartite graph. -/
private theorem singleton_connected_bipartite (G : SimpleGraph V) (v : V) :
    (G.induce ({v} : Set V)).Connected ∧
      (G.induce ({v} : Set V)).IsBipartite := by
  haveI : Nonempty ({v} : Set V) := ⟨⟨v, by simp⟩⟩
  haveI : Subsingleton ({v} : Set V) := by
    constructor
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    apply Subtype.ext
    simpa using hx.trans hy.symm
  constructor
  · rw [G.induce_singleton_eq_top]
    exact SimpleGraph.connected_top
  · refine ⟨SimpleGraph.Coloring.mk (fun _ => (0 : Fin 2)) ?_⟩
    intro x y hxy
    exact False.elim ((G.induce ({v} : Set V)).ne_of_adj hxy
      (Subsingleton.elim x y))

/-- A partial induced path, recorded only by its vertex set, final
vertex, and the high component from the previous stage. The connected
bipartite invariant suffices because every extension attaches a leaf. -/
private def IsActivePath (G : SimpleGraph V) (k q : ℕ) (S : Finset V) : Prop :=
  ∃ (P : Finset V) (v : V)
    (C : G.ComponentCompl (closedNeighborhoodSet G P)),
    S = insert v P ∧ v ∉ P ∧
      q ≤ HadwigerLean.chromatic (G.induce (C : Set V)) ∧
      (∃ x ∈ (C : Set V), x = v ∨ G.Adj v x) ∧
      (G.induce (S : Set V)).Connected ∧
      (G.induce (S : Set V)).IsBipartite ∧
      S.card < k

/-- The initial one-vertex path lies in a high component. -/
private theorem initial_active_path (G : SimpleGraph V) (k q : ℕ)
    (hk : 2 ≤ k) (hq : 1 ≤ q)
    (hchi : q ≤ HadwigerLean.chromatic G) :
    ∃ S : Finset V, IsActivePath G k q S := by
  classical
  let K : Set V := closedNeighborhoodSet G ∅
  have hK : K = ∅ := by simp [K]
  have hKc : Kᶜ = Set.univ := by
    rw [hK]
    simp
  have hhigh : q ≤ HadwigerLean.chromatic (G.induce Kᶜ) := by
    rw [hKc, chromatic_induce_univ]
    exact hchi
  obtain ⟨C, hC⟩ := exists_high_component G K q hq hhigh
  obtain ⟨v, hv⟩ := C.nonempty
  refine ⟨{v}, ∅, v, C, ?_, ?_, hC, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · exact ⟨v, hv, Or.inl rfl⟩
  · rw [Finset.coe_singleton]
    exact (singleton_connected_bipartite G v).1
  · rw [Finset.coe_singleton]
    exact (singleton_connected_bipartite G v).2
  · simp; omega

/-- Adding a leaf to an induced connected bipartite graph preserves
connectedness and bipartiteness. -/
private theorem leaf_connected_bipartite
    (G : SimpleGraph V) (P : Finset V) (v w : V)
    (hv : v ∈ P) (_hw : w ∉ P) (hvw : G.Adj v w)
    (honly : ∀ x ∈ P, G.Adj w x → x = v)
    (hconn : (G.induce (P : Set V)).Connected)
    (hbip : (G.induce (P : Set V)).IsBipartite) :
    (G.induce ((insert w P : Finset V) : Set V)).Connected ∧
      (G.induce ((insert w P : Finset V) : Set V)).IsBipartite := by
  classical
  constructor
  · have hsingle : (G.induce ({w} : Set V)).Preconnected := by
      intro x y
      have hxy : x = y := Subtype.ext
        (by simpa only [Set.mem_singleton_iff] using x.2.trans y.2.symm)
      subst y
      exact SimpleGraph.Reachable.refl _
    have hc := G.connected_induce_union hconn.preconnected hsingle hv (by simp) hvw
    have hset : ((insert w P : Finset V) : Set V) = (P : Set V) ∪ {w} := by
      ext z
      simp
    rw [hset]
    exact hc
  · let f := hbip.some
    let vc : Fin 2 := f ⟨v, hv⟩
    let wc : Fin 2 := if vc = 0 then 1 else 0
    have hwc : wc ≠ vc := by
      have h2 : ∀ c : Fin 2, (if c = 0 then 1 else 0) ≠ c := by decide
      exact h2 vc
    let cf (x : V) : Fin 2 := if hx : x ∈ P then f ⟨x, hx⟩ else 0
    have hcfv : cf v = vc := by simp [cf, hv, vc]
    let nf (x : V) : Fin 2 := if x = w then wc else cf x
    refine ⟨SimpleGraph.Coloring.mk (fun z => nf z.1) ?_⟩
    intro x y hxy
    have hadj : G.Adj x.1 y.1 := hxy
    by_cases hx : x.1 = w
    · by_cases hy : y.1 = w
      · exact False.elim ((G.ne_of_adj hadj) (hx.trans hy.symm))
      · have hyP : y.1 ∈ P := by
          rcases Finset.mem_insert.mp y.2 with h | h
          · exact False.elim (hy h)
          · exact h
        have hyv : y.1 = v := honly y.1 hyP (by simpa only [hx] using hadj)
        have hcfy : cf y.1 = vc := by simpa only [hyv] using hcfv
        simp only [nf, if_pos hx, if_neg hy, hcfy]
        exact hwc
    · by_cases hy : y.1 = w
      · have hxP : x.1 ∈ P := by
          rcases Finset.mem_insert.mp x.2 with h | h
          · exact False.elim (hx h)
          · exact h
        have hxv : x.1 = v := honly x.1 hxP (by simpa only [hy] using hadj.symm)
        have hcfx : cf x.1 = vc := by simpa only [hxv] using hcfv
        simp only [nf, if_neg hx, if_pos hy, hcfx]
        exact Ne.symm hwc
      · have hxP : x.1 ∈ P := by
          rcases Finset.mem_insert.mp x.2 with h | h
          · exact False.elim (hx h)
          · exact h
        have hyP : y.1 ∈ P := by
          rcases Finset.mem_insert.mp y.2 with h | h
          · exact False.elim (hy h)
          · exact h
        have hfvalid := f.valid
          (show (G.induce (P : Set V)).Adj ⟨x.1,hxP⟩ ⟨y.1,hyP⟩ from hadj)
        simpa [nf, hx, hy, cf, hxP, hyP] using hfvalid

/-- If an active path still leaves a high-chromatic complement, append
one leaf and obtain a strictly larger active path. -/
private theorem extend_active_path (G : SimpleGraph V) (k q : ℕ)
    (hq : 1 ≤ q) (hno : NoLargeConnectedBipartite G k)
    (hnopair : ∀ A B : Set V, Disjoint A B →
      HadwigerLean.chromatic (G.induce A) < q ∨
        HadwigerLean.chromatic (G.induce B) < q)
    {S : Finset V} (hactive : IsActivePath G k q S)
    (hhigh : q ≤ HadwigerLean.chromatic
      (G.induce (closedNeighborhoodSet G S)ᶜ)) :
    ∃ T : Finset V, IsActivePath G k q T ∧ S.card < T.card := by
  classical
  rcases hactive with ⟨P, v, C, rfl, hvP, hC, htouch, hconn, hbip, hshort⟩
  let K : Set V := closedNeighborhoodSet G P
  let L : Set V := closedNeighborhoodSet G (insert v P)
  have hKL : K ⊆ L :=
    closedNeighborhoodSet_mono G (Finset.subset_insert v P)
  have hLv : v ∈ L := ⟨v, Finset.mem_insert_self _ _, Or.inl rfl⟩
  have hLadj : ∀ x, G.Adj v x → x ∈ L := by
    intro x hx
    exact ⟨v, Finset.mem_insert_self _ _, Or.inr hx⟩
  have hLnew : ∀ x ∈ L, x ∉ K → x = v ∨ G.Adj v x := by
    intro x hxL hxK
    obtain ⟨t, ht, hxt⟩ := hxL
    rcases Finset.mem_insert.mp ht with htv | htP
    · simpa [htv] using hxt
    · exact False.elim (hxK ⟨t, htP, hxt⟩)
  have hhigh' : q ≤ HadwigerLean.chromatic (G.induce Lᶜ) := by
    simpa only [L] using hhigh
  obtain ⟨D, hD⟩ := exists_high_component G L q hq hhigh'
  have hhom : D.hom hKL = C :=
    high_component_hom_eq G K L q hKL hnopair D C hD hC
  obtain ⟨w, hwC, hvw, a, haD, hwa⟩ :=
    boundary_extension G K L v hKL hLv hLadj hLnew C D hhom htouch
  have hwNotK : w ∉ K := C.notMem_of_mem hwC
  have hwNotP : w ∉ P := by
    intro hwP
    exact hwNotK ⟨w, hwP, Or.inl rfl⟩
  have hwNeV : w ≠ v := (G.ne_of_adj hvw).symm
  have hwNotS : w ∉ insert v P := by
    simpa only [Finset.mem_insert] using
      (show ¬ (w = v ∨ w ∈ P) from not_or.mpr ⟨hwNeV, hwNotP⟩)
  have honly : ∀ x ∈ insert v P, G.Adj w x → x = v := by
    intro x hx hadj
    rcases Finset.mem_insert.mp hx with hxv | hxP
    · exact hxv
    · exact False.elim (hwNotK ⟨x, hxP, Or.inr hadj.symm⟩)
  let T : Finset V := insert w (insert v P)
  have hgood := leaf_connected_bipartite G (insert v P) v w
    (Finset.mem_insert_self _ _) hwNotS hvw honly hconn hbip
  have hTcard : T.card = (insert v P).card + 1 := by
    simpa only [T] using Finset.card_insert_of_notMem hwNotS
  have hTshort : T.card < k := by
    by_contra hnot
    have hcard : T.card = k := by omega
    exact hno T hcard hgood
  refine ⟨T, ?_, ?_⟩
  · refine ⟨insert v P, w, D, rfl, hwNotS, hD, ?_, hgood.1, hgood.2, hTshort⟩
    exact ⟨a, haD, Or.inr hwa⟩
  · omega

/-- Choose an active path with the largest vertex set. -/
private theorem exists_max_active_path (G : SimpleGraph V) (k q : ℕ)
    (hk : 2 ≤ k) (hq : 1 ≤ q)
    (hchi : q ≤ HadwigerLean.chromatic G) :
    ∃ S : Finset V, IsActivePath G k q S ∧
      ∀ T : Finset V, IsActivePath G k q T → T.card ≤ S.card := by
  classical
  let A : Finset (Finset V) := Finset.univ.filter (IsActivePath G k q)
  have hA : A.Nonempty := by
    obtain ⟨S, hS⟩ := initial_active_path G k q hk hq hchi
    exact ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩⟩
  obtain ⟨S, hSA, hmax⟩ := Finset.exists_max_image A Finset.card hA
  refine ⟨S, (Finset.mem_filter.mp hSA).2, ?_⟩
  intro T hT
  exact hmax T (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩)

/-- The induced-path localization conclusion of paper Lemma 13, in the
numeric form needed by separation. Its witness is the closed neighborhood
of a finite leaf-grown induced path. -/
theorem path_localization (G : SimpleGraph V) (k q : ℕ) :
    PathLocalizationStatement G k q := by
  intro hk hq hno hchi hnopair
  obtain ⟨S, hS, hmax⟩ := exists_max_active_path G k q hk hq hchi
  have hlow : HadwigerLean.chromatic
      (G.induce (closedNeighborhoodSet G S)ᶜ) < q := by
    by_contra hnot
    have hhigh : q ≤ HadwigerLean.chromatic
        (G.induce (closedNeighborhoodSet G S)ᶜ) := Nat.le_of_not_gt hnot
    obtain ⟨T, hT, hST⟩ :=
      extend_active_path G k q hq hno hnopair hS hhigh
    exact (Nat.not_le_of_gt hST) (hmax T hT)
  obtain ⟨_, _, _, _, _, _, _, _, _, hshort⟩ := hS
  exact localization_of_short_closed_path G k q hk hno S
    (Nat.le_of_lt hshort) hlow

end HadwigerLean.Bootstrap
























