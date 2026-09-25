import HadwigerLean.Graph.ChromaticConnectivity.Template
import Mathlib.Data.Nat.Find

/-!
# The additive chromatic connectivity argument

This module proves the Girão--Narayanan argument by choosing a smallest
induced graph admitting an admissible obstructing template. The connectivity
and chromatic-loss estimates follow from separator gluing and weighted-chunk recoloring.
-/

namespace HadwigerLean

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An induced vertex set admits an admissible, nonextendable palette template. -/
def HasAdmissibleObstruction (G : SimpleGraph V) (k n : ℕ) (U : Finset V) : Prop :=
  ∃ T : ChromaticTemplate V (Fin n),
    T.carrier = U ∧ T.Admissible G k ∧ T.Obstructing G

/-- Any graph requiring at least `7k` colors has a smallest induced carrier
supporting an admissible obstructing template with one fewer color. -/
theorem exists_minimal_obstructing_carrier (G : SimpleGraph V) (k : ℕ)
    (hk : 0 < k) (hχ : 7 * k ≤ chromatic G) :
    ∃ U : Finset V,
      HasAdmissibleObstruction G k (chromatic G - 1) U ∧
      ∀ W : Finset V, W.card < U.card →
        ¬ HasAdmissibleObstruction G k (chromatic G - 1) W := by
  classical
  have hq : 0 < chromatic G := by omega
  have hn : 0 < chromatic G - 1 := by omega
  let c : Fin (chromatic G - 1) := ⟨0, hn⟩
  have hnot : ¬ G.Colorable (chromatic G - 1) := by
    intro hc
    have hle := (chromatic_le_iff_colorable G _).2 hc
    omega
  have hinit : HasAdmissibleObstruction G k (chromatic G - 1) Finset.univ := by
    refine ⟨ChromaticTemplate.empty c, rfl, ?_, ?_⟩
    · exact ChromaticTemplate.empty_admissible G c k
    · exact ChromaticTemplate.empty_obstructing G c hnot
  let P (m : ℕ) : Prop := ∃ U : Finset V,
    U.card = m ∧ HasAdmissibleObstruction G k (chromatic G - 1) U
  have hP : ∃ m, P m := ⟨Finset.univ.card, Finset.univ, rfl, hinit⟩
  obtain ⟨U, hcard, hU⟩ := Nat.find_spec hP
  refine ⟨U, hU, ?_⟩
  intro W hW hbad
  have hsmall : W.card < Nat.find hP := by simpa [← hcard] using hW
  exact Nat.find_min hP hsmall ⟨W, rfl, hbad⟩

/-- Once the carrier is fixed, there is an admissible obstructing template
with the largest possible precolored set. -/
theorem exists_maximal_precoloring (G : SimpleGraph V) (k n : ℕ)
    (U : Finset V) (hU : HasAdmissibleObstruction G k n U) :
    ∃ T : ChromaticTemplate V (Fin n),
      T.carrier = U ∧ T.Admissible G k ∧ T.Obstructing G ∧
      ∀ T' : ChromaticTemplate V (Fin n),
        T'.carrier = U → T'.Admissible G k → T'.Obstructing G →
          T'.precolored.card ≤ T.precolored.card := by
  classical
  let S : Finset ℕ :=
    (Finset.range (Fintype.card V + 1)).filter
      (fun m => ∃ T : ChromaticTemplate V (Fin n),
        T.carrier = U ∧ T.Admissible G k ∧ T.Obstructing G ∧
          T.precolored.card = m)
  have hS : S.Nonempty := by
    obtain ⟨T, hT, ha, ho⟩ := hU
    refine ⟨T.precolored.card, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, T, hT, ha, ho, rfl⟩
    have hcard : T.precolored.card ≤ Fintype.card V :=
      (Finset.card_le_card (Finset.subset_univ T.precolored))
    omega
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image S id hS
  obtain ⟨_, T, hT, ha, ho, hcard⟩ := Finset.mem_filter.mp hm
  refine ⟨T, hT, ha, ho, ?_⟩
  intro T' hT' ha' ho'
  have hm' : T'.precolored.card ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, T', hT', ha', ho', rfl⟩
    have hbound : T'.precolored.card ≤ Fintype.card V :=
      Finset.card_le_card (Finset.subset_univ T'.precolored)
    omega
  have hle := hmax T'.precolored.card hm'
  simpa only [id_eq, ← hcard] using hle

/-- Maximality of the precolored set forces every remaining forbidden list
to have fewer than k colors. This is the first GN extremal step. -/
theorem lists_small_of_maximal_precoloring (G : SimpleGraph V) (k n : ℕ)
    (hk : 0 < k) (hpalette : 4 * k < n)
    (U : Finset V) (T : ChromaticTemplate V (Fin n))
    (hcarrier : T.carrier = U) (ha : T.Admissible G k)
    (ho : T.Obstructing G)
    (hmax : ∀ T' : ChromaticTemplate V (Fin n),
      T'.carrier = U → T'.Admissible G k → T'.Obstructing G →
        T'.precolored.card ≤ T.precolored.card) :
    ∀ v ∈ T.carrier \ T.precolored, (T.forbidden v).card < k := by
  classical
  intro v hv
  by_contra hbad
  have hkF : k ≤ (T.forbidden v).card := by omega
  obtain ⟨γ, hγF, hγS⟩ :=
    T.exists_fresh_color G k hk ha (by simpa using hpalette) v hv
  let T' := T.precolor v (Finset.mem_sdiff.mp hv).1 γ
  have ha' : T'.Admissible G k :=
    T.precolor_admissible G k ha v hv γ hγS hkF
  have ho' : T'.Obstructing G :=
    T.precolor_obstructing G v hv γ hγF ho
  have hcard := hmax T' (by simpa [T', ChromaticTemplate.precolor] using hcarrier)
    ha' ho'
  have hvS : v ∉ T.precolored := (Finset.mem_sdiff.mp hv).2
  have hstrict : T.precolored.card < T'.precolored.card := by
    simp [T', ChromaticTemplate.precolor, hvS]
  omega

/-- The maximally precolored obstructing carrier has more than k vertices. -/
theorem large_carrier_of_maximal_precoloring (G : SimpleGraph V) (k n : ℕ)
    (hk : 0 < k) (hpalette : 4 * k < n)
    (U : Finset V) (T : ChromaticTemplate V (Fin n))
    (hcarrier : T.carrier = U) (ha : T.Admissible G k)
    (ho : T.Obstructing G)
    (hmax : ∀ T' : ChromaticTemplate V (Fin n),
      T'.carrier = U → T'.Admissible G k → T'.Obstructing G →
        T'.precolored.card ≤ T.precolored.card) :
    k < U.card := by
  have hshort := lists_small_of_maximal_precoloring G k n hk hpalette
    U T hcarrier ha ho hmax
  have hn : 0 < n := by omega
  let base : Fin n := ⟨0, hn⟩
  by_contra hsmall
  have hcard : T.carrier.card ≤ k := by
    rw [hcarrier]
    omega
  exact (T.not_obstructing_of_small_carrier G base k hk
    (by simpa using hpalette) ha hshort hcard) ho

/-- The first complete extremal reduction in Appendix A.2: for a graph
requiring at least 7k colors, there is a vertex-minimal obstructing induced
carrier, and every maximizing template on it has more than k vertices and
short forbidden lists. -/
theorem exists_large_minimal_obstruction (G : SimpleGraph V) (k : ℕ)
    (hk : 0 < k) (hχ : 7 * k ≤ chromatic G) :
    ∃ (U : Finset V) (T : ChromaticTemplate V (Fin (chromatic G - 1))),
      k < U.card ∧
      T.carrier = U ∧ T.Admissible G k ∧ T.Obstructing G ∧
      (∀ W : Finset V, W.card < U.card →
        ¬ HasAdmissibleObstruction G k (chromatic G - 1) W) ∧
      (∀ v ∈ T.carrier \ T.precolored, (T.forbidden v).card < k) := by
  classical
  obtain ⟨U, hU, hmin⟩ :=
    exists_minimal_obstructing_carrier G k hk hχ
  obtain ⟨T, hT, ha, ho, hmax⟩ :=
    exists_maximal_precoloring G k (chromatic G - 1) U hU
  have hpalette : 4 * k < chromatic G - 1 := by omega
  have hlarge := large_carrier_of_maximal_precoloring G k
    (chromatic G - 1) hk hpalette U T hT ha ho hmax
  have hshort := lists_small_of_maximal_precoloring G k
    (chromatic G - 1) hk hpalette U T hT ha ho hmax
  exact ⟨U, T, hlarge, hT, ha, ho, hmin, hshort⟩

/-- The extremal carrier from the template argument has no decomposition
across fewer than k vertices into two nonempty anticomplete sides. -/
theorem no_small_separation_of_minimal_obstruction
    (G : SimpleGraph V) (k n : ℕ) (hk : 0 < k)
    (T : ChromaticTemplate V (Fin n))
    (ha : T.Admissible G k) (ho : T.Obstructing G)
    (hshort : ∀ v ∈ T.carrier \ T.precolored,
      (T.forbidden v).card < k)
    (hmin : ∀ W : Finset V, W.card < T.carrier.card →
      ¬ HasAdmissibleObstruction G k n W)
    (X Y Z : Finset V) (hcover : T.carrier = X ∪ Y ∪ Z)
    (hX : X.card < k) (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (hdisjZ : Disjoint Z (X ∪ Y))
    (hdisjY : Disjoint Y (X ∪ Z))
    (hno : ∀ ⦃y z : V⦄, y ∈ Y → z ∈ Z → ¬ G.Adj y z) :
    False := by
  classical
  have hminimal : ∀ T' : ChromaticTemplate V (Fin n),
      T'.carrier.card < T.carrier.card →
      T'.Admissible G k → ∃ f : V → Fin n, T'.Extends G f := by
    intro T' hcard hAd
    by_contra hnoext
    exact hmin T'.carrier hcard ⟨T', rfl, hAd, hnoext⟩
  exact T.no_small_separation G k hk ha ho hshort hminimal
    X Y Z hcover hX hY hZ hdisjZ hdisjY hno

/-- A disconnected finite graph splits into two nonempty anticomplete parts. -/
theorem disconnected_partition {W : Type*} [Fintype W] [DecidableEq W]
    [Nonempty W] (H : SimpleGraph W) (hH : ¬ H.Connected) :
    ∃ Y Z : Finset W,
      Y ∪ Z = Finset.univ ∧ Disjoint Y Z ∧
      Y.Nonempty ∧ Z.Nonempty ∧
      (∀ ⦃y z : W⦄, y ∈ Y → z ∈ Z → ¬ H.Adj y z) := by
  classical
  have hnotpre : ¬ H.Preconnected := by
    intro hp
    exact hH ⟨hp⟩
  obtain ⟨x, y, hxy⟩ : ∃ x y : W, ¬ H.Reachable x y := by
    simpa only [SimpleGraph.Preconnected, not_forall] using hnotpre
  let Y : Finset W := Finset.univ.filter (fun v => H.Reachable x v)
  let Z : Finset W := Finset.univ \ Y
  have hYx : x ∈ Y := by
    simp [Y]
  have hZy : y ∈ Z := by
    simp [Z, Y, hxy]
  refine ⟨Y, Z, ?_, ?_, ⟨x, hYx⟩, ⟨y, hZy⟩, ?_⟩
  · ext v
    simp [Z]
  · exact Finset.disjoint_sdiff
  · intro u v hu hv huv
    have hxu : H.Reachable x u := (Finset.mem_filter.mp hu).2
    have hxv : H.Reachable x v := hxu.trans huv.reachable
    exact (Finset.mem_sdiff.mp hv).2
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxv⟩)

/-- A disconnection after deleting fewer than k vertices of an induced
graph produces the finite separator partition used by the template lemma. -/
theorem partition_of_disconnected_delete (G : SimpleGraph V)
    (S : Finset V) (k : ℕ) (horder : k < S.card)
    (D : Finset (S : Set V)) (hD : D.card < k)
    (hconn : ¬ ((G.induce (S : Set V)).induce
      (D : Set (S : Set V))ᶜ).Connected) :
    ∃ X Y Z : Finset V,
      S = X ∪ Y ∪ Z ∧ X.card < k ∧
      Y.Nonempty ∧ Z.Nonempty ∧
      Disjoint Z (X ∪ Y) ∧ Disjoint Y (X ∪ Z) ∧
      (∀ ⦃y z : V⦄, y ∈ Y → z ∈ Z → ¬ G.Adj y z) := by
  classical
  let U : Set V := S
  have hScard : Fintype.card U = S.card := by
    simp [U]
  have hDcard : D.card < (Finset.univ : Finset U).card := by
    simpa [hScard] using (lt_trans hD horder)
  obtain ⟨d, _, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hDcard
  let W : Set U := (D : Set U)ᶜ
  haveI : Nonempty W := ⟨⟨d, hd⟩⟩
  let H := (G.induce U).induce W
  obtain ⟨P, Q, hPQ, hdisjPQ, hP, hQ, hnoPQ⟩ :=
    disconnected_partition H hconn
  let e : W → V := fun w => w.1.1
  have he : Function.Injective e := by
    intro u v h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  let X : Finset V := D.image (fun d : U => d.1)
  let Y : Finset V := P.image e
  let Z : Finset V := Q.image e
  have hXcard : X.card < k := by
    have hcard : X.card = D.card := by
      exact Finset.card_image_of_injective D Subtype.coe_injective
    omega
  have hcover : S = X ∪ Y ∪ Z := by
    ext v
    constructor
    · intro hv
      let s : U := ⟨v, hv⟩
      by_cases hsD : s ∈ D
      · apply Finset.mem_union.mpr
        left
        apply Finset.mem_union.mpr
        left
        exact Finset.mem_image.mpr ⟨s, hsD, rfl⟩
      · let w : W := ⟨s, hsD⟩
        have hw : w ∈ P ∪ Q := by
          rw [hPQ]
          exact Finset.mem_univ _
        rcases Finset.mem_union.mp hw with hwP | hwQ
        · apply Finset.mem_union.mpr
          left
          apply Finset.mem_union.mpr
          right
          exact Finset.mem_image.mpr ⟨w, hwP, rfl⟩
        · apply Finset.mem_union.mpr
          right
          exact Finset.mem_image.mpr ⟨w, hwQ, rfl⟩
    · intro hv
      rcases Finset.mem_union.mp hv with hXY | hZ
      · rcases Finset.mem_union.mp hXY with hX | hY
        · obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hX
          exact d.property
        · obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hY
          exact w.1.property
      · obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hZ
        exact w.1.property
  have hXYdisj : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro v hvX hvY
    obtain ⟨d, hdD, hdv⟩ := Finset.mem_image.mp hvX
    obtain ⟨w, _, hwv⟩ := Finset.mem_image.mp hvY
    have heq : d = w.1 := Subtype.ext (hdv.trans hwv.symm)
    exact w.2 (heq ▸ hdD)
  have hXZdisj : Disjoint X Z := by
    apply Finset.disjoint_left.mpr
    intro v hvX hvZ
    obtain ⟨d, hdD, hdv⟩ := Finset.mem_image.mp hvX
    obtain ⟨w, _, hwv⟩ := Finset.mem_image.mp hvZ
    have heq : d = w.1 := Subtype.ext (hdv.trans hwv.symm)
    exact w.2 (heq ▸ hdD)
  have hYZdisj : Disjoint Y Z := by
    apply Finset.disjoint_left.mpr
    intro v hvY hvZ
    obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp hvY
    obtain ⟨q, hq, hqv⟩ := Finset.mem_image.mp hvZ
    have heq : p = q := he (hpv.trans hqv.symm)
    exact (Finset.disjoint_left.mp hdisjPQ) hp (heq ▸ hq)
  have hZdisj : Disjoint Z (X ∪ Y) := by
    apply Finset.disjoint_left.mpr
    intro v hvZ hvXY
    rcases Finset.mem_union.mp hvXY with hvX | hvY
    · exact (Finset.disjoint_left.mp hXZdisj) hvX hvZ
    · exact (Finset.disjoint_left.mp hYZdisj) hvY hvZ
  have hYdisj : Disjoint Y (X ∪ Z) := by
    apply Finset.disjoint_left.mpr
    intro v hvY hvXZ
    rcases Finset.mem_union.mp hvXZ with hvX | hvZ
    · exact (Finset.disjoint_left.mp hXYdisj) hvX hvY
    · exact (Finset.disjoint_left.mp hYZdisj) hvY hvZ
  have hno : ∀ ⦃y z : V⦄, y ∈ Y → z ∈ Z → ¬ G.Adj y z := by
    intro y z hy hz hyz
    obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp hy
    obtain ⟨q, hq, hqv⟩ := Finset.mem_image.mp hz
    have hpq : H.Adj p q := by
      simpa [H, U, e, ← hpv, ← hqv] using hyz
    exact hnoPQ hp hq hpq
  exact ⟨X, Y, Z, hcover, hXcard, hP.image e,
    hQ.image e, hZdisj, hYdisj, hno⟩

theorem vertexConnected_of_no_small_separation
    (G : SimpleGraph V) (S : Finset V) (k : ℕ)
    (horder : k < S.card)
    (hsep : ∀ X Y Z : Finset V,
      S = X ∪ Y ∪ Z → X.card < k →
      Y.Nonempty → Z.Nonempty →
      Disjoint Z (X ∪ Y) → Disjoint Y (X ∪ Z) →
      (∀ ⦃y z : V⦄, y ∈ Y → z ∈ Z → ¬ G.Adj y z) → False) :
    VertexConnected (G.induce (S : Set V)) k := by
  classical
  refine ⟨?_, ?_⟩
  · simpa using horder
  · intro D hD
    by_contra hconn
    obtain ⟨X, Y, Z, hcover, hX, hY, hZ, hdisjZ, hdisjY, hno⟩ :=
      partition_of_disconnected_delete G S k horder D hD hconn
    exact hsep X Y Z hcover hX hY hZ hdisjZ hdisjY hno

/-- The maximally precolored minimal obstruction is k-vertex-connected. -/
theorem connected_of_minimal_obstruction
    (G : SimpleGraph V) (k n : ℕ) (hk : 0 < k)
    (T : ChromaticTemplate V (Fin n))
    (horder : k < T.carrier.card)
    (ha : T.Admissible G k) (ho : T.Obstructing G)
    (hshort : ∀ v ∈ T.carrier \ T.precolored,
      (T.forbidden v).card < k)
    (hmin : ∀ W : Finset V, W.card < T.carrier.card →
      ¬ HasAdmissibleObstruction G k n W) :
    VertexConnected (G.induce (T.carrier : Set V)) k := by
  apply vertexConnected_of_no_small_separation G T.carrier k horder
  intro X Y Z hcover hX hY hZ hdisjZ hdisjY hno
  exact no_small_separation_of_minimal_obstruction
    G k n hk T ha ho hshort hmin X Y Z
    hcover hX hY hZ hdisjZ hdisjY hno


/-- An obstructing template with short lists forces the induced carrier to
retain all but six k of the palette colors. -/
theorem chromatic_bound_of_obstructing_template
    (G : SimpleGraph V) (k n : ℕ) (hk : 0 < k)
    (T : ChromaticTemplate V (Fin n))
    (hnonempty : T.carrier.Nonempty)
    (ha : T.Admissible G k) (ho : T.Obstructing G)
    (hshort : ∀ v ∈ T.carrier \ T.precolored,
      (T.forbidden v).card < k) :
    n < chromatic (G.induce (T.carrier : Set V)) + 6 * k := by
  classical
  let H := G.induce (T.carrier : Set V)
  let m := chromatic H
  obtain ⟨c⟩ := colorable_chromatic H
  obtain ⟨v₀, hv₀⟩ := hnonempty
  let baseM : Fin m := c ⟨v₀, hv₀⟩
  let color : V → Fin m := fun v =>
    if hv : v ∈ T.carrier then c ⟨v, hv⟩ else baseM
  have hcolor : ∀ ⦃u v : V⦄,
      u ∈ T.carrier \ T.precolored →
      v ∈ T.carrier \ T.precolored →
      G.Adj u v → color u ≠ color v := by
    intro u v hu hv huv
    have huC := (Finset.mem_sdiff.mp hu).1
    have hvC := (Finset.mem_sdiff.mp hv).1
    simpa [color, huC, hvC] using
      (c.valid (show H.Adj ⟨u, huC⟩ ⟨v, hvC⟩ from huv))
  by_contra hbound
  change ¬ n < m + 6 * k at hbound
  have hpalette : m + 6 * k ≤ n := by omega
  have hn : 0 < n := by omega
  let base : Fin n := ⟨0, hn⟩
  have hext := T.extends_of_colorable_remainder G base k m hk ha
    hshort color hcolor (by simpa using hpalette)
  exact ho hext

/-- Additive Girão--Narayanan chromatic connectivity theorem. -/
theorem exists_chromatic_connected_induced
    (G : SimpleGraph V) (k : ℕ)
    (hk : 0 < k) (hχ : 7 * k ≤ chromatic G) :
    ∃ U : Finset V,
      VertexConnected (G.induce (U : Set V)) k ∧
      chromatic G ≤ chromatic (G.induce (U : Set V)) + 6 * k := by
  classical
  obtain ⟨U, T, hlarge, hcarrier, ha, ho, hmin, hshort⟩ :=
    exists_large_minimal_obstruction G k hk hχ
  refine ⟨U, ?_, ?_⟩
  · rw [← hcarrier]
    exact connected_of_minimal_obstruction G k (chromatic G - 1)
      hk T (by simpa [hcarrier] using hlarge) ha ho hshort
      (by simpa [hcarrier] using hmin)
  · have hnonempty : T.carrier.Nonempty := by
      rw [hcarrier]
      exact Finset.card_pos.mp (by omega)
    have hbound := chromatic_bound_of_obstructing_template G k
      (chromatic G - 1) hk T hnonempty ha ho hshort
    rw [hcarrier] at hbound
    omega
end HadwigerLean
