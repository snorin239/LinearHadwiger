import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Branch-set graph minors

`MinorModel H G` is a model of `H` in `G` by pairwise disjoint, nonempty,
connected induced branch sets.  For every edge of `H`, an edge of `G` joins
the corresponding branch sets.  Extra edges of `G` are allowed, as required
for the ordinary (non-induced) graph-minor relation.
-/

namespace HadwigerLean

universe u v w

/-- A branch-set model of `H` as a minor of `G`. -/
structure MinorModel {W : Type u} {V : Type v} (H : SimpleGraph W) (G : SimpleGraph V) where
  branch : W → Set V
  connected : ∀ w, (G.induce (branch w)).Connected
  disjoint : Pairwise fun w w' => Disjoint (branch w) (branch w')
  adjacent : ∀ ⦃w w'⦄, H.Adj w w' →
    ∃ x ∈ branch w, ∃ y ∈ branch w', G.Adj x y

/-- A complete graph of order `n` has a branch-set model in `G`. -/
def HasCliqueMinor {V : Type v} (G : SimpleGraph V) (n : ℕ) : Prop :=
  Nonempty (MinorModel (SimpleGraph.completeGraph (Fin n)) G)

/-- The largest order of a complete minor, on a finite vertex type. -/
noncomputable def cliqueMinorNumber {V : Type v} [Fintype V] (G : SimpleGraph V) : ℕ :=
  by
    classical
    exact (Finset.range (Fintype.card V + 1)).sup fun n =>
      if HasCliqueMinor G n then n else 0

namespace MinorModel

variable {W : Type u} {V : Type v} {H : SimpleGraph W} {G G' : SimpleGraph V}
/-- A chosen representative from each nonempty branch set. -/
noncomputable def representative (M : MinorModel H G) (w : W) : V :=
  (M.connected w).nonempty.some.val

theorem representative_mem (M : MinorModel H G) (w : W) :
    M.representative w ∈ M.branch w :=
  (M.connected w).nonempty.some.property

/-- Distinct branch sets have distinct representatives. -/
theorem representative_injective (M : MinorModel H G) :
    Function.Injective M.representative := by
  intro w w' heq
  by_contra hne
  exact (Set.disjoint_left.mp (M.disjoint hne)) (M.representative_mem w)
    (heq ▸ M.representative_mem w')

/-- A minor cannot have more vertices than its host. -/
theorem card_le (M : MinorModel H G) [Fintype W] [Fintype V] :
    Fintype.card W ≤ Fintype.card V :=
  Fintype.card_le_of_injective M.representative M.representative_injective

/-- Every graph is a minor of itself, using singleton branch sets. -/
def refl (G : SimpleGraph V) : MinorModel G G where
  branch := fun x => {x}
  connected := by
    intro x
    simp
  disjoint := by
    intro x y hxy
    simpa using hxy
  adjacent := by
    intro x y hxy
    exact ⟨x, by simp, y, by simp, hxy⟩

/-- A minor model remains valid when edges are added to the host graph. -/
def mono (M : MinorModel H G) (h : G ≤ G') : MinorModel H G' where
  branch := M.branch
  connected := fun w => M.connected w |>.mono (by
    intro x y hxy
    exact h hxy)
  disjoint := M.disjoint
  adjacent := by
    intro w w' hww'
    obtain ⟨x, hx, y, hy, hxy⟩ := M.adjacent hww'
    exact ⟨x, hx, y, hy, h hxy⟩

/-- Injective graph homomorphisms carry branch-set models to the target. -/
def map {X : Type w} {J : SimpleGraph X} (M : MinorModel H G) (f : G →g J)
    (hf : Function.Injective f) : MinorModel H J where
  branch := fun w => f '' M.branch w
  connected := by
    intro w
    let φ : (G.induce (M.branch w)) →g (J.induce (f '' M.branch w)) := {
      toFun := fun x => ⟨f x.1, ⟨x.1, x.2, rfl⟩⟩
      map_rel' := by
        intro x y hxy
        exact f.map_rel hxy
    }
    apply (M.connected w).map φ
    rintro ⟨z, hz⟩
    rcases hz with ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  disjoint := by
    intro w w' hne
    apply Set.disjoint_left.mpr
    intro z hz hz'
    rcases hz with ⟨x, hx, rfl⟩
    rcases hz' with ⟨y, hy, hyx⟩
    have hxy : x = y := hf hyx.symm
    subst y
    exact (Set.disjoint_left.mp (M.disjoint hne)) hx hy
  adjacent := by
    intro w w' hww'
    obtain ⟨x, hx, y, hy, hxy⟩ := M.adjacent hww'
    exact ⟨f x, ⟨x, hx, rfl⟩, f y, ⟨y, hy, rfl⟩, f.map_rel hxy⟩

private def branchUnion (N : MinorModel H G) (s : Set W) : Set V :=
  {x | ∃ i ∈ s, x ∈ N.branch i}

private theorem connected_branchUnion (N : MinorModel H G) (s : Set W)
    (hs : (H.induce s).Connected) : (G.induce (branchUnion N s)).Connected := by
  let U := branchUnion N s
  have sub (i : W) (hi : i ∈ s) : N.branch i ⊆ U :=
    fun x hx => ⟨i, hi, hx⟩
  have within (i : W) (hi : i ∈ s) (x y : V)
      (hx : x ∈ N.branch i) (hy : y ∈ N.branch i) :
      (G.induce U).Reachable ⟨x, sub i hi hx⟩ ⟨y, sub i hi hy⟩ := by
    exact ((N.connected i).preconnected ⟨x, hx⟩ ⟨y, hy⟩).map
      (G.induceHomOfLE (sub i hi)).toHom
  have cross (i j : W) (hi : i ∈ s) (hj : j ∈ s) (hij : H.Adj i j)
      (x y : V) (hx : x ∈ N.branch i) (hy : y ∈ N.branch j) :
      (G.induce U).Reachable ⟨x, sub i hi hx⟩ ⟨y, sub j hj hy⟩ := by
    obtain ⟨a, ha, b, hb, hab⟩ := N.adjacent hij
    have e : (G.induce U).Adj ⟨a, sub i hi ha⟩ ⟨b, sub j hj hb⟩ := hab
    exact ((within i hi x a hx ha).trans e.reachable).trans (within j hj b y hb hy)
  have walkLift : ∀ {i j : s}, (H.induce s).Walk i j →
      ∀ (x : V) (hx : x ∈ N.branch i) (y : V) (hy : y ∈ N.branch j),
        (G.induce U).Reachable ⟨x, sub i i.property hx⟩ ⟨y, sub j j.property hy⟩ := by
    intro i j p
    induction p with
    | @nil a =>
      intro x hx y hy
      exact within a.1 a.property x y hx hy
    | @cons a k _ h p ih =>
      intro x hx y hy
      let z := N.representative k.1
      have hz : z ∈ N.branch k.1 := N.representative_mem k.1
      exact (cross a.1 k.1 a.property k.property h x z hx hz).trans
        (ih z hz y hy)
  haveI : Nonempty U := by
    obtain ⟨i, hi⟩ := hs.nonempty
    obtain ⟨x, hx⟩ := (N.connected i).nonempty
    exact ⟨⟨x, ⟨i, hi, hx⟩⟩⟩
  refine ⟨?_⟩
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨i, hi, hxi⟩ := hx
  obtain ⟨j, hj, hyj⟩ := hy
  exact (hs ⟨i, hi⟩ ⟨j, hj⟩).elim
    (fun p => walkLift p x hxi y hyj)

/-- Composition of branch-set minor models. -/
def comp {X : Type w} {K : SimpleGraph X}
    (M : MinorModel K H) (N : MinorModel H G) : MinorModel K G where
  branch := fun k => branchUnion N (M.branch k)
  connected := fun k => connected_branchUnion N (M.branch k) (M.connected k)
  disjoint := by
    intro k k' hkk'
    apply Set.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨i, hi, hxi⟩ := hx
    obtain ⟨j, hj, hxj⟩ := hx'
    have hij : i ≠ j := by
      intro h
      subst j
      exact (Set.disjoint_left.mp (M.disjoint hkk')) hi hj
    exact (Set.disjoint_left.mp (N.disjoint hij)) hxi hxj
  adjacent := by
    intro k k' hkk'
    obtain ⟨i, hi, j, hj, hij⟩ := M.adjacent hkk'
    obtain ⟨x, hx, y, hy, hxy⟩ := N.adjacent hij
    exact ⟨x, ⟨i, hi, hx⟩, y, ⟨j, hj, hy⟩, hxy⟩


end MinorModel

/-- A complete minor has at most as many branch sets as host vertices. -/
theorem hasCliqueMinor_card_le {V : Type v} [Fintype V] {G : SimpleGraph V}
    {n : ℕ} (h : HasCliqueMinor G n) : n ≤ Fintype.card V := by
  obtain ⟨M⟩ := h
  simpa using M.card_le

/-- Every modeled clique order lies below the complete-minor number. -/
theorem hasCliqueMinor_le_cliqueMinorNumber {V : Type v} [Fintype V]
    {G : SimpleGraph V} {n : ℕ} (h : HasCliqueMinor G n) :
    n ≤ cliqueMinorNumber G := by
  classical
  have hn : n ∈ Finset.range (Fintype.card V + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hasCliqueMinor_card_le h))
  simpa [cliqueMinorNumber, h] using
    (Finset.le_sup (f := fun m => if HasCliqueMinor G m then m else 0) hn)

/-- The number of branch sets is bounded by the host order. -/
theorem cliqueMinorNumber_le_card {V : Type v} [Fintype V]
    (G : SimpleGraph V) : cliqueMinorNumber G ≤ Fintype.card V := by
  classical
  unfold cliqueMinorNumber
  refine Finset.sup_le fun n hn => ?_
  split_ifs with hminor
  · exact hasCliqueMinor_card_le hminor
  · exact Nat.zero_le _

/-- Any construction that lifts clique models also preserves the minor number. -/
theorem cliqueMinorNumber_le_of_transfer {V : Type v} {W : Type u}
    [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (transfer : ∀ n, HasCliqueMinor H n → HasCliqueMinor G n) :
    cliqueMinorNumber H ≤ cliqueMinorNumber G := by
  classical
  unfold cliqueMinorNumber
  refine Finset.sup_le fun n hn => ?_
  split_ifs with hminor
  · exact hasCliqueMinor_le_cliqueMinorNumber (transfer n hminor)
  · exact Nat.zero_le _


/-- The branch-set graph-minor relation. -/
def IsMinor {W : Type u} {V : Type v}
    (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  Nonempty (MinorModel H G)

theorem IsMinor.refl {V : Type v} (G : SimpleGraph V) : IsMinor G G :=
  ⟨MinorModel.refl G⟩

/-- Branch-set graph minors compose. -/
theorem IsMinor.trans {X : Type w} {W : Type u} {V : Type v}
    {K : SimpleGraph X} {H : SimpleGraph W} {G : SimpleGraph V}
    (hKH : IsMinor K H) (hHG : IsMinor H G) : IsMinor K G := by
  obtain ⟨M⟩ := hKH
  obtain ⟨N⟩ := hHG
  exact ⟨M.comp N⟩

/-- A clique model in a minor lifts to a clique model in the host. -/
theorem hasCliqueMinor_of_minor {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V} {n : ℕ}
    (hHG : IsMinor H G) (hn : HasCliqueMinor H n) : HasCliqueMinor G n :=
  IsMinor.trans hn hHG

/-- The complete-minor number is monotone under graph minors. -/
theorem cliqueMinorNumber_mono_minor {W : Type u} {V : Type v}
    [Fintype W] [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    (hHG : IsMinor H G) : cliqueMinorNumber H ≤ cliqueMinorNumber G :=
  cliqueMinorNumber_le_of_transfer (fun _ hn => hasCliqueMinor_of_minor hHG hn)

/-- Every graph contains the empty complete graph as a minor. -/
theorem hasCliqueMinor_zero {V : Type v} (G : SimpleGraph V) :
    HasCliqueMinor G 0 := by
  refine ⟨{ branch := Fin.elim0, connected := ?_, disjoint := ?_, adjacent := ?_ }⟩
  · intro i
    exact i.elim0
  · intro i
    exact i.elim0
  · intro i
    exact i.elim0

/-- A nonempty graph contains a one-vertex complete minor. -/
theorem hasCliqueMinor_one {V : Type v} [Nonempty V] (G : SimpleGraph V) :
    HasCliqueMinor G 1 := by
  classical
  let x : V := Classical.choice inferInstance
  refine ⟨{ branch := fun _ => {x}, connected := ?_, disjoint := ?_, adjacent := ?_ }⟩
  · intro i
    simp
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  · intro i j hij
    exact (hij.ne (Subsingleton.elim i j)).elim

/-- The finite supremum defining the complete-minor number is attained. -/
theorem hasCliqueMinor_cliqueMinorNumber {V : Type v} [Fintype V]
    (G : SimpleGraph V) : HasCliqueMinor G (cliqueMinorNumber G) := by
  classical
  let s := Finset.range (Fintype.card V + 1)
  have hs : s.Nonempty := ⟨0, by simp [s]⟩
  obtain ⟨n, hn, hsup⟩ :=
    Finset.exists_mem_eq_sup s hs (fun m => if HasCliqueMinor G m then m else 0)
  by_cases hminor : HasCliqueMinor G n
  · have heq : cliqueMinorNumber G = n := by
      simpa [cliqueMinorNumber, s, hminor] using hsup
    rwa [heq]
  · have heq : cliqueMinorNumber G = 0 := by
      simpa [cliqueMinorNumber, s, hminor] using hsup
    rw [heq]
    exact hasCliqueMinor_zero G

/-- On a nonempty vertex type, the complete-minor number is positive. -/
theorem cliqueMinorNumber_pos {V : Type v} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) : 0 < cliqueMinorNumber G := by
  have h := hasCliqueMinor_le_cliqueMinorNumber (hasCliqueMinor_one G)
  omega

/-- An injective graph homomorphism preserves every complete minor. -/
theorem hasCliqueMinor_map {V : Type v} {W : Type u}
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G →g H)
    (hf : Function.Injective f) {n : ℕ}
    (hn : HasCliqueMinor G n) : HasCliqueMinor H n := by
  obtain ⟨M⟩ := hn
  exact ⟨M.map f hf⟩

/-- The complete-minor number is monotone under injective graph homomorphisms. -/
theorem cliqueMinorNumber_map {V : Type v} {W : Type u}
    [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) :
    cliqueMinorNumber G ≤ cliqueMinorNumber H :=
  cliqueMinorNumber_le_of_transfer (fun _ hn => hasCliqueMinor_map f hf hn)

/-- Induced subgraphs have no larger complete minor than the original graph. -/
theorem cliqueMinorNumber_induce {V : Type v} [Fintype V]
    (G : SimpleGraph V) (s : Set V) [Fintype s] :
    cliqueMinorNumber (G.induce s) ≤ cliqueMinorNumber G := by
  let e : G.induce s ↪g G := SimpleGraph.Embedding.induce s
  exact cliqueMinorNumber_map e.toHom e.injective

/-- A complete graph has complete-minor number equal to its order. -/
theorem cliqueMinorNumber_completeGraph (n : ℕ) :
    cliqueMinorNumber (SimpleGraph.completeGraph (Fin n)) = n := by
  have hlow : n ≤ cliqueMinorNumber (SimpleGraph.completeGraph (Fin n)) :=
    hasCliqueMinor_le_cliqueMinorNumber ⟨MinorModel.refl _⟩
  have hhigh : cliqueMinorNumber (SimpleGraph.completeGraph (Fin n)) ≤ n := by
    simpa using cliqueMinorNumber_le_card (SimpleGraph.completeGraph (Fin n))
  exact Nat.le_antisymm hhigh hlow

/-- The minor relation is monotone in the host graph's edge set. -/
theorem hasCliqueMinor_mono {V : Type v} {G G' : SimpleGraph V} (h : G ≤ G')
    {n : ℕ} (hn : HasCliqueMinor G n) : HasCliqueMinor G' n := by
  obtain ⟨M⟩ := hn
  exact ⟨M.mono h⟩

/-- The complete-minor number is monotone in the host graph's edge set. -/
theorem cliqueMinorNumber_mono {V : Type v} [Fintype V] {G G' : SimpleGraph V}
    (h : G ≤ G') : cliqueMinorNumber G ≤ cliqueMinorNumber G' := by
  classical
  unfold cliqueMinorNumber
  refine Finset.sup_le fun n hn => ?_
  split_ifs with hminor
  · simpa [hasCliqueMinor_mono h hminor] using
      (Finset.le_sup (f := fun m => if HasCliqueMinor G' m then m else 0) hn)
  · exact Nat.zero_le _

/-- The empty graph has complete-minor number zero. -/
@[simp] theorem cliqueMinorNumber_isEmpty {V : Type v} [Fintype V] [IsEmpty V]
    (G : SimpleGraph V) : cliqueMinorNumber G = 0 := by
  classical
  simp [cliqueMinorNumber, Fintype.card_eq_zero]

end HadwigerLean
