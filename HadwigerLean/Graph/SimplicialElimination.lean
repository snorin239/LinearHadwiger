import HadwigerLean.Graph.Finite

/-!
# Simplicial elimination and clique colorability

The hypothesis says that every nonempty induced vertex set has a vertex whose
neighbors within that set form a clique.  Greedy elimination then colors the
graph with as many colors as its largest clique.
-/

namespace HadwigerLean

variable {V : Type*} [Fintype V]

/-- A vertex is simplicial within a specified induced vertex set. -/
def IsSimplicialOn (G : SimpleGraph V) (s : Finset V) (v : V) : Prop :=
  ∀ ⦃x y : V⦄, x ∈ s → y ∈ s → G.Adj v x → G.Adj v y → x ≠ y → G.Adj x y

omit [Fintype V] in
/-- A vertex is simplicial when all of its neighbors in the specified set lie
inside a clique. -/
theorem IsSimplicialOn.of_neighbor_subset_clique
    (G : SimpleGraph V) (s K : Finset V) (v : V)
    (hK : G.IsClique (K : Set V))
    (hN : ∀ x ∈ s, G.Adj v x → x ∈ K) : IsSimplicialOn G s v := by
  intro x y hx hy hvx hvy hxy
  exact hK (hN x hx hvx) (hN y hy hvy) hxy
/-- Every nonempty induced vertex set contains a simplicial vertex. -/
def HasSimplicialElimination (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, IsSimplicialOn G s v

omit [Fintype V] in
private theorem colorable_induce_of_simplicial_elimination
    (G : SimpleGraph V) (n : ℕ) (helim : HasSimplicialElimination G)
    (hclique : ∀ t : Finset V, G.IsClique (t : Set V) → t.card ≤ n)
    (s : Finset V) : (G.induce (s : Set V)).Colorable n := by
  classical
  refine Finset.strongInductionOn (p := fun s => (G.induce (s : Set V)).Colorable n) s ?_
  intro s ih
  by_cases hs : s.Nonempty
  · obtain ⟨v, hv, hsim⟩ := helim s hs
    let t : Finset V := s.erase v
    have ht : t ⊂ s := Finset.erase_ssubset hv
    let C : (G.induce (t : Set V)).Coloring (Fin n) :=
      Classical.choice (ih t ht)
    let N : Finset V := t.filter (G.Adj v)
    have hNs {x : V} (hx : x ∈ N) : x ∈ s := by
      exact (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).2
    have hNa {x : V} (hx : x ∈ N) : G.Adj v x :=
      (Finset.mem_filter.mp hx).2
    have hnv : v ∉ N := by
      intro h
      exact G.irrefl (hNa h)
    have hNclique : G.IsClique ((insert v N : Finset V) : Set V) := by
      intro x hx y hy hxy
      change x ∈ insert v N at hx
      change y ∈ insert v N at hy
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rcases Finset.mem_insert.mp hy with rfl | hy
        · exact False.elim (hxy rfl)
        · exact hNa hy
      · rcases Finset.mem_insert.mp hy with rfl | hy
        · exact (hNa hx).symm
        · exact hsim (hNs hx) (hNs hy) (hNa hx) (hNa hy) hxy
    have hNcard : N.card < n := by
      have h := hclique (insert v N) hNclique
      rw [Finset.card_insert_of_notMem hnv] at h
      omega
    let neighborColor : N → Fin n := fun x =>
      C ⟨x.1, (Finset.mem_filter.mp x.2).1⟩
    let used : Finset (Fin n) := Finset.univ.image neighborColor
    have hused : used.card ≤ N.card := by
      simpa [used] using
        (Finset.card_image_le (s := (Finset.univ : Finset N)) (f := neighborColor))
    have hmissing : ∃ a : Fin n, a ∉ used := by
      by_contra h
      push Not at h
      have hsubset : (Finset.univ : Finset (Fin n)) ⊆ used := by
        intro a _
        exact h a
      have hcard := Finset.card_le_card hsubset
      simp only [Finset.card_univ, Fintype.card_fin] at hcard
      omega
    obtain ⟨a, ha⟩ := hmissing
    let color : {x : V // x ∈ (s : Set V)} → Fin n := fun x =>
      if hx : x.1 = v then a
      else C ⟨x.1, Finset.mem_erase.mpr ⟨hx, x.2⟩⟩
    refine ⟨SimpleGraph.Coloring.mk color ?_⟩
    intro x y hxy
    change G.Adj x.1 y.1 at hxy
    by_cases hx : x.1 = v
    · by_cases hy : y.1 = v
      · rw [hx, hy] at hxy
        exact False.elim (G.irrefl hxy)
      · have hyN : y.1 ∈ N := by
          apply Finset.mem_filter.mpr
          constructor
          · exact Finset.mem_erase.mpr ⟨hy, y.2⟩
          · simpa only [hx] using hxy
        have hcy : C ⟨y.1, (Finset.mem_filter.mp hyN).1⟩ ∈ used := by
          apply Finset.mem_image.mpr
          exact ⟨⟨y.1, hyN⟩, Finset.mem_univ _, rfl⟩
        intro heq
        have heq' : a = C ⟨y.1, (Finset.mem_filter.mp hyN).1⟩ := by
          simpa only [color, dif_pos hx, dif_neg hy] using heq
        exact ha (heq' ▸ hcy)
    · by_cases hy : y.1 = v
      · have hxN : x.1 ∈ N := by
          apply Finset.mem_filter.mpr
          constructor
          · exact Finset.mem_erase.mpr ⟨hx, x.2⟩
          · simpa only [hy] using hxy.symm
        have hcx : C ⟨x.1, (Finset.mem_filter.mp hxN).1⟩ ∈ used := by
          apply Finset.mem_image.mpr
          exact ⟨⟨x.1, hxN⟩, Finset.mem_univ _, rfl⟩
        intro heq
        have heq' : C ⟨x.1, (Finset.mem_filter.mp hxN).1⟩ = a := by
          simpa only [color, dif_neg hx, dif_pos hy] using heq
        exact ha (heq' ▸ hcx)
      · have hxy' : (G.induce (t : Set V)).Adj
            ⟨x.1, Finset.mem_erase.mpr ⟨hx, x.2⟩⟩
            ⟨y.1, Finset.mem_erase.mpr ⟨hy, y.2⟩⟩ := hxy
        simpa only [color, dif_neg hx, dif_neg hy] using C.valid hxy'
  · have hEmpty : IsEmpty {x : V // x ∈ (s : Set V)} := by
      constructor
      intro x
      exact hs ⟨x.1, x.2⟩
    letI := hEmpty
    exact SimpleGraph.Colorable.of_isEmpty n

/-- A finite graph with a simplicial elimination property is colorable by its
clique number. -/
theorem HasSimplicialElimination.colorable_cliqueNum
    {G : SimpleGraph V} (h : HasSimplicialElimination G) :
    G.Colorable G.cliqueNum := by
  classical
  let C : (G.induce ((Finset.univ : Finset V) : Set V)).Coloring (Fin G.cliqueNum) :=
    Classical.choice <| colorable_induce_of_simplicial_elimination G G.cliqueNum h
      (fun t ht => ht.card_le_cliqueNum) Finset.univ
  refine ⟨SimpleGraph.Coloring.mk (fun v => C ⟨v, Finset.mem_univ v⟩) ?_⟩
  intro v w hvw
  exact C.valid hvw

/-- The usual chromatic number equals the clique number for a graph with
simplicial elimination. -/
theorem HasSimplicialElimination.chromatic_eq_cliqueNum
    {G : SimpleGraph V} (h : HasSimplicialElimination G) :
    chromatic G = G.cliqueNum := by
  apply Nat.le_antisymm
  · exact (chromatic_le_iff_colorable G G.cliqueNum).2 h.colorable_cliqueNum
  · obtain ⟨s, hs⟩ := G.maximumClique_exists
    rw [← G.maximumClique_card_eq_cliqueNum s hs]
    exact hs.isClique.card_le_of_colorable G.colorable_chromaticNumber_of_fintype

omit [Fintype V] in
/-- Simplicial elimination is invariant under graph isomorphism. -/
theorem HasSimplicialElimination.of_iso {W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (h : HasSimplicialElimination G) :
    HasSimplicialElimination H := by
  classical
  intro s hs
  let t : Finset V := s.image e.symm
  have ht : t.Nonempty := by
    obtain ⟨w, hw⟩ := hs
    exact ⟨e.symm w, Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩
  obtain ⟨v, hv, hsim⟩ := h t ht
  have hvs : e v ∈ s := by
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    have hwev : w = e v := by
      calc
        w = e (e.symm w) := (e.apply_symm_apply w).symm
        _ = e v := congrArg e hwv
    exact hwev ▸ hw
  refine ⟨e v, hvs, ?_⟩
  intro x y hx hy hvx hvy hxy
  have htx : e.symm x ∈ t := Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hty : e.symm y ∈ t := Finset.mem_image.mpr ⟨y, hy, rfl⟩
  have hvx' : G.Adj v (e.symm x) := by
    apply e.map_rel_iff.mp
    simpa using hvx
  have hvy' : G.Adj v (e.symm y) := by
    apply e.map_rel_iff.mp
    simpa using hvy
  have hne : e.symm x ≠ e.symm y := by
    intro heq
    exact hxy (e.symm.injective heq)
  have hxy' := hsim htx hty hvx' hvy' hne
  have hadj : H.Adj (e (e.symm x)) (e (e.symm y)) := e.map_rel_iff.mpr hxy'
  simpa using hadj
omit [Fintype V] in
/-- Restricting to an induced vertex set preserves simplicial elimination. -/
theorem HasSimplicialElimination.induce {G : SimpleGraph V}
    (h : HasSimplicialElimination G) (S : Set V) :
    HasSimplicialElimination (G.induce S) := by
  classical
  intro s hs
  let t : Finset V := s.image Subtype.val
  have ht : t.Nonempty := by
    obtain ⟨w, hw⟩ := hs
    exact ⟨w.1, Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩
  obtain ⟨v, hv, hsim⟩ := h t ht
  obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
  subst v
  refine ⟨w, hw, ?_⟩
  intro x y hx hy hwx hwy hxy
  have htx : x.1 ∈ t := Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hty : y.1 ∈ t := Finset.mem_image.mpr ⟨y, hy, rfl⟩
  have hne : x.1 ≠ y.1 := by
    intro heq
    exact hxy (Subtype.ext heq)
  exact hsim htx hty hwx hwy hne
/-- Adding a simplicial vertex to a graph with simplicial elimination preserves
simplicial elimination. The remaining graph is represented as an induced graph
on the vertices different from `v`. -/
theorem HasSimplicialElimination.of_simplicial_vertex
    (G : SimpleGraph V) (v : V)
    (hv : IsSimplicialOn G Finset.univ v)
    (hrest : HasSimplicialElimination (G.induce {x : V | x ≠ v})) :
    HasSimplicialElimination G := by
  classical
  intro s hs
  by_cases hvs : v ∈ s
  · refine ⟨v, hvs, ?_⟩
    intro x y hx hy hvx hvy hxy
    exact hv (Finset.mem_univ x) (Finset.mem_univ y) hvx hvy hxy
  · let t : Finset {x : V // x ≠ v} := Finset.univ.filter (fun x => x.1 ∈ s)
    have ht : t.Nonempty := by
      obtain ⟨x, hx⟩ := hs
      have hxne : x ≠ v := by
        intro he
        exact hvs (he ▸ hx)
      exact ⟨⟨x, hxne⟩, by simp [t, hx]⟩
    obtain ⟨w, hw, hsim⟩ := hrest t ht
    have hws : w.1 ∈ s := (Finset.mem_filter.mp hw).2
    refine ⟨w.1, hws, ?_⟩
    intro x y hx hy hwx hwy hxy
    have hxne : x ≠ v := by
      intro he
      exact hvs (he ▸ hx)
    have hyne : y ≠ v := by
      intro he
      exact hvs (he ▸ hy)
    have htx : (⟨x, hxne⟩ : {x : V // x ≠ v}) ∈ t := by simp [t, hx]
    have hty : (⟨y, hyne⟩ : {x : V // x ≠ v}) ∈ t := by simp [t, hy]
    have hne : (⟨x, hxne⟩ : {x : V // x ≠ v}) ≠ ⟨y, hyne⟩ := by
      intro he
      exact hxy (congrArg Subtype.val he)
    exact hsim htx hty hwx hwy hne
/-- Removing a finite set of globally simplicial vertices reduces the
elimination question to the induced graph on the remaining vertices. -/
theorem HasSimplicialElimination.of_simplicial_set
    (G : SimpleGraph V) (Z : Finset V)
    (hZ : ∀ z ∈ Z, IsSimplicialOn G Finset.univ z)
    (hrest : HasSimplicialElimination (G.induce {x : V | x ∉ Z})) :
    HasSimplicialElimination G := by
  classical
  intro s hs
  by_cases hmeet : ∃ z ∈ s, z ∈ Z
  · obtain ⟨z, hzs, hzZ⟩ := hmeet
    refine ⟨z, hzs, ?_⟩
    intro x y hx hy hzx hzy hxy
    exact hZ z hzZ (Finset.mem_univ x) (Finset.mem_univ y) hzx hzy hxy
  · let t : Finset {x : V // x ∉ Z} := Finset.univ.filter (fun x => x.1 ∈ s)
    have ht : t.Nonempty := by
      obtain ⟨x, hx⟩ := hs
      have hxZ : x ∉ Z := by
        intro hz
        exact hmeet ⟨x, hx, hz⟩
      exact ⟨⟨x, hxZ⟩, by simp [t, hx]⟩
    obtain ⟨w, hw, hsim⟩ := hrest t ht
    have hws : w.1 ∈ s := (Finset.mem_filter.mp hw).2
    refine ⟨w.1, hws, ?_⟩
    intro x y hx hy hwx hwy hxy
    have hxZ : x ∉ Z := by
      intro hz
      exact hmeet ⟨x, hx, hz⟩
    have hyZ : y ∉ Z := by
      intro hz
      exact hmeet ⟨y, hy, hz⟩
    have htx : (⟨x, hxZ⟩ : {x : V // x ∉ Z}) ∈ t := by simp [t, hx]
    have hty : (⟨y, hyZ⟩ : {x : V // x ∉ Z}) ∈ t := by simp [t, hy]
    have hne : (⟨x, hxZ⟩ : {x : V // x ∉ Z}) ≠ ⟨y, hyZ⟩ := by
      intro he
      exact hxy (congrArg Subtype.val he)
    exact hsim htx hty hwx hwy hne
end HadwigerLean
