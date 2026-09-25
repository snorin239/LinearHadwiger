import HadwigerLean.Graph.SetMenger

/-!
# Projecting paths through a vertex-split network

Every positive-capacity source--sink path alternates between the input and
output copy of an original vertex. The projection is a graph path and each
vertex it uses has a unit split arc in the network path.
-/

namespace HadwigerLean.SetMenger

universe v

variable {V : Type v} [Fintype V] [DecidableEq V]

/-- The four possible shapes of a positive-capacity arc. -/
theorem positive_split_arc (G : SimpleGraph V) (A B : Finset V)
    {x y : SplitVertex V} (h : 0 < splitCapacity G A B x y) :
    (∃ a ∈ A, x = splitSource ∧ y = splitIn a) ∨
    (∃ v, x = splitIn v ∧ y = splitOut v) ∨
    (∃ u v, G.Adj u v ∧ x = splitOut u ∧ y = splitIn v) ∨
    (∃ b ∈ B, x = splitOut b ∧ y = splitSink) := by
  classical
  cases x with
  | inl ox =>
    cases ox with
    | none =>
      cases y with
      | inl oy =>
        cases oy with
        | none => simp [splitCapacity] at h
        | some a =>
          simp only [splitCapacity] at h
          split_ifs at h with ha
          · exact Or.inl ⟨a, ha, rfl, rfl⟩
          · omega
      | inr oy => cases oy <;> simp [splitCapacity] at h
    | some u =>
      cases y with
      | inl oy => cases oy <;> simp [splitCapacity] at h
      | inr oy =>
        cases oy with
        | none => simp [splitCapacity] at h
        | some w =>
          simp only [splitCapacity] at h
          split_ifs at h with huw
          · subst w
            exact Or.inr (Or.inl ⟨u, rfl, rfl⟩)
          · omega
  | inr ox =>
    cases ox with
    | none => cases y <;> (rename_i oy; cases oy <;> simp [splitCapacity] at h)
    | some u =>
      cases y with
      | inl oy =>
        cases oy with
        | none => simp [splitCapacity] at h
        | some w =>
          simp only [splitCapacity] at h
          split_ifs at h with huw
          · exact Or.inr (Or.inr (Or.inl ⟨u, w, huw, rfl, rfl⟩))
          · omega
      | inr oy =>
        cases oy with
        | none =>
          simp only [splitCapacity] at h
          split_ifs at h with huB
          · exact Or.inr (Or.inr (Or.inr ⟨u, huB, rfl, rfl⟩))
          · omega
        | some w => simp [splitCapacity] at h


theorem positive_into_splitOut (G : SimpleGraph V) (A B : Finset V)
    {u v : SplitVertex V} (h : 0 < splitCapacity G A B u v)
    {w : V} (hv : v = splitOut w) : u = splitIn w := by
  rcases positive_split_arc G A B h with h1 | h2 | h3 | h4
  · obtain ⟨a, _, hu, hv'⟩ := h1
    cases hv'.symm.trans hv
  · obtain ⟨x, hu, hv'⟩ := h2
    have hx : x = w := by simpa [splitOut] using hv'.symm.trans hv
    subst x
    exact hu
  · obtain ⟨x, y, _, _, hv'⟩ := h3
    cases hv'.symm.trans hv
  · obtain ⟨b, _, _, hv'⟩ := h4
    cases hv'.symm.trans hv

theorem no_reverse_split_unit_arc (G : SimpleGraph V) (A B : Finset V)
    (w : V) : ¬ 0 < splitCapacity G A B (splitOut w) (splitIn w) := by
  simp [splitCapacity, splitOut, splitIn]


/-- Visiting an output copy means the unit arc of that original vertex is
traversed once by the directed split path. -/
theorem delta_split_unit_of_out_mem (G : SimpleGraph V) (A B : Finset V)
    {t : SplitVertex V} {l : List (SplitVertex V)}
    (p : FiniteFlow.DirectedSimplePath
      (fun x y => 0 < splitCapacity G A B x y) splitSource t l)
    (w : V) (hw : splitOut w ∈ l) :
    p.delta (splitIn w) (splitOut w) = 1 := by
  induction p with
  | nil =>
      simp [splitSource, splitOut] at hw
  | @snoc u v l p hres hfresh ih =>
      rcases List.mem_append.mp hw with hOld | hNew
      · have hvne : v ≠ splitOut w := by
          intro hv
          exact hfresh (hv ▸ hOld)
        have hforward : ¬ (splitIn w = u ∧ splitOut w = v) := by
          intro h
          exact hvne h.2.symm
        have hback : ¬ (splitIn w = v ∧ splitOut w = u) := by
          rintro ⟨hv, hu⟩
          have hbad : 0 < splitCapacity G A B (splitOut w) (splitIn w) := by
            simpa only [hu, hv] using hres
          exact no_reverse_split_unit_arc G A B w hbad
        simpa [FiniteFlow.DirectedSimplePath.delta, hforward, hback] using
          ih hOld
      · have hv : v = splitOut w := by simpa using (List.mem_singleton.mp hNew).symm
        subst v
        have hu : u = splitIn w :=
          positive_into_splitOut G A B hres rfl
        subst u
        have hzero : p.delta (splitIn w) (splitOut w) = 0 :=
          p.delta_right_zero hfresh
        simp only [FiniteFlow.DirectedSimplePath.delta]
        rw [hzero]
        simp [splitIn, splitOut]


private inductive ProjectionState (G : SimpleGraph V) (A B : Finset V) :
    SplitVertex V → List (SplitVertex V) → Prop where
  | source {l} : ProjectionState G A B splitSource l
  | incoming {l a v} (ha : a ∈ A) (w : G.Walk a v)
      (hvertices : ∀ x ∈ w.support, x = v ∨ splitOut x ∈ l) :
      ProjectionState G A B (splitIn v) l
  | outgoing {l a v} (ha : a ∈ A) (w : G.Walk a v)
      (hvertices : ∀ x ∈ w.support, splitOut x ∈ l) :
      ProjectionState G A B (splitOut v) l
  | sink {l a b} (ha : a ∈ A) (hb : b ∈ B) (w : G.Walk a b)
      (hvertices : ∀ x ∈ w.support, splitOut x ∈ l) :
      ProjectionState G A B splitSink l

private theorem projected_state (G : SimpleGraph V) (A B : Finset V)
    {t : SplitVertex V} {l : List (SplitVertex V)}
    (p : FiniteFlow.DirectedSimplePath
      (fun x y => 0 < splitCapacity G A B x y) splitSource t l) :
    ProjectionState G A B t l := by
  induction p with
  | nil => exact .source
  | @snoc u v l p hres hfresh ih =>
      rcases positive_split_arc G A B hres with hstart | hunit | hedge | hend
      · obtain ⟨a, ha, hu, hv⟩ := hstart
        subst u
        subst v
        apply ProjectionState.incoming ha (SimpleGraph.Walk.nil : G.Walk a a)
        intro x hx
        left
        simpa using hx
      · obtain ⟨z, hu, hv⟩ := hunit
        subst u
        subst v
        cases ih with
        | incoming ha w hvertices =>
            apply ProjectionState.outgoing ha w
            intro x hx
            rcases hvertices x hx with hlast | hused
            · subst x
              simp
            · exact List.mem_append.mpr (Or.inl hused)
      · obtain ⟨z, w, hzw, hu, hv⟩ := hedge
        subst u
        subst v
        cases ih with
        | outgoing ha pgraph hvertices =>
            apply ProjectionState.incoming ha (pgraph.concat hzw)
            intro x hx
            rw [SimpleGraph.Walk.support_concat] at hx
            rcases List.mem_append.mp hx with hused | hlast
            · right
              exact List.mem_append.mpr (Or.inl (hvertices x hused))
            · left
              simpa using hlast
      · obtain ⟨b, hb, hu, hv⟩ := hend
        subst u
        subst v
        cases ih with
        | outgoing ha pgraph hvertices =>
            apply ProjectionState.sink ha hb pgraph
            intro x hx
            exact List.mem_append.mpr (Or.inl (hvertices x hx))


/-- A positive-capacity path in the vertex-split network projects to an
A--B path in the original graph. Every projected vertex traverses its unit
split arc exactly once. -/
theorem capacityPath_project (G : SimpleGraph V) (A B : Finset V)
    (p : (splitNetwork G A B).CapacityPath) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ q : G.Path a b,
      ∀ v ∈ pathVertexSet q,
        p.2.delta (splitIn v) (splitOut v) = 1 := by
  have hs : ProjectionState G A B splitSink p.1 :=
    projected_state G A B p.2
  cases hs with
  | sink ha hb w hvertices =>
      refine ⟨_, ha, _, hb, w.toPath, ?_⟩
      intro v hv
      have hvw : v ∈ w.support :=
        w.support_toPath_subset_support hv
      exact delta_split_unit_of_out_mem G A B p.2 v
        (hvertices v hvw)

end HadwigerLean.SetMenger
