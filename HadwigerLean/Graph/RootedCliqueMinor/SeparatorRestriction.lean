import HadwigerLean.Graph.RootedCliqueMinor

/-!
# Restricting a clique minor across a separation

When each branch meets the right side of a separation, deleting the left
strict side and completing the boundary to a clique preserves the model.
This is the torso step in the rooted clique minor separator dichotomy.
-/

namespace HadwigerLean

universe u

namespace VertexSeparation

variable {V : Type u} [Fintype V] {J : SimpleGraph V}
  (S : VertexSeparation J)

/-- A vertex outside the right side belongs to the strict left side. -/
theorem strictLeft_of_not_right {x : V} (hx : x ∉ S.right) :
    x ∈ S.strictLeft := by
  have hcover : x ∈ S.left ∪ S.right := by rw [S.cover]; trivial
  rcases hcover with hl | hr
  · exact ⟨hl, hx⟩
  · exact (hx hr).elim

/-- A right-side neighbor of a vertex outside the right side lies on the
separator boundary. -/
theorem left_of_adj_not_right {x y : V}
    (hx : x ∉ S.right) (hy : y ∈ S.right) (hxy : J.Adj x y) :
    y ∈ S.left := by
  by_contra hyl
  exact S.no_cross (S.strictLeft_of_not_right hx).1 hx hy hyl hxy

/-- A connected branch meeting both sides also meets the boundary. -/
theorem connected_set_meets_separator (C : Set V)
    (hconn : (J.induce C).Connected)
    (hright : ∃ x ∈ C, x ∈ S.right)
    (houtside : ∃ x ∈ C, x ∉ S.right) :
    ∃ x ∈ C, x ∈ S.left ∧ x ∈ S.right := by
  by_contra hnone
  obtain ⟨a, haC, haR⟩ := houtside
  obtain ⟨b, hbC, hbR⟩ := hright
  let a' : C := ⟨a, haC⟩
  let b' : C := ⟨b, hbC⟩
  have stay : ∀ {x y : C}, (J.induce C).Walk x y →
      (x : V) ∉ S.right → (y : V) ∉ S.right := by
    intro x y p
    induction p with
    | nil => intro hx; exact hx
    | @cons x y z hxy p ih =>
      intro hx
      have hy : (y : V) ∉ S.right := by
        intro hyR
        have hyL := S.left_of_adj_not_right hx hyR hxy
        exact hnone ⟨y, y.property, hyL, hyR⟩
      exact ih hy
  exact (stay (hconn.preconnected a' b').some haR) hbR

/-- The right-side torso completes the common boundary to a clique. -/
def torso : SimpleGraph S.right :=
  completeRoots (J.induce S.right) {x : S.right | (x : V) ∈ S.left}

/-- Restricting a connected set to the right side remains connected in the
torso, because each excursion through the strict left side can be replaced by
an edge of the completed boundary clique. -/
theorem connected_restrict_torso (C : Set V)
    (hconn : (J.induce C).Connected)
    (hright : ∃ x ∈ C, x ∈ S.right) :
    ((S.torso).induce {x : S.right | (x : V) ∈ C}).Connected := by
  classical
  let D : Set S.right := {x | (x : V) ∈ C}
  let T : SimpleGraph S.right := S.torso
  have hanchor : ∃ c ∈ C, c ∈ S.right ∧
      ((∃ x ∈ C, x ∉ S.right) → c ∈ S.left) := by
    by_cases hout : ∃ x ∈ C, x ∉ S.right
    · obtain ⟨c, hcC, hcL, hcR⟩ := S.connected_set_meets_separator C hconn hright hout
      exact ⟨c, hcC, hcR, fun _ => hcL⟩
    · obtain ⟨c, hcC, hcR⟩ := hright
      exact ⟨c, hcC, hcR, fun h => (hout h).elim⟩
  obtain ⟨c, hcC, hcR, hcL⟩ := hanchor
  let anchor : D := ⟨⟨c, hcR⟩, hcC⟩
  let φ : C → D := fun x =>
    if hx : (x : V) ∈ S.right then ⟨⟨x, hx⟩, x.property⟩ else anchor
  have hstep : ∀ {x y : C}, (J.induce C).Adj x y →
      (T.induce D).Reachable (φ x) (φ y) := by
    intro x y hxy
    by_cases hx : (x : V) ∈ S.right
    · by_cases hy : (y : V) ∈ S.right
      · have he : T.Adj ⟨x, hx⟩ ⟨y, hy⟩ := Or.inl hxy
        have he' : (T.induce D).Adj (φ x) (φ y) := by
          change T.Adj (φ x).1 (φ y).1
          simpa [φ, hx, hy] using he
        exact he'.reachable
      · have hcLeft : c ∈ S.left := hcL ⟨y, y.property, hy⟩
        have hxLeft : (x : V) ∈ S.left :=
          S.left_of_adj_not_right hy hx hxy.symm
        by_cases hxc : (x : V) = c
        · have heq : φ x = φ y := by
            simp only [φ, dif_pos hx, dif_neg hy]
            exact Subtype.ext (Subtype.ext hxc)
          exact heq ▸ SimpleGraph.Reachable.refl _
        · have he : T.Adj ⟨x, hx⟩ ⟨c, hcR⟩ :=
            Or.inr ⟨hxLeft, hcLeft, fun h => hxc (congrArg Subtype.val h)⟩
          have he' : (T.induce D).Adj (φ x) (φ y) := by
            change T.Adj (φ x).1 (φ y).1
            simpa [φ, hx, hy, anchor] using he
          exact he'.reachable
    · by_cases hy : (y : V) ∈ S.right
      · have hcLeft : c ∈ S.left := hcL ⟨x, x.property, hx⟩
        have hyLeft : (y : V) ∈ S.left :=
          S.left_of_adj_not_right hx hy hxy
        by_cases hcy : c = (y : V)
        · have heq : φ x = φ y := by
            simp only [φ, dif_neg hx, dif_pos hy]
            exact Subtype.ext (Subtype.ext hcy)
          exact heq ▸ SimpleGraph.Reachable.refl _
        · have he : T.Adj ⟨c, hcR⟩ ⟨y, hy⟩ :=
            Or.inr ⟨hcLeft, hyLeft, fun h => hcy (congrArg Subtype.val h)⟩
          have he' : (T.induce D).Adj (φ x) (φ y) := by
            change T.Adj (φ x).1 (φ y).1
            simpa [φ, hx, hy, anchor] using he
          exact he'.reachable
      · have heq : φ x = φ y := by simp [φ, hx, hy]
        exact heq ▸ SimpleGraph.Reachable.refl _
  have lift : ∀ {x y : C}, (J.induce C).Walk x y →
      (T.induce D).Reachable (φ x) (φ y) := by
    intro x y p
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons x y z hxy p ih => exact (hstep hxy).trans ih
  haveI : Nonempty D := by
    obtain ⟨x, hxC, hxR⟩ := hright
    exact ⟨⟨⟨x, hxR⟩, hxC⟩⟩
  refine ⟨?_⟩
  intro x y
  let xC : C := ⟨x.1.1, x.property⟩
  let yC : C := ⟨y.1.1, y.property⟩
  have hφx : φ xC = x := by
    apply Subtype.ext
    apply Subtype.ext
    simp [φ, xC, x.1.property]
  have hφy : φ yC = y := by
    apply Subtype.ext
    apply Subtype.ext
    simp [φ, yC, y.1.property]
  simpa only [hφx, hφy] using lift (hconn.preconnected xC yC).some
/-- A minor model whose every branch meets the right shore restricts to a
minor model in the right-side torso. -/
def restrictMinorModel {W : Type*} {H : SimpleGraph W}
    (M : MinorModel H J)
    (hmeet : ∀ i, ∃ x ∈ M.branch i, x ∈ S.right) :
    MinorModel H S.torso where
  branch := fun i => {x : S.right | (x : V) ∈ M.branch i}
  connected := fun i => S.connected_restrict_torso (M.branch i) (M.connected i) (hmeet i)
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact (Set.disjoint_left.mp (M.disjoint hij)) hxi hxj
  adjacent := by
    intro i j hij
    obtain ⟨x, hxi, y, hyj, hxy⟩ := M.adjacent hij
    have hne : i ≠ j := hij.ne
    by_cases hxR : x ∈ S.right
    · by_cases hyR : y ∈ S.right
      · exact ⟨⟨x, hxR⟩, hxi, ⟨y, hyR⟩, hyj, Or.inl hxy⟩
      · obtain ⟨c, hcB, hcL, hcR⟩ :=
          S.connected_set_meets_separator (M.branch j) (M.connected j)
            (hmeet j) ⟨y, hyj, hyR⟩
        have hxL : x ∈ S.left := S.left_of_adj_not_right hyR hxR hxy.symm
        have hxc : x ≠ c := by
          intro heq
          subst c
          exact (Set.disjoint_left.mp (M.disjoint hne)) hxi hcB
        exact ⟨⟨x, hxR⟩, hxi, ⟨c, hcR⟩, hcB,
          Or.inr ⟨hxL, hcL, fun h => hxc (congrArg Subtype.val h)⟩⟩
    · obtain ⟨c, hcB, hcL, hcR⟩ :=
        S.connected_set_meets_separator (M.branch i) (M.connected i)
          (hmeet i) ⟨x, hxi, hxR⟩
      by_cases hyR : y ∈ S.right
      · have hyL : y ∈ S.left := S.left_of_adj_not_right hxR hyR hxy
        have hcy : c ≠ y := by
          intro heq
          subst y
          exact (Set.disjoint_left.mp (M.disjoint hne)) hcB hyj
        exact ⟨⟨c, hcR⟩, hcB, ⟨y, hyR⟩, hyj,
          Or.inr ⟨hcL, hyL, fun h => hcy (congrArg Subtype.val h)⟩⟩
      · obtain ⟨d, hdB, hdL, hdR⟩ :=
          S.connected_set_meets_separator (M.branch j) (M.connected j)
            (hmeet j) ⟨y, hyj, hyR⟩
        have hcd : c ≠ d := by
          intro heq
          subst d
          exact (Set.disjoint_left.mp (M.disjoint hne)) hcB hdB
        exact ⟨⟨c, hcR⟩, hcB, ⟨d, hdR⟩, hdB,
          Or.inr ⟨hcL, hdL, fun h => hcd (congrArg Subtype.val h)⟩⟩
/-- Completing a root set on the left does not create an edge across the
strict sides of the separation. -/
def completeLeftRoots (R : Set V) (hR : R ⊆ S.left) :
    VertexSeparation (completeRoots J R) where
  left := S.left
  right := S.right
  cover := S.cover
  no_cross := by
    intro x y hxL hxNR hyR hyNL hxy
    rcases hxy with hxy | ⟨_, hyRoot, _⟩
    · exact S.no_cross hxL hxNR hyR hyNL hxy
    · exact hyNL (hR hyRoot)

/-- If every branch of a model in the root-completed graph reaches the far
shore, its restriction is a clique model in the far shore with the separator
completed to a clique. -/
def restrictCompletedRootModel {W : Type*} {H : SimpleGraph W}
    (R : Set V) (hR : R ⊆ S.left)
    (M : MinorModel H (completeRoots J R))
    (hmeet : ∀ i, ∃ x ∈ M.branch i, x ∈ S.right) :
    MinorModel H
      (completeRoots (J.induce S.right) {x : S.right | (x : V) ∈ S.left}) := by
  let S' : VertexSeparation (completeRoots J R) := S.completeLeftRoots R hR
  have hmono : S'.torso ≤
      completeRoots (J.induce S.right) {x : S.right | (x : V) ∈ S.left} := by
    intro x y hxy
    rcases hxy with hxy | hxy
    · rcases hxy with hxy | ⟨hxR, hyR, hne⟩
      · exact Or.inl hxy
      · exact Or.inr ⟨hR hxR, hR hyR, fun heq => hne (congrArg Subtype.val heq)⟩
    · exact Or.inr hxy
  exact (S'.restrictMinorModel M hmeet).mono hmono
/-- If one clique branch lies strictly on the far shore, every other branch
must meet the far shore as well. -/
theorem cliqueBranches_meet_right (R : Set V) (hR : R ⊆ S.left)
    {r : ℕ}
    (M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots J R))
    (j : Fin (2 * r)) (hfar : M.branch j ⊆ S.strictRight) :
    ∀ i, ∃ x ∈ M.branch i, x ∈ S.right := by
  let S' : VertexSeparation (completeRoots J R) := S.completeLeftRoots R hR
  intro i
  by_cases hij : i = j
  · subst j
    obtain ⟨x, hx⟩ := (M.connected i).nonempty
    exact ⟨x, hx, (hfar hx).1⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := M.adjacent (by simpa using hij)
    have hyFar : y ∈ S'.strictRight := hfar hy
    by_contra hnone
    have hxNotR : x ∉ S'.right := by
      intro hxR
      exact hnone ⟨x, hx, hxR⟩
    exact (S'.no_cross' (S'.strictLeft_of_not_right hxNotR) hyFar) hxy
end VertexSeparation

end HadwigerLean
