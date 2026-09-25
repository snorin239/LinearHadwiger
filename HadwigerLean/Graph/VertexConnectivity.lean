import HadwigerLean.Graph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Vertex connectivity for finite simple graphs

The convention agrees with the paper: an `r`-connected graph has more than
`r` vertices, and deleting fewer than `r` vertices leaves a connected graph.
The deletion is represented by an induced graph on the complement of a finite
set. This avoids assigning a connectivity value to the empty graph.
-/

namespace HadwigerLean

variable {V : Type*} [Fintype V]

/-- `G` is `k`-vertex-connected, using the paper's strict order convention. -/
def VertexConnected (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ U : Finset V, U.card < k → (G.induce (U : Set V)ᶜ).Connected

namespace VertexConnected

variable {G : SimpleGraph V} {k : ℕ}

/-- A `k`-connected graph has more than `k` vertices. -/
theorem order_gt (h : VertexConnected G k) : k < Fintype.card V := h.1

/-- Deleting fewer than `k` vertices leaves a connected induced graph. -/
theorem connected_delete (h : VertexConnected G k) (U : Finset V)
    (hU : U.card < k) : (G.induce (U : Set V)ᶜ).Connected := h.2 U hU

/-- Two successive finite deletions can be treated as one deletion. -/
theorem connected_delete_union [DecidableEq V] (h : VertexConnected G k) (U W : Finset V)
    (hUW : U.card + W.card < k) :
    (G.induce ((U ∪ W : Finset V) : Set V)ᶜ).Connected := by
  apply h.connected_delete
  exact lt_of_le_of_lt (Finset.card_union_le U W) hUW

/-- Connectivity is monotone in the connectivity parameter. -/
theorem of_le (h : VertexConnected G k) {l : ℕ} (hl : l ≤ k) :
    VertexConnected G l := by
  refine ⟨lt_of_le_of_lt hl h.1, ?_⟩
  intro U hU
  exact h.2 U (lt_of_lt_of_le hU hl)

/-- Adding edges does not reduce vertex connectivity. -/
theorem mono_graph {H : SimpleGraph V} (h : VertexConnected G k)
    (hGH : G ≤ H) : VertexConnected H k := by
  refine ⟨h.order_gt, ?_⟩
  intro U hU
  exact (h.connected_delete U hU).mono (by
    intro x y hxy
    exact hGH hxy)

/-- Deleting vertices lowers the connectivity guarantee by at most their number.
The result is stated with an arbitrary residual lower bound. -/
theorem induce_compl [DecidableEq V] (h : VertexConnected G k)
    (U : Finset V) (m : ℕ) (hm : U.card + m ≤ k) :
    VertexConnected (G.induce (U : Set V)ᶜ) m := by
  classical
  let s : Set V := (U : Set V)ᶜ
  have hcard : Fintype.card s + U.card = Fintype.card V := by
    have hs : Fintype.card s = (Uᶜ : Finset V).card := by
      apply Fintype.card_of_finset' (Uᶜ)
      intro x
      simp [s]
    rw [hs]
    exact Finset.card_compl_add_card U
  refine ⟨?_, ?_⟩
  · change m < Fintype.card s
    have hk := h.order_gt
    omega
  intro W hW
  let F : Finset V := U ∪ W.image (fun z : s => (z : V))
  have hF : F.card < k := by
    have h1 : F.card ≤ U.card + (W.image (fun z : s => (z : V))).card :=
      Finset.card_union_le _ _
    have h2 : (W.image (fun z : s => (z : V))).card ≤ W.card :=
      Finset.card_image_le
    omega
  have hconn : (G.induce (F : Set V)ᶜ).Connected :=
    h.connected_delete F hF
  let f : (G.induce (F : Set V)ᶜ) →g
      ((G.induce s).induce (W : Set s)ᶜ) := {
    toFun := fun z => by
      have hzF : (z : V) ∉ F := z.property
      have hzU : (z : V) ∉ U := by
        intro hz
        exact hzF (Finset.mem_union.mpr (Or.inl hz))
      have hzW : (⟨z, hzU⟩ : s) ∉ W := by
        intro hz
        apply hzF
        apply Finset.mem_union.mpr
        right
        exact Finset.mem_image.mpr ⟨⟨z, hzU⟩, hz, rfl⟩
      exact ⟨⟨z, hzU⟩, hzW⟩
    map_rel' := by
      intro x y hxy
      exact hxy
  }
  have hf : Function.Surjective f := by
    intro z
    have hzF : (z : V) ∉ F := by
      intro hz
      rcases Finset.mem_union.mp hz with hzU | hzW
      · exact z.1.property hzU
      · obtain ⟨w, hw, hval⟩ := Finset.mem_image.mp hzW
        have hwz : w = z.1 := Subtype.ext hval
        exact z.property (hwz ▸ hw)
    refine ⟨⟨z, hzF⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl
  exact hconn.map f hf

/-- Positive vertex connectivity implies ordinary connectedness. -/
theorem connected (h : VertexConnected G k) (hk : 0 < k) : G.Connected := by
  have h' : (G.induce ((∅ : Finset V) : Set V)ᶜ).Connected :=
    h.connected_delete ∅ (by simpa using hk)
  have hset : (((∅ : Finset V) : Set V)ᶜ) = Set.univ := by
    ext x
    simp
  rw [hset] at h'
  have h'' : (G.induce Set.univ).Connected := h'
  exact (SimpleGraph.induceUnivIso G).connected_iff.mp h''

/-- The graph remaining after any admissible deletion is nonempty. -/
theorem nonempty_delete (h : VertexConnected G k) (U : Finset V)
    (hU : U.card < k) : ∃ v : V, v ∉ U := by
  obtain ⟨v⟩ := (h.connected_delete U hU).nonempty
  exact ⟨v.1, v.2⟩

end VertexConnected

/-- A vertex separation has no edge between its two strict sides. -/
structure VertexSeparation (G : SimpleGraph V) where
  left : Set V
  right : Set V
  cover : left ∪ right = Set.univ
  no_cross : ∀ ⦃x y⦄, x ∈ left → x ∉ right → y ∈ right → y ∉ left → ¬ G.Adj x y

namespace VertexSeparation

variable {G : SimpleGraph V}

/-- The common vertices of the two sides. -/
def separator (S : VertexSeparation G) : Set V := S.left ∩ S.right

/-- The finite set of vertices shared by the two sides. -/
noncomputable def separatorFinset (S : VertexSeparation G) : Finset V := by
  classical
  exact S.separator.toFinset

@[simp] theorem mem_separatorFinset (S : VertexSeparation G) (x : V) :
    x ∈ S.separatorFinset ↔ x ∈ S.left ∧ x ∈ S.right := by
  classical
  simp [separatorFinset, separator]

/-- The left side after removing the separator. -/
def strictLeft (S : VertexSeparation G) : Set V := S.left \ S.right

/-- The right side after removing the separator. -/
def strictRight (S : VertexSeparation G) : Set V := S.right \ S.left

omit [Fintype V] in
theorem no_cross' (S : VertexSeparation G) {x y : V}
    (hx : x ∈ S.strictLeft) (hy : y ∈ S.strictRight) : ¬ G.Adj x y :=
  S.no_cross hx.1 hx.2 hy.1 hy.2

omit [Fintype V] in
theorem strictLeft_disjoint_strictRight (S : VertexSeparation G) :
    Disjoint S.strictLeft S.strictRight := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hx.2 hy.1

/-- A separation with two nonempty strict sides has order at least the
vertex connectivity. -/
theorem not_two_strict_sides (S : VertexSeparation G)
    (hconn : VertexConnected G k) (hsmall : S.separatorFinset.card < k) :
    ¬(S.strictLeft.Nonempty ∧ S.strictRight.Nonempty) := by
  rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  let U := S.separatorFinset
  have hxU : x ∉ U := by
    intro h
    exact hx.2 ((S.mem_separatorFinset x).mp h).2
  have hyU : y ∉ U := by
    intro h
    exact hy.2 ((S.mem_separatorFinset y).mp h).1
  let x' : ↥((U : Set V)ᶜ) := ⟨x, hxU⟩
  let y' : ↥((U : Set V)ᶜ) := ⟨y, hyU⟩
  have hG : (G.induce (U : Set V)ᶜ).Connected := hconn.connected_delete U hsmall
  have hstay : ∀ {a b : ↥((U : Set V)ᶜ)},
      (G.induce (U : Set V)ᶜ).Walk a b →
      (a : V) ∈ S.strictLeft → (b : V) ∈ S.strictLeft := by
    intro a b p
    induction p with
    | nil => intro ha; exact ha
    | @cons a b c hab p ih =>
      intro ha
      have hbcover : (b : V) ∈ S.left ∪ S.right := by
        rw [S.cover]
        trivial
      have hb : (b : V) ∈ S.strictLeft := by
        rcases hbcover with hbL | hbR
        · exact ⟨hbL, fun hbR =>
            b.property ((S.mem_separatorFinset b).mpr ⟨hbL, hbR⟩)⟩
        · have hbNotL : (b : V) ∉ S.left := by
            intro hbL
            exact b.property ((S.mem_separatorFinset b).mpr ⟨hbL, hbR⟩)
          exact False.elim ((S.no_cross ha.1 ha.2 hbR hbNotL) hab)
      exact ih hb
  exact hy.2 (hstay (hG.preconnected x' y').some hx).1

/-- Reversing the sides gives another separation. -/
def symm (S : VertexSeparation G) : VertexSeparation G where
  left := S.right
  right := S.left
  cover := by simpa only [Set.union_comm] using S.cover
  no_cross := by
    intro x y hx hr hy hl hxy
    exact S.no_cross hy hl hx hr hxy.symm

end VertexSeparation

end HadwigerLean
