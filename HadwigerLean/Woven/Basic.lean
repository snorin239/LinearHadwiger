import HadwigerLean.Graph.RootedMinor
import HadwigerLean.Graph.IndexedLinkage

/-!
# Woven graphs

The finite family of prescribed terminal pairs is indexed by `Fin j`, with
`j ≤ b`. This is the up-to-`b` convention used in the common outer induction.
Roots may be terminals, and the two ends of an individual pair may coincide.
-/

namespace HadwigerLean

universe v

/-- All vertices occupied by the branches of a minor model. -/
def MinorModel.vertices {W : Type*} {V : Type v} {H : SimpleGraph W}
    {G : SimpleGraph V} (M : MinorModel H G) : Set V :=
  ⋃ i, M.branch i

/-- The prescribed endpoints of all indexed pairs. -/
def IndexedPairs.allTerminals {ι : Type*} {V : Type v}
    (P : IndexedPairs ι V) : Set V :=
  ⋃ i, P.terminals i

/-- A rooted clique model and prescribed linkage with exactly the allowed
intersection: roots which are also linkage terminals. -/
structure WovenSolution {V : Type v} (G : SimpleGraph V) {a j : ℕ}
    (root : Fin a → V) (P : IndexedPairs (Fin j) V) where
  model : RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G root
  linkage : IndexedLinkage G P
  exact_intersection :
    model.toMinorModel.vertices ∩ linkage.vertices =
      Set.range root ∩ P.allTerminals

/-- `Woven G a b` means every `a` distinct roots and every family of at most
`b` indexed terminal pairs have a compatible rooted model and linkage. -/
def Woven {V : Type v} (G : SimpleGraph V) (a b : ℕ) : Prop :=
  ∀ (root : Fin a → V), Function.Injective root →
    ∀ (j : ℕ) (_ : j ≤ b) (P : IndexedPairs (Fin j) V),
      P.DisjointTerminals → Nonempty (WovenSolution G root P)

namespace Woven

variable {V : Type v} {G : SimpleGraph V} {a b c : ℕ}

/-- The pair budget may be decreased. -/
theorem of_le (h : Woven G a b) (hcb : c ≤ b) : Woven G a c := by
  intro root hroot j hj P hP
  exact h root hroot j (hj.trans hcb) P hP

/-- Wovenness supplies a rooted clique minor for every injective root map.
The empty terminal family is essential here: no padding is needed. -/
theorem rooted_minor (h : Woven G a b) (root : Fin a → V)
    (hroot : Function.Injective root) : HasRootedCliqueMinor G root := by
  let P : IndexedPairs (Fin 0) V :=
    { start := Fin.elim0, finish := Fin.elim0 }
  have hP : P.DisjointTerminals := by
    intro i
    exact i.elim0
  obtain ⟨S⟩ := h root hroot 0 (Nat.zero_le b) P hP
  exact ⟨S.model⟩

/-- Forgetting roots gives an ordinary clique minor. -/
theorem clique_minor (h : Woven G a b)
    (root : Fin a → V) (hroot : Function.Injective root) :
    HasCliqueMinor G a :=
  (h.rooted_minor root hroot).toCliqueMinor

end Woven

namespace IndexedLinkage

variable {ι : Type*} {V : Type v} {G H : SimpleGraph V}
  {P : IndexedPairs ι V}

/-- A linkage remains valid when edges are added to the host graph. -/
def mono (L : IndexedLinkage G P) (h : G ≤ H) : IndexedLinkage H P where
  path := fun i => ⟨(L.path i).1.mapLe h, (L.path i).2.mapLe h⟩
  disjoint := by
    intro i j hij
    simpa only [pathVertexSet, SimpleGraph.Walk.support_mapLe_eq_support] using
      L.disjoint hij

@[simp] theorem vertices_mono (L : IndexedLinkage G P) (h : G ≤ H) :
    (L.mono h).vertices = L.vertices := by
  apply Set.iUnion_congr
  intro i
  ext x
  change x ∈ ((L.path i).1.mapLe h).support ↔ x ∈ (L.path i).1.support
  rw [SimpleGraph.Walk.support_mapLe_eq_support]

end IndexedLinkage

namespace WovenSolution

variable {V : Type v} {G H : SimpleGraph V} {a j : ℕ}
  {root : Fin a → V} {P : IndexedPairs (Fin j) V}

/-- A woven solution remains valid in a graph with more edges. -/
def mono (S : WovenSolution G root P) (h : G ≤ H) :
    WovenSolution H root P where
  model := S.model.mono h
  linkage := S.linkage.mono h
  exact_intersection := by
    change S.model.toMinorModel.vertices ∩ (S.linkage.mono h).vertices =
      Set.range root ∩ P.allTerminals
    simpa only [IndexedLinkage.vertices_mono] using S.exact_intersection

end WovenSolution

namespace Woven

variable {V : Type v} {G H : SimpleGraph V} {a b : ℕ}

/-- Wovenness is monotone when host edges are added. -/
theorem mono_graph (hG : Woven G a b) (hGH : G ≤ H) : Woven H a b := by
  intro root hroot j hj P hP
  obtain ⟨S⟩ := hG root hroot j hj P hP
  exact ⟨S.mono hGH⟩

end Woven

end HadwigerLean

namespace HadwigerLean

namespace Woven

variable {V : Type*} {G : SimpleGraph V} {a : ℕ}

/-- The rooted-clique-minor property is precisely the zero-pair woven base. -/
theorem of_rooted_minor_zero
    (h : ∀ (root : Fin a → V), Function.Injective root →
      HasRootedCliqueMinor G root) : Woven G a 0 := by
  intro root hroot j hj P _
  have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
  subst j
  obtain ⟨M⟩ := h root hroot
  let L : IndexedLinkage G P := {
    path := fun i => i.elim0
    disjoint := by
      intro i
      exact i.elim0
  }
  refine ⟨{ model := M, linkage := L, exact_intersection := ?_ }⟩
  simp [IndexedLinkage.vertices, IndexedPairs.allTerminals]

end Woven

end HadwigerLean

namespace HadwigerLean

namespace Woven

variable {V : Type*}

/-- In a complete graph, two terminals are joined by their edge, or by the
length-zero path when they coincide. -/
private noncomputable def completePath (s t : V) :
    (SimpleGraph.completeGraph V).Path s t := by
  by_cases h : s = t
  · subst t
    exact SimpleGraph.Path.nil
  · exact SimpleGraph.Path.singleton (by simpa using h)

private theorem completePath_vertices (s t : V) :
    pathVertexSet (completePath s t) = ({s, t} : Set V) := by
  by_cases h : s = t
  · subst t
    simp [completePath, pathVertexSet]
  · ext x; simp [completePath, h, pathVertexSet, SimpleGraph.Path.singleton]

/-- Every complete graph is woven for any numbers of roots and disjoint
terminal pairs. This also checks the singleton-pair and root-terminal cases
of the definition. -/
theorem completeGraph (a b : ℕ) :
    Woven (SimpleGraph.completeGraph V) a b := by
  intro root hroot j _ P hP
  let M : RootedMinorModel (SimpleGraph.completeGraph (Fin a))
      (SimpleGraph.completeGraph V) root := {
    branch := fun i => {root i}
    connected := by
      intro i
      simp
    disjoint := by
      intro i k hik
      simpa using hroot.ne hik
    adjacent := by
      intro i k hik
      exact ⟨root i, by simp, root k, by simp,
        by simpa using hroot.ne hik⟩
    root_mem := by
      intro i
      simp
  }
  let L : IndexedLinkage (SimpleGraph.completeGraph V) P := {
    path := fun i => completePath (P.start i) (P.finish i)
    disjoint := by
      intro i k hik
      simpa only [completePath_vertices, IndexedPairs.terminals] using hP hik
  }
  refine ⟨{ model := M, linkage := L, exact_intersection := ?_ }⟩
  have hm : M.toMinorModel.vertices = Set.range root := by
    ext x
    simp [MinorModel.vertices, M]
  have hl : L.vertices = P.allTerminals := by
    ext x
    simp [IndexedLinkage.vertices, IndexedPairs.allTerminals, L,
      completePath_vertices, IndexedPairs.terminals]
  rw [hm, hl]

end Woven

end HadwigerLean

namespace HadwigerLean

namespace WovenSolution

variable {V : Type*} {G : SimpleGraph V} {a j : ℕ}
  {root : Fin a → V} {P : IndexedPairs (Fin j) V}

/-- Every prescribed root belongs to the model's vertex set. -/
theorem root_mem_model (S : WovenSolution G root P) (i : Fin a) :
    root i ∈ S.model.toMinorModel.vertices :=
  Set.mem_iUnion.mpr ⟨i, S.model.root_mem i⟩

/-- Every prescribed terminal belongs to the linkage's vertex set. -/
theorem start_mem_linkage (S : WovenSolution G root P) (i : Fin j) :
    P.start i ∈ S.linkage.vertices :=
  S.linkage.start_mem_vertices i

theorem finish_mem_linkage (S : WovenSolution G root P) (i : Fin j) :
    P.finish i ∈ S.linkage.vertices :=
  S.linkage.finish_mem_vertices i

/-- All overlap is explained by a prescribed root that is also a terminal. -/
theorem overlap_iff (S : WovenSolution G root P) (x : V) :
    x ∈ S.model.toMinorModel.vertices ∧ x ∈ S.linkage.vertices ↔
      x ∈ Set.range root ∧ x ∈ P.allTerminals := by
  change x ∈ S.model.toMinorModel.vertices ∩ S.linkage.vertices ↔
    x ∈ Set.range root ∩ P.allTerminals
  rw [S.exact_intersection]

end WovenSolution

end HadwigerLean
