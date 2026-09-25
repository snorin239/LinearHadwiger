import HadwigerLean.Graph.RootedDensity.MinimalRootedModel
import Mathlib.Tactic

/-!
# Replacing one branch in a rooted model

A branch can be trimmed whenever its replacement stays connected,
contains the prescribed root, and still witnesses every required
target edge. A model minimizing total branch size forbids a proper
such replacement.
-/

namespace HadwigerLean.RootedDensity

universe u v

def replaceRootedBranch
    {V : Type u} {I : Type v}
    {G : SimpleGraph V} {H : SimpleGraph I} {root : I → V}
    (M : RootedMinorModel H G root) (i : I) (C : Set V)
    [DecidableEq I]
    (hsub : C ⊆ M.branch i)
    (hconn : (G.induce C).Connected)
    (hroot : root i ∈ C)
    (hadj : ∀ j, H.Adj i j →
      ∃ x ∈ C, ∃ y ∈ M.branch j, G.Adj x y) :
    RootedMinorModel H G root where
  toMinorModel := {
    branch := fun j => if j = i then C else M.branch j
    connected := by
      intro j
      by_cases hji : j = i
      · subst j
        rw [if_pos rfl]
        exact hconn
      · rw [if_neg hji]
        exact M.connected j
    disjoint := by
      intro j k hjk
      by_cases hji : j = i
      · subst j
        by_cases hki : k = i
        · exact (hjk hki.symm).elim
        · simpa [hki] using
            (Set.disjoint_left.mpr (fun x hx hy =>
              (Set.disjoint_left.mp (M.disjoint (Ne.symm hki)))
                (hsub hx) hy))
      · by_cases hki : k = i
        · subst k
          simpa [hji] using
            (Set.disjoint_left.mpr (fun x hx hy =>
              (Set.disjoint_left.mp (M.disjoint hji))
                hx (hsub hy)))
        · simpa [hji,hki] using M.disjoint hjk
    adjacent := by
      intro j k hjk
      by_cases hji : j = i
      · subst j
        obtain ⟨x,hx,y,hy,hxy⟩ := hadj k hjk
        have hki : k ≠ i := hjk.ne.symm
        exact ⟨x, by simpa, y, by simpa [hki], hxy⟩
      · by_cases hki : k = i
        · subst k
          obtain ⟨x,hx,y,hy,hxy⟩ := hadj j hjk.symm
          exact ⟨y, by simpa [hji] using hy,
            x, by simpa using hx, hxy.symm⟩
        · obtain ⟨x,hx,y,hy,hxy⟩ := M.adjacent hjk
          exact ⟨x, by simpa [hji] using hx,
            y, by simpa [hki] using hy, hxy⟩
  }
  root_mem := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hroot
    · simpa [hji] using M.root_mem j

theorem rootedModelOrder_replaceBranch_lt
    {V : Type u} {I : Type v}
    [Fintype V] [Fintype I] [DecidableEq I]
    {G : SimpleGraph V} {H : SimpleGraph I} {root : I → V}
    (M : RootedMinorModel H G root) (i : I) (C : Set V)
    (hproper : C ⊂ M.branch i)
    (hconn : (G.induce C).Connected)
    (hroot : root i ∈ C)
    (hadj : ∀ j, H.Adj i j →
      ∃ x ∈ C, ∃ y ∈ M.branch j, G.Adj x y) :
    rootedModelOrder
      (replaceRootedBranch M i C hproper.subset hconn hroot hadj) <
        rootedModelOrder M := by
  let N := replaceRootedBranch M i C hproper.subset hconn hroot hadj
  unfold rootedModelOrder
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hji : j = i
    · subst j
      change (if i = i then C else M.branch i).ncard ≤
        (M.branch i).ncard
      rw [if_pos rfl]
      exact le_of_lt (Set.ncard_lt_ncard hproper)
    · change (if j = i then C else M.branch j).ncard ≤
        (M.branch j).ncard
      rw [if_neg hji]
  · refine ⟨i,Finset.mem_univ i,?_⟩
    change (if i = i then C else M.branch i).ncard <
      (M.branch i).ncard
    rw [if_pos rfl]
    exact Set.ncard_lt_ncard hproper

theorem minimal_rooted_model_no_trim
    {V : Type u} {I : Type v}
    [Fintype V] [Fintype I] [DecidableEq I]
    {G : SimpleGraph V} {H : SimpleGraph I} {root : I → V}
    (M : RootedMinorModel H G root)
    (hmin : ∀ N : RootedMinorModel H G root,
      rootedModelOrder M ≤ rootedModelOrder N)
    (i : I) (C : Set V)
    (hproper : C ⊂ M.branch i)
    (hconn : (G.induce C).Connected)
    (hroot : root i ∈ C)
    (hadj : ∀ j, H.Adj i j →
      ∃ x ∈ C, ∃ y ∈ M.branch j, G.Adj x y) : False := by
  exact (not_lt_of_ge
    (hmin (replaceRootedBranch M i C hproper.subset hconn hroot hadj)))
    (rootedModelOrder_replaceBranch_lt M i C hproper
      hconn hroot hadj)

end HadwigerLean.RootedDensity
