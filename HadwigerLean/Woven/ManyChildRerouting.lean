import HadwigerLean.Woven.Rerouting
import Mathlib.Tactic

/-!
# Rerouting one linkage through finitely many disjoint woven children

Each child contributes a rooted model. Later reroutings preserve the
earlier model-linkage intersections because all child regions are
disjoint and all roots remain prescribed terminals of the linkage.
-/

namespace HadwigerLean.Woven

universe u

/-- Sequentially reroute one indexed linkage through pairwise disjoint
woven induced child regions, retaining exact intersection with every
rooted child model and control of the new linkage's vertex support. -/
theorem reroute_linkage_through_all_children
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (p a b j : ℕ)
    (J : Fin p → Finset V)
    (hJdis : ∀ i k, i ≠ k →
      Disjoint (J i : Set V) (J k : Set V))
    (hW : ∀ i, Woven (G.induce (J i : Set V)) a b)
    (root : Fin p → Fin a → V)
    (hrootinj : ∀ i, Function.Injective (root i))
    (hrootJ : ∀ i z, root i z ∈ J i)
    {P : IndexedPairs (Fin j) V}
    (L₀ : IndexedLinkage G P)
    (hj : j ≤ b)
    (hrootTerminal : ∀ i, Set.range (root i) ⊆ P.allTerminals) :
    ∃ (L : IndexedLinkage G P)
      (M : ∀ i, RootedMinorModel
        (SimpleGraph.completeGraph (Fin a)) G (root i)),
      (∀ i, (M i).toMinorModel.vertices ⊆ (J i : Set V)) ∧
      (∀ i, (M i).toMinorModel.vertices ∩ L.vertices =
        Set.range (root i)) ∧
      L.vertices ⊆ L₀.vertices ∪ ⋃ i, (J i : Set V) := by
  classical
  have hstep : ∀ S : Finset (Fin p),
      ∃ (L : IndexedLinkage G P)
        (M : ∀ i, i ∈ S →
          RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G (root i)),
        (∀ i (hi : i ∈ S),
          (M i hi).toMinorModel.vertices ⊆ (J i : Set V)) ∧
        (∀ i (hi : i ∈ S),
          (M i hi).toMinorModel.vertices ∩ L.vertices =
            Set.range (root i)) ∧
        L.vertices ⊆ L₀.vertices ∪ ⋃ i ∈ S, (J i : Set V) := by
    intro S
    induction S using Finset.induction with
    | empty =>
        refine ⟨L₀, (fun i hi => False.elim
          ((by simpa using hi))), ?_, ?_, ?_⟩
        · intro i hi
          exact False.elim (by simpa using hi)
        · intro i hi
          exact False.elim (by simpa using hi)
        · intro v hv
          exact Or.inl hv
    | @insert k S hk ih =>
        obtain ⟨L,M,hMsub,hMexact,hLsub⟩ := ih
        obtain ⟨Mk,L',hMkSub,hL'base,hMkExact⟩ :=
          reroute_linkage_through_child_exact
            (J k) (hW k) (root k) (hrootinj k) (hrootJ k)
            L hj (hrootTerminal k)
        let M' : ∀ i, i ∈ insert k S →
            RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G (root i) := by
          intro i hi
          by_cases hik : i = k
          · subst i
            exact Mk
          · exact M i ((Finset.mem_insert.mp hi).resolve_left hik)
        refine ⟨L',M', ?_, ?_, ?_⟩
        · intro i hi
          by_cases hik : i = k
          · subst i
            simpa [M'] using hMkSub
          · have hiS : i ∈ S := (Finset.mem_insert.mp hi).resolve_left hik
            simpa [M', hik] using hMsub i hiS
        · intro i hi
          by_cases hik : i = k
          · subst i
            simpa [M'] using hMkExact
          · have hiS : i ∈ S := (Finset.mem_insert.mp hi).resolve_left hik
            have hMeq : M' i hi = M i hiS := by
              simp [M', hik]
            rw [hMeq]
            change (M i hiS).toMinorModel.vertices ∩ L'.vertices =
              Set.range (root i)
            apply Set.Subset.antisymm
            · intro v hv
              rcases hL'base hv.2 with hvL | hvJ
              · have hOld : v ∈ (M i hiS).toMinorModel.vertices ∩
                    L.vertices := ⟨hv.1,hvL⟩
                rw [hMexact i hiS] at hOld
                exact hOld
              · exact False.elim
                  ((Set.disjoint_left.mp (hJdis i k hik))
                    (hMsub i hiS hv.1) hvJ)
            · rintro v ⟨z,rfl⟩
              have hterm : root i z ∈ P.allTerminals :=
                hrootTerminal i ⟨z,rfl⟩
              obtain ⟨t,ht⟩ := Set.mem_iUnion.mp hterm
              exact ⟨Set.mem_iUnion.mpr
                ⟨z,(M i hiS).root_mem z⟩,
                L'.path_subset_vertices t
                  (L'.terminal_subset_path t ht)⟩
        · intro v hv
          rcases hL'base hv with hvL | hvJ
          · rcases hLsub hvL with hv₀ | hvS
            · exact Or.inl hv₀
            · right
              obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hvS
              obtain ⟨hiS,hiJ⟩ := Set.mem_iUnion.mp hi
              exact Set.mem_iUnion.mpr ⟨i,
                Set.mem_iUnion.mpr
                  ⟨Finset.mem_insert_of_mem hiS,hiJ⟩⟩
          · right
            exact Set.mem_iUnion.mpr ⟨k,
              Set.mem_iUnion.mpr
                ⟨Finset.mem_insert_self k S,hvJ⟩⟩
  obtain ⟨L,M,hMsub,hMexact,hLsub⟩ := hstep Finset.univ
  refine ⟨L, (fun i => M i (Finset.mem_univ i)), ?_, ?_, ?_⟩
  · intro i
    exact hMsub i (Finset.mem_univ i)
  · intro i
    exact hMexact i (Finset.mem_univ i)
  · intro v hv
    rcases hLsub hv with hv₀ | hvJ
    · exact Or.inl hv₀
    · right
      simpa using hvJ

end HadwigerLean.Woven
